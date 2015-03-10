/*
 * Copyright (C) 2015 Huawei Technologies Duesseldorf GmbH
 *
 * Written by Eduard Shishkin <eduard.shishkin@huawei.com>
 *
 * This work is open source software, licensed under the terms of the
 * BSD license as described in the LICENSE file in the top-level directory.
 *
 */

/*
 * This tool has been written for the OSv operating system
 * in order to be able to manipulate (add) files to an OSv image.
 */

#include <sys/debug.h>
#include <sys/mount.h>
#include <sys/types.h>
#include <sys/cred.h>
#include <sys/cmn_err.h>
#include <sys/zfs_znode.h>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
#include <pthread.h>
#include <syslog.h>

#include "libsolkerncompat.h"
#include "zfs_ioctl.h"

#include "cmd_listener.h"
#include "fuse_listener.h"

#include "zfs_operations.h"
#include "util.h"

#define MAX_NESTED_LINKS    (8)
#define ZFS_USERSPACE_DEBUG (1)
/*
 * ZFS user-space operations.
 *
 * Everything is going in user-space.
 * That is, we don't call FUSE and ZFS kernel
 * modules for any service.
 */

extern vfsops_t *zfs_vfsops;
extern int zfs_vfsinit(int fstype, char *name);

static int zfs_path_walk(vfs_t *vsf, char *path,
			 int start_lookup_dir, int *result,
			 char **short_name);

typedef enum zfs_userspace_action {
	ZFS_USERSPACE_UNKNOWN_ACT,
	ZFS_USERSPACE_READ_ACT,
	ZFS_USERSPACE_WRITE_ACT,
	ZFS_USERSPACE_MKDIR_ACT,
	ZFS_USERSPACE_SYMLINK_ACT,
} zfs_userspace_action_t;

static char *zfs_spec = NULL;
static char *from_file = NULL;
static char *new_file = NULL;
static char *symlink_target = NULL;
static char *mount_point = NULL;
static zfs_userspace_action_t action = ZFS_USERSPACE_UNKNOWN_ACT;

static void userspace_get_cred(cred_t *cred)
{
	cred->cr_uid = getuid();
	cred->cr_gid = getgid();
}

vfs_t *zfs_userspace_volume_init(char *spec,
				 char *dir, int mflag, char *opt)
{
	int ret;

	VERIFY(mflag == 0);
	VERIFY(opt[0] == '\0');

	vfs_t *vfs = kmem_zalloc(sizeof(vfs_t), KM_SLEEP);
	if(vfs == NULL)
		return NULL;

	VFS_INIT(vfs, zfs_vfsops, 0);
	VFS_HOLD(vfs);

	struct mounta uap = {spec, dir, mflag | MS_SYSSPACE, NULL, opt, strlen(opt)};

	ret = VFS_MOUNT(vfs, rootdir, &uap, kcred);
	if (ret != 0) {
		printf("failed to init ZFS volume %s (%d)\n", spec, ret);
		kmem_free(vfs, sizeof(vfs_t));
		return NULL;
	}
	return vfs;
}

static int zfs_userspace_volume_fini(vfs_t *vfs, boolean_t force)
{
	int ret;

	VFS_SYNC(vfs, 0, kcred);

	ret = VFS_UNMOUNT(vfs, force ? MS_FORCE : 0, kcred);
	VFS_RELE(vfs);
	if(ret != 0) {
		printf("failed to fini ZFS volume %s (%d)\n", zfs_spec, ret);
		return ret;
	}
	ASSERT(force || vfs->vfs_count == 1);
	return 0;
}

int zfs_userspace_lookup(vfs_t *vfs, fuse_ino_t parent,
				const char *name, int *ino)
{
	if(strlen(name) >= MAXNAMELEN)
		return ENAMETOOLONG;

	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	znode_t *znode;

	int error = zfs_zget(zfsvfs, parent, &znode, B_TRUE);
	if(error) {
		ZFS_EXIT(zfsvfs);
		/* If the inode we are trying to get was recently deleted
		   dnode_hold_impl will return EEXIST instead of ENOENT */
		return error == EEXIST ? ENOENT : error;
	}

	ASSERT(znode != NULL);
	vnode_t *dvp = ZTOV(znode);
	ASSERT(dvp != NULL);

	vnode_t *vp = NULL;

	cred_t cred;
	userspace_get_cred(&cred);

	error = VOP_LOOKUP(dvp, (char *) name, &vp, NULL, 0, NULL, &cred, NULL, NULL, NULL);
	if(error)
		goto out;
	if(vp == NULL)
		goto out;
	*ino = VTOZ(vp)->z_id;

 out:
	if(vp != NULL)
		VN_RELE(vp);
	VN_RELE(dvp);
	ZFS_EXIT(zfsvfs);

	return error;
}

static int zfs_userspace_opencreate(vfs_t *vfs, int fflags, int ino,
				    mode_t createmode, const char *name,
				    file_info_t *info)
{
	if(name && strlen(name) >= MAXNAMELEN)
		return ENAMETOOLONG;

	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	cred_t cred;
	userspace_get_cred(&cred);

	/* Map flags */
	int mode, flags;

	if(fflags & O_WRONLY) {
		mode = VWRITE;
		flags = FWRITE;
	} else if(fflags & O_RDWR) {
		mode = VREAD | VWRITE;
		flags = FREAD | FWRITE;
	} else {
		mode = VREAD;
		flags = FREAD;
	}

	if(fflags & O_CREAT)
		flags |= FCREAT;
	if(fflags & O_SYNC)
		flags |= FSYNC;
	if(fflags & O_DSYNC)
		flags |= FDSYNC;
	if(fflags & O_RSYNC)
		flags |= FRSYNC;
	if(fflags & O_APPEND)
		flags |= FAPPEND;
	if(fflags & O_LARGEFILE)
		flags |= FOFFMAX;
	if(fflags & O_NOFOLLOW)
		flags |= FNOFOLLOW;
	if(fflags & O_TRUNC)
		flags |= FTRUNC;
	if(fflags & O_EXCL)
		flags |= FEXCL;

	znode_t *znode;
	int error = zfs_zget(zfsvfs, ino, &znode, B_FALSE);
	if(error) {
		ZFS_EXIT(zfsvfs);
		/* If the inode we are trying to get was recently deleted
		   dnode_hold_impl will return EEXIST instead of ENOENT */
		return error == EEXIST ? ENOENT : error;
	}

	ASSERT(znode != NULL);
	vnode_t *vp = ZTOV(znode);
	ASSERT(vp != NULL);

	if (flags & FCREAT) {
		enum vcexcl excl;

		/*
		 * Wish to create a file.
		 */
		vattr_t vattr;
		vattr.va_type = VREG;
		vattr.va_mode = createmode;
		vattr.va_mask = AT_TYPE|AT_MODE;
		if (flags & FTRUNC) {
			vattr.va_size = 0;
			vattr.va_mask |= AT_SIZE;
		}
		if (flags & FEXCL)
			excl = EXCL;
		else
			excl = NONEXCL;

		vnode_t *new_vp;
		/*
		 * FIXME: check filesystem boundaries
		 */
		error = VOP_CREATE(vp, (char *) name, &vattr,
				   excl, mode, &new_vp, &cred, 0, NULL, NULL);
		if(error)
			goto out;

		VN_RELE(vp);
		vp = new_vp;
	} else {
		/*
		 * Get the attributes to check whether file is large.
		 * We do this only if the O_LARGEFILE flag is not set and
		 * only for regular files.
		 */
		if (!(flags & FOFFMAX) && (vp->v_type == VREG)) {
			vattr_t vattr;
			vattr.va_mask = AT_SIZE;
			if ((error = VOP_GETATTR(vp, &vattr, 0, &cred, NULL)))
				goto out;

			if (vattr.va_size > (u_offset_t) MAXOFF32_T) {
				/*
				 * Large File API - regular open fails
				 * if FOFFMAX flag is set in file mode
				 */
				error = EOVERFLOW;
				goto out;
			}
		}

		/*
		 * Check permissions.
		 */
		if (error = VOP_ACCESS(vp, mode, 0, &cred, NULL))
			goto out;
	}

	if ((flags & FNOFOLLOW) && vp->v_type == VLNK) {
		error = ELOOP;
		goto out;
	}

	vnode_t *old_vp = vp;

	error = VOP_OPEN(&vp, flags, &cred, NULL);
	ASSERT(old_vp == vp);

	info->vp = vp;
	info->flags = flags;

 out:
	if(error) {
		ASSERT(vp->v_count > 0);
		VN_RELE(vp);
	}
	ZFS_EXIT(zfsvfs);
	return error;
}

static int zfs_userspace_open(vfs_t *vfs, int fflags, int ino,
			      const char *name, file_info_t *info)
{
	return zfs_userspace_opencreate(vfs, fflags, ino, 0, name, info);
}

static int zfs_userspace_create(vfs_t *vfs, int fflags, int parent_ino,
				mode_t createmode, const char *name,
				file_info_t *info)
{
	return zfs_userspace_opencreate(vfs, fflags, parent_ino,
					createmode, name, info);
}

static int zfs_userspace_release(vfs_t *vfs, int ino, file_info_t *info)
{
	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	ASSERT(info->vp != NULL);
	ASSERT(VTOZ(info->vp) != NULL);
	ASSERT(VTOZ(info->vp)->z_id == ino);

	cred_t cred;
	userspace_get_cred(&cred);

	int error = VOP_CLOSE(info->vp, info->flags, 1, (offset_t) 0, &cred, NULL);
	VERIFY(error == 0);

	VN_RELE(info->vp);

	ZFS_EXIT(zfsvfs);
	if (error)
		printf("zfs userspace release failed");
	return error;
}

/*
 * @parent_ino - inode of directory where to create
 * @name - short name of directory to create
 */
static int zfs_userspace_mkdir(vfs_t *vfs, int parent_ino, const char *name,
			       mode_t mode, file_info_t *info)
{
	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);
	
	znode_t *znode;

	int error = zfs_zget(zfsvfs, parent_ino, &znode, B_FALSE);
	if(error) {
		ZFS_EXIT(zfsvfs);
		/* If the inode we are trying to get was recently deleted
		   dnode_hold_impl will return EEXIST instead of ENOENT */
		return error == EEXIST ? ENOENT : error;
	}

	ASSERT(znode != NULL);
	vnode_t *dvp = ZTOV(znode);
	ASSERT(dvp != NULL);

	vnode_t *vp = NULL;

	vattr_t vattr = { 0 };
	vattr.va_type = VDIR;
	vattr.va_mode = mode & PERMMASK;
	vattr.va_mask = AT_TYPE | AT_MODE;

	cred_t cred;
	userspace_get_cred(&cred);

	error = VOP_MKDIR(dvp, (char *) name, &vattr, &vp, &cred, NULL, 0, NULL);
	if(error)
		goto out;

	ASSERT(vp != NULL);
 out:
	if(vp != NULL)
		VN_RELE(vp);
	VN_RELE(dvp);

	ZFS_EXIT(zfsvfs);
	return error;
}

/*
 * @name - short name of the symlink to be created
 * @link - target of the symlink
 * @parent - inode of directory where to create symlink
 */
static int zfs_userspace_symlink(vfs_t *vfs, int parent,
				 const char *link, const char *name,
				 file_info_t *info)
{
	if(strlen(name) >= MAXNAMELEN)
		return ENAMETOOLONG;

	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	znode_t *znode;

	int error = zfs_zget(zfsvfs, parent, &znode, B_FALSE);
	if(error) {
		ZFS_EXIT(zfsvfs);
		/* If the inode we are trying to get was recently deleted
		   dnode_hold_impl will return EEXIST instead of ENOENT */
		return error == EEXIST ? ENOENT : error;
	}

	ASSERT(znode != NULL);
	vnode_t *dvp = ZTOV(znode);
	ASSERT(dvp != NULL);

	cred_t cred;
	userspace_get_cred(&cred);

	vattr_t vattr;
	vattr.va_type = VLNK;
	vattr.va_mode = 0777;
	vattr.va_mask = AT_TYPE | AT_MODE;

	error = VOP_SYMLINK(dvp, (char *) name, &vattr, (char *) link, &cred, NULL, 0);

	vnode_t *vp = NULL;

	if(error)
		goto out;

	error = VOP_LOOKUP(dvp, (char *) name, &vp, NULL, 0, NULL, &cred, NULL, NULL, NULL);
	if(error)
		goto out;
	ASSERT(vp != NULL);
 out:
	if(vp != NULL)
		VN_RELE(vp);
	VN_RELE(dvp);

	ZFS_EXIT(zfsvfs);
	return error;
}

static int zfs_userspace_readlink(vfs_t *vfs, int link_ino, char *buffer)
{
	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);
	znode_t *znode;

	int error = zfs_zget(zfsvfs, link_ino, &znode, B_FALSE);
	if(error) {
		ZFS_EXIT(zfsvfs);
		return error;
	}
	ASSERT(znode != NULL);
	vnode_t *vp = ZTOV(znode);
	ASSERT(vp != NULL);

	iovec_t iovec;
	uio_t uio;
	uio.uio_iov = &iovec;
	uio.uio_iovcnt = 1;
	uio.uio_segflg = UIO_SYSSPACE;
	uio.uio_fmode = 0;
	uio.uio_llimit = RLIM64_INFINITY;
	iovec.iov_base = buffer;
	iovec.iov_len = sizeof(buffer) - 1;
	uio.uio_resid = iovec.iov_len;
	uio.uio_loffset = 0;

	cred_t cred;
	userspace_get_cred(&cred);

	error = VOP_READLINK(vp, &uio, &cred, NULL);

	VN_RELE(vp);
	ZFS_EXIT(zfsvfs);

	return error;
}

/*
 * Try to read @size bytes at offset @off to buffer @buf
 * Return < 0 in the case of error.
 * Otherwise return number of bytes that was actually read
 */
static ssize_t zfs_userspace_read(vfs_t *vfs, file_info_t *info,
				  size_t size, off_t off, char *buf)
{
	vnode_t *vp = info->vp;
	ASSERT(vp != NULL);
	ASSERT(VTOZ(vp) != NULL);

	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	iovec_t iovec;
	uio_t uio;
	uio.uio_iov = &iovec;
	uio.uio_iovcnt = 1;
	uio.uio_segflg = UIO_SYSSPACE;
	uio.uio_fmode = 0;
	uio.uio_llimit = RLIM64_INFINITY;

	iovec.iov_base = buf;
	iovec.iov_len = size;
	uio.uio_resid = iovec.iov_len;
	uio.uio_loffset = off;

	cred_t cred;
	userspace_get_cred(&cred);

	int error = VOP_READ(vp, &uio, info->flags, &cred, NULL);

	ZFS_EXIT(zfsvfs);
	if (error)
		return -1;
	return uio.uio_loffset - off;
}

/*
 * Try to write @size bytes from buffer @buf at offset @off
 * in the file.
 * Return < 0 in the case of error.
 * Otherwise return number of bytes that was actually written
 */
ssize_t zfs_userspace_write(vfs_t *vfs, file_info_t *info,
			    const char *buf, size_t size, off_t off)
{
	vnode_t *vp = info->vp;
	ASSERT(vp != NULL);
	ASSERT(VTOZ(vp) != NULL);

	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	iovec_t iovec;
	uio_t uio;
	uio.uio_iov = &iovec;
	uio.uio_iovcnt = 1;
	uio.uio_segflg = UIO_SYSSPACE;
	uio.uio_fmode = 0;
	uio.uio_llimit = RLIM64_INFINITY;

	iovec.iov_base = (void *) buf;
	iovec.iov_len = size;
	uio.uio_resid = iovec.iov_len;
	uio.uio_loffset = off;

	cred_t cred;
	userspace_get_cred(&cred);

	int error = VOP_WRITE(vp, &uio, info->flags, &cred, NULL);

	ZFS_EXIT(zfsvfs);

	if(!error) {
		/*
		 * When not using direct_io, we must always write 'size' bytes
		 */
		VERIFY(uio.uio_resid == 0);
		return size - uio.uio_resid;
	}
	return -1;
}

static int zfs_userspace_fsync(vfs_t *vfs, file_info_t *info, int datasync)
{
	zfsvfs_t *zfsvfs = vfs->vfs_data;

	ZFS_ENTER(zfsvfs);

	ASSERT(info->vp != NULL);
	ASSERT(VTOZ(info->vp) != NULL);

	vnode_t *vp = info->vp;

	cred_t cred;
	userspace_get_cred(&cred);

	int error = VOP_FSYNC(vp, datasync ? FDSYNC : FSYNC, &cred, NULL);

	ZFS_EXIT(zfsvfs);

	return error;
}

static void zfs_userspace_init(void)
{
	libsolkerncompat_init();
	zfs_vfsinit(zfstype, NULL);
	VERIFY(zfs_ioctl_init() == 0);
}

static void zfs_userspace_fini(void)
{
	int ret = zfs_ioctl_fini();
	if(ret != 0)
		printf("Error %i in zfs_ioctl_fini().\n", ret);
	libsolkerncompat_exit();
}

#define ROOT_INODE (3)
#define MKDIR_MODE (493)
#define CREATE_MODE (33188)
#define CREATE_FFLAGS (33345)

static int zfs_userspace_create_dir(vfs_t *vfs, char *dirname)
{
	int ret;
	file_info_t info;
	char *short_dirname = NULL;
	int parent;

	ret = zfs_path_walk(vfs, dirname,
			    ROOT_INODE, &parent, &short_dirname);
	if (!ret)
		return EEXIST;
	if (ret != ENOENT)
		return ret;
	if (!short_dirname)
		return ret;

	ret = zfs_userspace_mkdir(vfs, parent,
				  short_dirname, MKDIR_MODE, &info);
	if (ret) 
		printf("failed to create directory %s\n", dirname);
	return ret;
}

static int zfs_userspace_create_symlink(vfs_t *vfs,
					char *name, char *target_name)
{
	int ret;
	file_info_t info;
	char *short_name = NULL;
	int parent = ROOT_INODE;

	ret = zfs_path_walk(vfs, name,
			    ROOT_INODE, &parent, &short_name);
	if (!ret)
		return EEXIST;
	if (ret != ENOENT)
		return ret;
	if (!short_name)
		return ret;
	
	ret = zfs_userspace_symlink(vfs, parent,
				    target_name, short_name, &info);
	if (ret)
		printf("failed to create symlink %s for %s\n",
		       name, target_name);
	return ret;
}

static void read_to_stdout(char *src, int len)
{
	int i;
	for (i = 0; i < len; i++)
		printf("%c", src[i]);
}

/*
 * @filename - name of the file (absolute, or relative) to be read
 */
static int zfs_userspace_file_read(vfs_t *vfs, char *filename)
{
	int ret;
	int nread;
	off_t offset = 0;
	char buf[4096];

	int inode;
	file_info_t info;
	char *parent_dirname;

	/*
	 * resolve file's name to inode
	 */
	ret = zfs_path_walk(vfs, filename, ROOT_INODE, &inode, &parent_dirname);
	if (ret)
		return ret;

	ret = zfs_userspace_open(vfs, O_RDWR, inode, NULL, &info);
	if (ret) {
		printf("failed to open file %s\n", filename);
		goto error;
	}

	while (1) {
		nread = zfs_userspace_read(vfs, &info,
					   sizeof(buf), offset, buf);
		if (nread <= 0)
			break;
		read_to_stdout(buf, nread);
		offset += nread;
	}
	if (nread < 0) {
		printf("failed to read file %s\n", filename);
		goto error;
	}

	ret = zfs_userspace_release(vfs, VTOZ(info.vp)->z_id, &info);
	if (ret) {
		printf("failed to release file %s\n", filename);
		goto error;
	}
	return 0;
 error:
	return 1;
}

/*
 * create a file @dst_file_name on zfs volume
 * and copy the content of @src_file_name
 */
static int zfs_userspace_file_copy(vfs_t *vfs,
				   char *src_file_name,
				   char *dst_file_name)
{
	int ret;
	int fd;
	int nread;
	off_t offset = 0;
	char buf[4096];

	file_info_t info;

	int parent = ROOT_INODE;
	char *short_dst_file_name;

	fd = open(src_file_name, O_RDONLY);
	if (fd < 0) {
		printf("failed to open input file %s\n", src_file_name);
		return 1;
	}
	/*
	 * resolve destination path
	 */
	ret = zfs_path_walk(vfs, dst_file_name,
			    ROOT_INODE, &parent, &short_dst_file_name);
	if (!ret)
		return EEXIST;
	if (ret != ENOENT)
		return ret;
	if (!short_dst_file_name)
		return ret;
	/*
	 * create a file on ZFS volume
	 */
	ret = zfs_userspace_create(vfs,
				   CREATE_FFLAGS, parent,
				   CREATE_MODE, short_dst_file_name, &info);
	if (ret) {
		printf("failed to create output file %s\n", dst_file_name);
		goto error;
	}

	while (1) {
		ssize_t nwritten;

		nread = read(fd, buf, sizeof(buf));
		if (nread <= 0)
			break;

		nwritten = zfs_userspace_write(vfs, &info,
					       buf, nread, offset);
		if (nwritten < 0) {
			printf("failed to write file %s\n", dst_file_name);
			goto error;
		}
		VERIFY(nwritten == nread);

		offset += nwritten;
	}
	if (nread < 0) {
		printf("failed to read input file %s\n", src_file_name);
		goto error;
	}

	ret = zfs_userspace_fsync(vfs, &info, 0);
	if (ret) {
		printf("failed to sync file %s\n", dst_file_name);
		goto error;
	}

	ret = zfs_userspace_release(vfs, VTOZ(info.vp)->z_id, &info);
	if (ret) {
		printf("failed to release file %s\n", dst_file_name);
		goto error;
	}
	ret = close(fd);
	if (ret)
		printf("failed to close file %s\n", src_file_name);
	return 0;
 error:
	ret = close(fd);
	if (ret)
		printf("failed to close file %s\n", src_file_name);
	return 1;
}

/*
 * return length of the current path component
 */
static int short_name_len(char *name)
{
	int len = 0;
	int c = (unsigned char)*name;
	do {
		len++;
		c = (unsigned char)name[len];
	} while (c && c != '/');
	return len;
}

static enum vtype type_of_file(int inode, vfs_t *vfs)
{
	int error;
	znode_t *znode;	
	zfsvfs_t *zfsvfs = vfs->vfs_data;
	vnode_t *vp;

	error = zfs_zget(zfsvfs, inode, &znode, B_TRUE);
	if (error)
		return VBAD;
	ASSERT(znode != NULL);
	vp = ZTOV(znode);
	ASSERT(vp != NULL);

	return vp->v_type;
}

/*
 * Resolve symlink with inode number @symlink_ino
 * and put result to @result.
 */
static int resolve_symlink(vfs_t *vfs,
			   int start_lookup_dir, int symlink_ino, int *result)
{
	int ret;
	int res = 0;
	char *last;
	char buf[PATH_MAX + 1];

	memset(buf, 0, sizeof(buf));
	/*
	 * evaluate symlink 
	 */
	ret = zfs_userspace_readlink(vfs, symlink_ino, buf);
	if (ret) {
		printf("failed to read link (%d)\n", ret);
		return ret;
	}
	if (buf[0] == '/')
		start_lookup_dir = ROOT_INODE;

	ret = zfs_path_walk(vfs, buf, start_lookup_dir, &res, &last);
	if (ret)
		/*
		 * All components of symlink has to be found.
		 */
		return ret;
	*result = res;
	return 0;
}

/*
 * Procedure of name resolution (see path_resolution (7))
 * This is recursive because of need to resolve symlinks.
 * Convert path name to inode number.
 *
 * Inode number of the last found component is stored in @result.
 * Name of the last not found component is stored in @last_not_found
 *
 */
static int zfs_path_walk(vfs_t *vfs, char *path,
			 int start_lookup_dir, int *result,
			 char **last_not_found)
{
	int ret;
	char *name; /* short name of the current component */
	int name_len;
	int nr_followed = 0;
	int lookup_dir = start_lookup_dir;

	*result = start_lookup_dir;
	name = path;
	/*
	 * skip slashes 
	 */
	while (*name == '/')
		name++;
	if (!*name)
		return 0;
	/*
	 * we have a real path component
	 */
	while (1) {
		char c;
		static enum vtype type;
		int lookup_result;

		name_len = short_name_len(name);
		ASSERT(name_len != 0);
		c = name[name_len];
		ASSERT(c == '/' || c == 0);

		name[name_len] = 0;

		ret = zfs_userspace_lookup(vfs, lookup_dir,
					   name, &lookup_result);
		name[name_len] = c;

		if (ret == ENOENT && c == 0) {
			/*
			 * Last component not found
			 */
			*last_not_found = name;
			*result = lookup_dir;
		}
		if (ret) {
			if (ret != ENOENT)
				printf("lookup failed (%d)\n", ret);
			return ret;
		}
		type = type_of_file(lookup_result, vfs);

		if (c != 0 && type != VDIR && type != VLNK)
			return ENOTDIR;
	handle_by_type:

		switch (type) {
		case VLNK:
			if (nr_followed >= MAX_NESTED_LINKS)
				return ELOOP;
			/*
			 * this will update lookup_result with
			 * the result of symlink resolution
			 */
			ret = resolve_symlink(vfs, lookup_dir,
					      lookup_result, &lookup_result);
			if (ret)
				return ret;
			nr_followed ++;
			type = type_of_file(lookup_result, vfs);
			goto handle_by_type;
		case VDIR:
			if (c == 0) {
				/*
				 * final component
				 */
				*result = lookup_result;
				return 0;
			}
			name += name_len;
			/*
			 * skip slashes
			 */
			do {
				name++;
			} while (*name == '/');
			if (!*name) {
				/*
				 * it was a final component
				 * with trailing slashes
				 */
				*result = lookup_result;
				return 0;
			}
			/*
			 * we have a real path component
			 * to be lookup-ed
			 */
			lookup_dir = lookup_result;
			continue;
		case VREG:
			/*
			 * we know there is no trailing slashes
			 */
			ASSERT(c == 0);
			*result = lookup_result;
			return 0;
		default:
			printf("bad file type: %d\n", type);
			return -1;
		}
	}
}

extern char *optarg;
extern int optind, opterr, optopt;

static struct option longopts[] = {
	{ "mount-point",
	  1, /* has-arg */
	  NULL, /* flag */
	  'm'
	},
	{ "from-file",
	  1,
	  NULL,
	  'f'
	},
	{ "new-file",
	  1,
	  NULL,
	  'n'
	},
	{ "symlink-target",
	  1,
	  NULL,
	  't'
	},
	{ "dir",
	  0,
	  NULL,
	  'd'
	},
	{ "read",
	  0,
	  NULL,
	  'r'
	},
	{ "write",
	  0,
	  NULL,
	  'w'
	},
	{ "symlink",
	  0,
	  NULL,
	  's'
	},
	{ "help",
	  0,
	  NULL,
	  'h'
	},
	{ 0, 0, 0, 0 }
};

static void print_usage(int argc, char *argv[])
{
	const char *progname = argv[0];

	fprintf(stderr,
		"Usage: %s [OPTION] volname\n"
		"\n"
		"Options:\n"
		"  -m PATHNAME, --mount-point PATHNAME\n"
		"			Specifies ZFS mount point.\n"
		"  -f PATHNAME, --from-file PATHNAME\n"
		"			Specifies input file for copy and read operations.\n"
		"  -n PATHNAME, --new-file PATHNAME\n"
		"			Specifies new file name for copy, symlink and mkdir opeatations.\n"
		"  -t PATHNAME, --symlink-target PATHNAME\n"
		"			Specifies target file for new symlink creation.\n"
		"  -d, --dir\n"
		"			Create directory on ZFS volume.\n"
		"  -r, --read\n"
		"			Read input file to the standard output.\n"
		"  -w, --write\n"
		"			Copy input file to the ZFS volume.\n"
		"  -s, --symlink\n"
		"			Create a symlink on ZFS volume.\n"
		"  -h, --help\n"
		"			Show this usage summary.\n"
		, progname);
}

int parse_args(int argc, char *argv[])
{
	int retval;
	const char *progname = argv[0];

	while ((retval = getopt_long(argc, argv, "-hrwsdm:f:n:t:", longopts, NULL)) != -1) {
		switch(retval) {
		case 1: /* non-option argument passed */
			zfs_spec = optarg;
			goto check;
		case 'h':
		case '?':
			print_usage(argc, argv);
			return 1;
		case 'm':
			if (mount_point != NULL) {
				print_usage(argc, argv);
				return 1;
			}
			mount_point = optarg;
			break;
		case 'f':
			if (from_file != NULL) {
				print_usage(argc, argv);
				return 1;
			}
			from_file = optarg;
			break;
		case 'n':
			if (new_file != NULL) {
				print_usage(argc, argv);
				return 1;
			}
			new_file = optarg;
			break;
		case 't':
			if (symlink_target != NULL) {
				print_usage(argc, argv);
				return 1;
			}
			symlink_target = optarg;
			break;
		case 'd':
			if (action != ZFS_USERSPACE_UNKNOWN_ACT) {
				print_usage(argc, argv);
				return 1;
			}
			action = ZFS_USERSPACE_MKDIR_ACT;
			break;
		case 'r':
			if (action != ZFS_USERSPACE_UNKNOWN_ACT) {
				print_usage(argc, argv);
				return 1;
			}
			action = ZFS_USERSPACE_READ_ACT;
			break;
		case 'w':
			if (action != ZFS_USERSPACE_UNKNOWN_ACT) {
				print_usage(argc, argv);
				return 1;
			}
			action = ZFS_USERSPACE_WRITE_ACT;
			break;
		case 's':
			if (action != ZFS_USERSPACE_UNKNOWN_ACT) {
				print_usage(argc, argv);
				return 1;
			}
			action = ZFS_USERSPACE_SYMLINK_ACT;
			break;
		default:
			/*
			 * This should never happen
			 */
			fprintf(stderr, "%s: option not recognized\n",
				progname);
			print_usage(argc, argv);
			return 1;
		}
	}
	if (optind >= argc) {
		fprintf(stderr,
			"%s requires an argument (ZFS volume)\n", progname);
		return 1;
	}
	zfs_spec = argv[optind];
 check:
	if (mount_point == NULL)
		mount_point = "";

	switch (action) {
	case ZFS_USERSPACE_MKDIR_ACT:
		if (new_file == NULL) {
			fprintf(stderr,
				"specify directory name to create \n");
			return 1;
		}
		break;
	case ZFS_USERSPACE_READ_ACT:
		if (from_file == NULL) {
			fprintf(stderr,
				"specify input file for read action\n");
			return 1;
		}
		break;
	case ZFS_USERSPACE_WRITE_ACT:
		if (from_file == NULL) {
			fprintf(stderr,
				"specify source file for copy action\n");
			return 1;
		}
		if (new_file == NULL) {
			fprintf(stderr,
				"specify new file for copy action\n");
			return 1;
		}
		break;		
	case ZFS_USERSPACE_SYMLINK_ACT:
		if (new_file == NULL) {
			fprintf(stderr,
				"specify name of new symlink\n");
			return 1;
		}
		if (symlink_target == NULL) {
			fprintf(stderr,
				"specify target file for new symlink\n");
			return 1;
		}
		break;
	default:
		break;
	}
	return 0;
}

int main(int argc, char *argv[])
{
	int ret = 0;
	vfs_t *vfs;

	if (parse_args(argc, argv))
		exit(EXIT_FAILURE);

	zfs_userspace_init();

	vfs = zfs_userspace_volume_init(zfs_spec, mount_point,
					0, "" /* mount options */);
	if (vfs == NULL)
		goto error;

	switch (action) {
	case ZFS_USERSPACE_READ_ACT:
		ret = zfs_userspace_file_read(vfs, from_file);
		break;
	case ZFS_USERSPACE_WRITE_ACT:
		ret = zfs_userspace_file_copy(vfs, from_file, new_file);
		break;
	case ZFS_USERSPACE_MKDIR_ACT:
		ret = zfs_userspace_create_dir(vfs, new_file);
		break;
	case ZFS_USERSPACE_SYMLINK_ACT:
		ret = zfs_userspace_create_symlink(vfs,
						   new_file,
						   symlink_target);
		break;
	default:
		break;
	}
	if (zfs_userspace_volume_fini(vfs, 1 /* force */)) {
		printf("failed to fini zfs volume\n");
		goto error;
	}
	if (ret)
		goto error;

	zfs_userspace_fini();
	exit(EXIT_SUCCESS);
 error:
	zfs_userspace_fini();
	exit(EXIT_FAILURE);
}

/*
  Local variables:
  c-indentation-style: "K&R"
  mode-name: "LC"
  c-basic-offset: 8
  tab-width: 8
  fill-column: 80
  scroll-step: 1
  End:
*/
