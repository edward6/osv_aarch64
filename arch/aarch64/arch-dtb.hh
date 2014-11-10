/*
 * Copyright (C) 2014 Huawei Technologies Duesseldorf GmbH
 *
 * This work is open source software, licensed under the terms of the
 * BSD license as described in the LICENSE file in the top-level directory.
 */

#ifndef ARCH_DTB_HH
#define ARCH_DTB_HH

/* dtb is set early during boot */
extern void *dtb;

/* this information is also stored and exported in this module,
 * since it has to be collected at dtb setup time.
 * Only the boot loader references this, should never be used
 * elsewhere, as the pointed memory is overwritten with dtb.
 */
extern char *cmdline;

/* void __attribute__((constructor(init_prio::dtb))) dtb_setup()
 *
 * this is a constructor that is run at premain time with priority dtb,
 * in order to check the dtb contents for correctness, and on failure
 * avoid any fdt use by setting the global dtb pointer to NULL.
 * If dtb is valid, it will move the device tree to its final place
 * in memory if necessary, and update the global dtb pointer accordingly.
 *
 * GNU g++ quirk note: if you include a prototype here like:
 * void dtb_setup()
 *
 * with the implementation in arch-dtb.cc containing the "constructor"
 * attribute, the result is that dtb_setup ends up in the init array,
 * but _with the wrong priority_
 */

/* size_t dtb_get_phys_memory(void **addr)
 *
 * puts the physical memory address in *addr, and
 * returns the size in bytes, or 0 to signal an error.
 */
size_t dtb_get_phys_memory(u64 *addr);

/* u64 dtb_get_uart_base()
 *
 * return the base address of the uart, or NULL on failure.
 */
u64 dtb_get_uart_base();

/* int gdb_get_timer_irq()
 *
 * returns the irqid of the virtual timer from the dtb,
 * or 0 on failure. 0 is safe since PPIs start from 16.
 */
int dtb_get_timer_irq();

/* bool dtb_get_gic_v2(u64 *dist, u64 *cpu)
 *
 * gets the GIC v2 distributor and cpu interface.
 * return false on failure.
 */
bool dtb_get_gic_v2(u64 *dist, size_t *dist_len, u64 *cpu, size_t *cpu_len);

/* size_t dtb_get_pci_cfg(u64 *addr);
 *
 * gets the PCI configuration space base address and length.
 * Returns 0 on failure.
 */
size_t dtb_get_pci_cfg(u64 *addr);

/* bool dtb_get_pci_ranges(u64 *addr, size_t *len, int n);
 *
 * gets the CPU addressable memory regions corresponding
 * to the to the PCI ranges. Returns false on failure.
 */
bool dtb_get_pci_ranges(u64 *addr, size_t *len, int n);

/* int dtb_get_pci_irqmap_count();
 *
 * gets the number of mappings between pci devices and platform IRQs.
 * a return value of -1 signals a parse error.
 */
int dtb_get_pci_irqmap_count();

/* u32 dtb_get_pci_irqmask();
 *
 * gets the mask for just the slot member of the pci address.
 * a return value of 0 signals a parse error.
 */
u32 dtb_get_pci_irqmask();

/* bool dtb_get_pci_irqmap(u32 *slots, int *irq_ids, int n);
 *
 * fills the passed arrays with up to n IRQ mappings.
 * Returns true on success, false on parse error.
 */
bool dtb_get_pci_irqmap(u32 *slots, int *irq_ids, int n);

#endif /* ARCH_DTB_HH */
