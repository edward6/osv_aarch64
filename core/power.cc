/*
 * Copyright (C) 2013 Cloudius Systems, Ltd.
 *
 * This work is open source software, licensed under the terms of the
 * BSD license as described in the LICENSE file in the top-level directory.
 */

#include <osv/power.hh>
#include <osv/debug.hh>
#include <smp.hh>
#include <processor.hh>
#include <arch.hh>

#include <sys/reboot.h>

#ifndef AARCH64_PORT_STUB
extern "C" {
#include "acpi.h"
}
#endif /* !AARCH64_PORT_STUB */

namespace osv {

// NOTE: Please do not print informational messages from inside halt() or
// poweroff(), as they may be called in situations where OSV's state
// is questionable (e.g., abort()) so a debug() call might call further
// problems.

void halt(void)
{
#ifndef AARCH64_PORT_STUB
    crash_other_processors();
#endif /* !AARCH64_PORT_STUB */

    while (true) {
        arch::halt_no_interrupts();
    }
}

void poweroff(void)
{
#ifndef AARCH64_PORT_STUB
    ACPI_STATUS status = AcpiEnterSleepStatePrep(ACPI_STATE_S5);
    if (ACPI_FAILURE(status)) {
        debug("AcpiEnterSleepStatePrep failed: %s\n", AcpiFormatException(status));
        halt();
    }
    status = AcpiEnterSleepState(ACPI_STATE_S5);
    if (ACPI_FAILURE(status)) {
        debug("AcpiEnterSleepState failed: %s\n", AcpiFormatException(status));
        halt();
    }
#endif /* !AARCH64_PORT_STUB */

    // We shouldn't get here on x86.
    halt();
}

// reboot() does not normally return, but may return if the reboot magic for
// some reason fails.
void reboot(void)
{
#ifdef __x86_64__
    // It would be nice if AcpiReset() worked, but it doesn't seem to work
    // (on qemu & kvm), so let's resort to brute force...
    processor::outb(1, 0x92);
    debug("osv::reboot() did not work :(\n");
#else /* !__x86_64__ */
    // FIXME:
    halt();
#endif /* __x86_64__ */
}


} /* namespace osv */

int reboot(int cmd)
{
    switch (cmd) {
    case RB_POWER_OFF:
        printf("Power down\n");
        osv::poweroff();
        break;
    case RB_HALT_SYSTEM:
        printf("System halted\n");
        osv::halt();
        break;
    case RB_AUTOBOOT:
        printf("Restarting system\n");
        osv::reboot();
        break;
    case RB_SW_SUSPEND:
    case RB_ENABLE_CAD:
    case RB_DISABLE_CAD:
    case RB_KEXEC:
    default:
        return EINVAL;
    }

    return 0;
}
