/*
 * Copyright (C) 2014 Huawei Technologies Duesseldorf GmbH
 *
 * This work is open source software, licensed under the terms of the
 * BSD license as described in the LICENSE file in the top-level directory.
 */

#include <osv/debug.hh>
#include <osv/prio.hh>
#include "exceptions.hh"
#include "gic.hh"

__thread exception_frame* current_interrupt_frame;
class interrupt_table interrupt_table __attribute__((init_priority((int)init_prio::idt)));

interrupt_table::interrupt_table() {
    debug_early_entry("interrupt_table::interrupt_table()");

    debug_early("calling gic::gic_driver(d, c)\n");
    /* XXX hardcoded addresses */
    gic::gic_driver = new class gic::gic_driver(0x8001000, 0x8002000);
    debug_early("calling gic::gic_driver::init_cpu(0)\n");
    gic::gic_driver->init_cpu(0);
    debug_early("calling gic::gic_driver::init_dist(0)\n");
    gic::gic_driver->init_dist(0);

    this->nr_irqs = gic::gic_driver->nr_irqs;

    debug_early("returning from interrupt_table::interrupt_table()\n");
}

void interrupt_table::enable_irqs()
{
    int i;
    for (i = 0; i < this->nr_irqs; i++) {
        struct interrupt_desc *desc = &this->irq_desc[i];
        if (desc->handler) {
            debug_early_u64("enabling InterruptID=", desc->id);
            gic::gic_driver->set_irq_type(desc->id, gic::irq_type::IRQ_TYPE_EDGE);
            gic::gic_driver->unmask_irq(desc->id);
        }
    }
}

void interrupt_table::register_handler(int i, interrupt_handler h)
{
    WITH_LOCK(_lock) {
        assert(i < this->nr_irqs);
        struct interrupt_desc *desc = &this->irq_desc[i];

        if (desc->handler) {
            debug_early_u64("already registered IRQ id=", (u64)i);
            return;
        }

        desc->init(i, h);
        debug_early_u64("registered IRQ id=", (u64)i);
    }
}

void interrupt_table::invoke_interrupt(int id)
{
    WITH_LOCK(osv::rcu_read_lock) {
        assert(id < this->nr_irqs);
        struct interrupt_desc *desc = &this->irq_desc[id];

        if (!desc->handler) {
            return;
        }

        desc->handler(desc);
    }
}

extern "C" { void interrupt(exception_frame* frame); }

void interrupt(exception_frame* frame)
{
    // Rather that force the exception frame down the call stack,
    // remember it in a global here.  This works because our interrupts
    // don't nest.
    current_interrupt_frame = frame;
    debug_early("interrupt() reached.\n");
    asm volatile ("1: wfi; b 1b;");
    /*
    unsigned vector = frame->error_code;
    idt.invoke_interrupt(vector);
    // must call scheduler after EOI, or it may switch contexts and miss the EOI
    current_interrupt_frame = nullptr;
    // FIXME: layering violation
    sched::preempt();
    */
}
