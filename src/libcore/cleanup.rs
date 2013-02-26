// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[doc(hidden)];
#[forbid(managed_heap_memory)];

use cast::transmute;
use io::{fd_t, WriterUtil};
use io;
use libc::{c_char, c_void, c_uint, intptr_t, uintptr_t, size_t};
use libc;
use kinds::Copy;
use managed::raw::{BoxRepr, BoxHeaderRepr,
                   RC_MANAGED_UNIQUE, RC_IMMORTAL};
use option::{Option,Some,None};
use ptr::{mut_null, null, to_unsafe_ptr, offset};
use sys::size_of;
use sys::{TypeDesc, size_of};
use task::each_retained_ptr;
use uint;
use vec;
use unstable::exchange_alloc;
use unstable::intrinsics::ctpop64;

/*
* A trie for holding pointers.
*/



// FIXME: need to manually update TrieNode when SHIFT changes
const SHIFT: uint = 4;
const SIZE: uint = 1 << SHIFT;
const MASK: uint = SIZE - 1;

enum Child<T> {
    Internal(~TrieNode<T>),
    External(uint,T),
    Nothing
}

pub struct TrieMap<T> {
    priv root: TrieNode<T>,
    priv length: uint
}

impl<T:Copy> TrieMap<T> {
    static pure fn new() -> TrieMap<T> {
        TrieMap {
            root: TrieNode::new(),
            length: 0
        }
    }

    fn clear(&mut self) {
        self.root = TrieNode::new();
        self.length = 0;
    }

    pure fn prev(&self, key: uint) ->
        Option<(uint,&self/T)> {
        prev(&self.root, key, 0)
    }

    pure fn next(&self, key: uint) ->
        Option<(uint,&self/T)> {
        next(&self.root, key, 0)
    }

    pure fn contains(&self, key: uint) -> bool {
        let mut node = &self.root;
        let mut idx = 0;
        loop {
            match node.children[chunk(key, idx)] {
              Internal(ref x) => node = &**x,
              External(stored,_) => return stored == key,
              Nothing => return false
            }
            idx += 1;
        }
    }

    fn each_mut(&mut self, f: fn(uint,&mut T) -> bool) {
        self.root.each_mut(f)
    }

    fn insert(&mut self, key: uint, val: T) -> bool {
        let ret = insert(&mut self.root.count,
                         &mut self.root.children[chunk(key, 0)],
                         key, val, 1);
        if ret { self.length += 1 }
        ret
    }

    fn remove(&mut self, key: uint) -> bool {
        let ret = remove(&mut self.root.count,
                         &mut self.root.children[chunk(key, 0)], key, 1);
        if ret { self.length -= 1 }
        ret
    }

}

struct TrieNode<T> {
    priv count: uint,
    priv children: [Child<T> * 16] // FIXME: can't use the SIZE constant yet
}

impl<T:Copy> TrieNode<T> {
    static pure fn new() -> TrieNode<T> {
        TrieNode{count: 0, children: [Nothing, ..SIZE]}
    }

    fn each_mut(&mut self, f: fn(uint, &mut T) -> bool) {
        for vec::each_mut(self.children) |child| {
            match *child {
                Internal(ref mut x) => {
                    // Sigh, not-very-composable for loops.
                    let mut stop = false;
                    for x.each_mut |k,v| {
                        if !f(k,v) {
                            stop = true;
                            break;
                        }
                    }
                    if stop {
                        break;
                    }
                }
                External(k, ref mut v) => {
                    if !f(k, v) {
                        break;
                    }
                }
                Nothing => ()
            }
        }
    }

}

#[inline(always)]
pure fn chunk(n: uint, idx: uint) -> uint {
    use core::sys;
    (n >> ((size_of::<uint>() * 8) - (SHIFT * (idx + 1)))) & MASK
}

pure fn prev<T>(node: &k/TrieNode<T>,
                mut key: uint,
                idx: uint) -> Option<(uint,&k/T)> {
    let mut c = chunk(key, idx) as int;
    while c >= 0 {
        match node.children[c] {
            Internal(ref sub) => {
                match prev(*sub, key, idx+1) {
                    None => (),
                    Some(v) => return Some(v)
                }
            }
            External(k,ref v) if k <= key => return Some((k,v)),
            External(_,_) | Nothing => ()
        }
        // If we find nothing in the c child, we move to the next-lowest
        // child in the array and ask for its _maximum_ value, since that's
        // necessarily the next-lowest all the way down.
        c -= 1;
        key = uint::max_value;
    }
    None
}

pure fn next<T>(node: &k/TrieNode<T>,
                mut key: uint,
                idx: uint) -> Option<(uint,&k/T)> {
    let mut c = chunk(key, idx) as int;
    while c < (SIZE as int) {
        match node.children[c] {
            Internal(ref sub) => {
                match next(*sub, key, idx+1) {
                    None => (),
                    Some(v) => return Some(v)
                }
            }
            External(k,ref v) if k >= key => return Some((k,v)),
            External(_,_) | Nothing => ()
        }
        // If we find nothing in the c child, we move to the next-highest
        // child in the array and ask for its _minimum_ value, since that's
        // necessarily the next-highest all the way down.
        c += 1;
        key = 0;
    }
    None
}


fn insert<T:Copy>(count: &mut uint,
                  child: &mut Child<T>,
                  key: uint,
                  val: T,
                  idx: uint) -> bool {
    let mut tmp = Nothing;
    tmp <-> *child;
    let mut added = false;
    *child = match tmp {
        External(ekey, eval) => {
            if ekey == key {
                External(ekey, val)
            } else {
                added = true;
                // conflict - split the node
                let mut new = ~TrieNode::new();
                insert(&mut new.count,
                       &mut new.children[chunk(ekey, idx)],
                       ekey, eval, idx + 1);
                insert(&mut new.count,
                       &mut new.children[chunk(key, idx)],
                       key, val, idx + 1);
                Internal(new)
            }
        }
        Internal(x) => {
            let mut x = x;
            added = insert(&mut x.count,
                           &mut x.children[chunk(key, idx)],
                           key, val, idx + 1);
            Internal(x)
        }
        Nothing => {
            *count += 1;
            added = true;
            External(key, val)
        }
    };
    added
}

fn remove<T>(count: &mut uint,
             child: &mut Child<T>,
             key: uint,
             idx: uint) -> bool {
    let (ret, this) = match *child {
        External(stored, _) => {
            if stored == key { (true, true) } else { (false, false) }
        }
        Internal(ref mut x) => {
            let ret = remove(&mut x.count, &mut x.children[chunk(key, idx)],
                             key, idx + 1);
            (ret, x.count == 0)
        }
        Nothing => (false, false)
    };

    if this {
        *child = Nothing;
        *count -= 1;
    }
    ret
}

#[cfg(notest)] use ptr::to_unsafe_ptr;

/**
 * Runtime structures
 *
 * NB: These must match the representation in the C++ runtime.
 */

type DropGlue<'self> = &'self fn(**TypeDesc, *c_void);
type FreeGlue<'self> = &'self fn(**TypeDesc, *c_void);

type TaskID = uintptr_t;

#[cfg(target_word_size = "64")]
pub struct StackSegment {
    prev: *StackSegment,
    next: *StackSegment,
    end: uintptr_t,
    valgrind_id: c_uint,
    rust_task: *Task,
    canary: uintptr_t,
    data: u8
}

#[cfg(target_word_size = "32")]
pub struct StackSegment {
    prev: *StackSegment,
    next: *StackSegment,
    end: uintptr_t,
    valgrind_id: c_uint,
    pad: u32,
    rust_task: *Task,
    canary: uintptr_t,
    data: u8
}

struct Scheduler { priv opaque: () }
struct SchedulerLoop { priv opaque: () }
struct Kernel { priv opaque: () }
struct Env { priv opaque: () }
struct AllocHeader { priv opaque: () }
struct MemoryRegion { priv opaque: () }

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
struct Registers {
    data: [u32, ..16]
}

#[cfg(target_arch="mips")]
struct Registers {
    data: [u32, ..32]
}

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
#[cfg(target_arch="mips")]
struct Context {
    regs: Registers,
    next: *Context,
    pad: [u32, ..3]
}

#[cfg(target_arch="x86_64")]
struct Registers {
    data: [u64, ..22]
}

#[cfg(target_arch="x86_64")]
struct Context {
    regs: Registers,
    next: *Context,
    pad: uintptr_t
}

pub struct BoxedRegion {
    env: *Env,
    backing_region: *MemoryRegion,
    live_allocs: *BoxRepr,
}

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
#[cfg(target_arch="mips")]
pub struct Task {
    // Public fields
    refcount: intptr_t,                 // 0
    id: TaskID,                         // 4
    pad: [u32, ..2],                    // 8
    ctx: Context,                       // 16
    stack_segment: *StackSegment,       // 96
    runtime_sp: uintptr_t,              // 100
    scheduler: *Scheduler,              // 104
    scheduler_loop: *SchedulerLoop,     // 108

    // Fields known only to the runtime
    kernel: *Kernel,                    // 112
    name: *c_char,                      // 116
    list_index: i32,                    // 120
    boxed_region: BoxedRegion,          // 128
    gc: *c_void,                        // 132
}

#[cfg(target_arch="x86_64")]
pub struct Task {
    // Public fields
    refcount: intptr_t,
    id: TaskID,
    ctx: Context,
    stack_segment: *StackSegment,
    runtime_sp: uintptr_t,
    scheduler: *Scheduler,
    scheduler_loop: *SchedulerLoop,

    // Fields known only to the runtime
    kernel: *Kernel,
    name: *c_char,
    list_index: i32,
    boxed_region: BoxedRegion,
    gc: *c_void,
}

// A transmuted ~to one of these is held in the task.
// The annihilator drops it. Until then, all GC runs
// through it.

struct HeapRecord {
    size: uint,
    is_marked: bool
}

pub struct Gc {
    task: *Task,
    debug_gc: bool,
    actually_gc: bool,
    report_gc_stats: bool,

    gc_in_progress: bool,
    free_buffer: TrieMap<()>,
    heap: TrieMap<HeapRecord>,
    lowest: uint,
    highest: uint,

    threshold: uint,

    n_collections: uint,
    n_boxes_marked: Stat,
    n_bytes_marked: Stat,
    n_boxes_swept: Stat,
    n_bytes_swept: Stat,
    n_boxes_annihilated: Stat,
    n_bytes_annihilated: Stat,
}

#[cfg(unix)]
fn debug_mem() -> bool {
    ::rt::env::get().debug_mem
}

pub impl Gc {
    static fn get_task_gc() -> &mut Gc {
        unsafe {
            let tp : *Task = transmute(rust_get_task());
            let task : &mut Task = transmute(tp);
            if task.gc == null() {
                task.gc = transmute(~Gc::new(tp));
            }
            let p: &mut ~Gc = transmute(&(task.gc));
            &mut (**p)
        }
    }


    #[cfg(unix)]
    static fn debug_gc() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_DEBUG_GC") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(unix)]
    static fn report_gc_stats() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_REPORT_GC_STATS") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(unix)]
    static fn actually_gc() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_ACTUALLY_GC") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(windows)]
    static fn debug_gc() -> bool {
        false
    }

    #[cfg(windows)]
    static fn report_gc_stats() -> bool {
        false
    }
    
    #[cfg(windows)]
    static fn actually_gc() -> bool {
        false
    }

    static fn new(t: *Task) -> Gc {
        Gc {
            task: t,
            debug_gc: Gc::debug_gc(),
            actually_gc: Gc::actually_gc(),
            report_gc_stats: Gc::report_gc_stats(),

            gc_in_progress: false,
            free_buffer: TrieMap::new(),
            heap: TrieMap::new(),
            lowest: 0,
            highest: 0,

            threshold: 1024,

            n_collections: 0,
            n_boxes_marked: Stat::new(),
            n_bytes_marked: Stat::new(),
            n_boxes_swept: Stat::new(),
            n_bytes_swept: Stat::new(),
            n_boxes_annihilated: Stat::new(),
            n_bytes_annihilated: Stat::new(),
        }
    }

    #[inline(always)]
    static fn stderr_fd() -> fd_t {
        libc::STDERR_FILENO as fd_t
    }

    #[inline(always)]
    fn debug_str(&self, s: &str) {
        if self.debug_gc {
            Gc::stderr_fd().write_str(s)
        }
    }

    #[inline(always)]
    fn debug_uint(&self, n: uint) {
        if self.debug_gc {
            Gc::stderr_fd().write_uint(n)
        }
    }

    #[inline(always)]
    fn debug_str_hex(&self, s: &str, p: uint) {
        if self.debug_gc {
            Gc::write_str_hex(s, p);
        }
    }

    #[inline(always)]
    fn debug_str_range(&self, s: &str,
                       p: uint, len: uint) {
        if self.debug_gc {
            let e = Gc::stderr_fd();
            e.write_str(s);
            e.write_str(": [");
            e.write_hex_uint(p);
            e.write_str(", ");
            e.write_hex_uint(p + len);
            e.write_str(") = ");
            e.write_uint(len);
            e.write_str(" bytes\n");
        }
    }

    static fn write_str_uint(s: &str, n: uint) {
        let e = Gc::stderr_fd();
        e.write_str(s);
        e.write_str(": ");
        e.write_uint(n);
        e.write_str("\n");
    }

    static fn write_str_hex(s: &str, n: uint) {
        let e = Gc::stderr_fd();
        e.write_str(s);
        e.write_str(": ");
        e.write_hex_uint(n);
        e.write_str("\n");
    }

    fn report_stat(&self, s: &str, t: &Stat) {
        Gc::stderr_fd().write_str("    ");
        Gc::write_str_uint(s, t.total as uint);
    }

    fn report_stats() {
        if self.report_gc_stats {
            Gc::write_str_uint("    n_collections",
                               self.n_collections);
            self.report_stat("n_boxes_marked",
                             &self.n_boxes_marked);
            self.report_stat("n_bytes_marked",
                             &self.n_bytes_marked);
            self.report_stat("n_boxes_swept",
                             &self.n_boxes_swept);
            self.report_stat("n_bytes_swept",
                             &self.n_bytes_swept);
            self.report_stat("n_boxes_annihilated",
                             &self.n_boxes_annihilated);
            self.report_stat("n_bytes_annihilated",
                             &self.n_bytes_annihilated);
        }
    }

    fn note_alloc(&mut self, ptr: uint, sz: uint, align: uint) {
        assert !self.gc_in_progress;
        let h = HeapRecord {
            size: exchange_alloc::get_box_size(sz, align),
            is_marked: false
        };
        self.debug_str_range("gc::note_malloc", ptr, h.size);
        self.heap.insert(ptr, h);
        if ! self.actually_gc {
            return;
        }
        if self.heap.length > self.threshold {
            self.debug_str("commencing gc at threshold: ");
            self.debug_uint(self.threshold);
            self.debug_str("\n");
            let prev = self.heap.length;
            unsafe {
                self.gc();
            }
            self.debug_str("gc complete, heap count: ");
            self.debug_uint(self.heap.length);
            self.debug_str(" (freed ");
            self.debug_uint(prev - self.heap.length);
            self.debug_str(" boxes)\n");
            if self.heap.length * 2 > self.threshold {
                self.debug_str("gc did not recover enough, \
                                raising threshold to: ");
                self.debug_uint(self.threshold * 2);
                self.debug_str("\n");
                self.threshold *= 2;
            }
        }
    }

    fn note_free(&mut self, ptr: uint) {
        self.debug_str_hex("gc::note_free", ptr);
        if self.gc_in_progress {
            self.free_buffer.insert(ptr, ());
        } else {
            self.heap.remove(ptr);
            if ! self.actually_gc {
                return;
            }
            if self.heap.length < (self.threshold / 4) {
                self.debug_str("lowering gc threshold to: ");
                self.debug_uint(self.threshold / 2);
                self.debug_str("\n");
                self.threshold /= 2;
            }
        }
    }

    fn note_realloc(&mut self, from: uint, to: uint, sz: uint) {
        assert !self.gc_in_progress;
        if self.debug_gc {
            let e = Gc::stderr_fd();
            e.write_str("gc::note_realloc: ");
            e.write_hex_uint(from);
            e.write_str(" -> [");
            e.write_hex_uint(to);
            e.write_str(", ");
            e.write_hex_uint(to + sz);
            e.write_str(")\n");
        }
        self.heap.remove(from);
        let h = HeapRecord {
            size: sz,
            is_marked: false
        };
        self.heap.insert(to, h);
    }

    fn check_consistency(&mut self, phase: &str) {
        let mut tmp = TrieMap::new();
        for self.each_live_alloc |box| {
            let box = box as uint;
            if ! self.heap.contains(box) {
                Gc::stderr_fd().write_str(phase);
                Gc::write_str_hex(" inconsistency: gc heap \
                                   missing live alloc ptr",
                                  box)
            }
            tmp.insert(box, ());
        }
        for self.heap.each_mut |box, _| {
            if ! tmp.contains(box) {
                Gc::stderr_fd().write_str(phase);
                Gc::write_str_hex(" inconsistency: live allocs \
                                   missing gc heap ptr",
                                  box)
            }
        }
        if self.heap.length != tmp.length {
            Gc::stderr_fd().write_str(phase);
            Gc::write_str_uint(" inconsistency: num gc heap ptr",
                               self.heap.length);
            Gc::stderr_fd().write_str(phase);
            Gc::write_str_uint(" inconsistency: num live alloc ptrs",
                               tmp.length);
        }
    }

    unsafe fn each_live_alloc(&self, f: &fn(box: *mut BoxRepr) -> bool) {
        use managed;
        let box = (*self.task).boxed_region.live_allocs;
        let mut box: *mut BoxRepr = transmute(copy box);
        while box != mut_null() {
            let next = transmute(copy (*box).header.next);
            if ! f(box) {
                break
            }
            box = next
        }
    }
                  
    static unsafe fn drop_boxes(actually_drop: bool,
                                debug_flag: bool,
                                free_buffer: &mut TrieMap<()>,
                                each: fn(fn(*mut BoxRepr) -> bool)) {
        
        for each |boxp| {
            if free_buffer.contains(boxp as uint) {
                loop;
            }
            let box: &mut BoxRepr = transmute(boxp);
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #1: setting immortal",
                                  boxp as uint);
            }
            if actually_drop {
                box.header.ref_count = RC_IMMORTAL;
            }
        }

        for each |boxp| {
            if free_buffer.contains(boxp as uint) {
                loop;
            }
            let box: &BoxRepr = transmute(boxp);
            let tydesc: *TypeDesc = transmute(box.header.type_desc);
            let drop_glue: DropGlue = transmute(((*tydesc).drop_glue, 0));
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #2: running drop glue",
                                  boxp as uint);
            }
            if actually_drop {
                drop_glue(to_unsafe_ptr(&tydesc),
                          transmute(&(*box).data));
            }
        }

        for each |boxp| {
            if free_buffer.contains(boxp as uint) {
                loop;
            }
            let box: &BoxRepr = transmute(boxp);
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #3: freeing",
                                  boxp as uint);
            }
            if actually_drop {
                rust_upcall_free(transmute(box));
                free_buffer.insert(boxp as uint, ());
            }
        }
    }

    unsafe fn mark_object(&mut self,
                          level: uint,
                          addr: uint) {

        if addr < self.lowest || addr > self.highest {
            self.debug_str_hex("implausible heap addr", addr);
            return;
        }

        self.debug_str_hex("searching for prev object", addr);
        let (obj, record) = match self.heap.prev(addr) {
            None => {
                self.debug_str_hex("no object found", addr);
                return
            }
            Some((obj,rptr)) => (obj, *rptr)
        };

        if addr > obj + record.size {
            self.debug_str_range("address past object-end",
                                 obj, record.size);
            // We picked the object previous to the probe addr; but that
            // object might not extend all the way to _include_ the probe
            // addr. If not, skip.
            return;
        }

        if record.is_marked {
            self.debug_str_hex("object already marked", obj);
            // if we've already visited, don't visit again.
            return;
        }
        let record = HeapRecord {
            is_marked: true,
            ..record
        };
        self.heap.insert(obj, record);
        let adj = size_of::<BoxHeaderRepr>();
        self.mark_range("marking object", level + 1,
                        obj + adj, record.size - adj);
    }
                         
    unsafe fn mark_stack(&mut self) {

        // We want to avoid marking frames below us, so we
        // take a base address from the current frame and
        // pass it into the stack-marker.
        let base = 0;
        let base : uint = transmute(&base);
        let mut segment = (*self.task).stack_segment;
        while segment != null() {
            let mut ptr: uint = transmute(&(*segment).data);
            let mut end: uint = transmute(copy (*segment).end);
            if ptr <= base && base < end {
                self.debug_str_hex("limiting stack-marking to base",
                                   base);
                ptr = base;
            }
            self.mark_range("marking stack segment",
                            0, ptr, end-ptr);
            segment = (*segment).prev;
        }
    }

    unsafe fn mark_range(&mut self,
                         s: &str, level: uint,
                         p: uint, sz: uint) {
        self.debug_str("level ");
        self.debug_uint(level);
        self.debug_str(": ");
        self.debug_str_range(s, p, sz);
        let mut curr = p;
        let end = p + sz;
        while curr + size_of::<uint>() <= end {
            self.mark_object(level, *(curr as *uint));
            curr += 1;
        }
    }

    unsafe fn mark(&mut self) {

        self.lowest = match self.heap.next(0) {
            None => 0,
            Some((k, _)) => k
        };
        self.highest = match self.heap.prev(uint::max_value) {
            None => uint::max_value,
            Some((k, r)) => k + r.size
        };

        self.debug_str_hex("lowest heap ptr", self.lowest);
        self.debug_str_hex("highest heap ptr", self.highest);
        
        self.mark_stack();

        
        self.debug_str("marking TLS values\n");
        do each_retained_ptr(transmute(self.task)) |p| {
            self.debug_str_hex("marking TLS value",
                               transmute(p));
            self.mark_object(0, transmute(p));
        }

        // Awkward but necessary: registers must be 16-byte
        // aligned on x64 due to dumping xmm state using
        // movapd. So we don't use the Registers structure.
        self.debug_str("marking registers\n");
        let regs = [0u64, ..64];
        let r : uint = transmute(&regs);
        let r = (r + 16) & (!15);
        swap_registers(transmute(r), transmute(r));
        for regs.each |r| {
            self.mark_object(0, transmute(*r));
        }
    }

    unsafe fn sweep(&mut self) {        
        do Gc::drop_boxes(self.actually_gc,
                          self.debug_gc,
                          &mut self.free_buffer) |step| {
            for self.heap.each_mut |ptr, record| {
                if record.is_marked {
                    loop;
                }
                let box: &BoxRepr = transmute(ptr);
                if box.header.ref_count == RC_MANAGED_UNIQUE {
                    loop;
                }
                step(transmute(ptr));
            }
        }

        // Clear all mark bits
        for self.heap.each_mut |_, record| {
            record.is_marked = false;
        }

        // Clean out the free buffer
        for self.free_buffer.each_mut |ptr, _| {
            self.heap.remove(ptr);
            ()
        }

        self.free_buffer.clear();
    }

    unsafe fn gc(&mut self) {
        // NB: need this here before we lock down the GC, to make sure
        // TLS is initialized; easiest approach. It allocates a @Dvec.
        do each_retained_ptr(transmute(self.task)) |_| { }

        self.gc_in_progress = true;
        self.check_consistency("pre-gc");
        self.mark();
        self.sweep();
        self.check_consistency("post-gc");
        self.gc_in_progress = false; 
    }

    unsafe fn annihilate(&mut self) {
        self.check_consistency("pre-annihilate");
        self.gc_in_progress = true;
        do Gc::drop_boxes(true,
                          self.debug_gc,
                          &mut self.free_buffer) |step| {
            for self.heap.each_mut |ptr, _| {
                let box: &BoxRepr = transmute(ptr);
                if box.header.ref_count != RC_MANAGED_UNIQUE {
                    step(transmute(ptr));
                }
            }
        }
        for self.free_buffer.each_mut |ptr, _| {
            self.heap.remove(ptr);
            ()
        }
        self.gc_in_progress = false;
        self.check_consistency("post-annihilate");
    }
}

pub struct Stat {
    curr: i64,
    total: i64,
    hist: [i64 * 64],
}

pub impl Stat {
    fn flush(&mut self) {
        self.total += self.curr;
        unsafe {
            self.hist[ctpop64(self.curr)] += 1;
        }
        self.curr = 0;
    }
    static fn new() -> Stat {
        Stat {
            curr: 0,
            total: 0,
            hist: [0, ..64]
        }
    }
}


/*
 * Box annihilation
 *
 * This runs at task death to free all boxes.
 */


/// Destroys all managed memory (i.e. @ boxes) held by the current task.
#[cfg(notest)]
#[lang="annihilate"]
pub unsafe fn annihilate() {
    let gc : &mut Gc = Gc::get_task_gc();
    gc.annihilate();
    let task: &Task = transmute(rust_get_task());
    let _dropme: ~Gc = transmute(task.gc);
}

pub fn gc() {
    unsafe {
        Gc::get_task_gc().gc();
    }
}

#[link_name = "rustrt"]
extern {
    #[rust_stack]
    // FIXME (#4386): Unable to make following method private.
    fn rust_get_task() -> *c_void;

    #[rust_stack]
    fn rust_upcall_free(ptr: *c_char);

    #[rust_stack]
    fn swap_registers(out_regs: *mut Registers, in_regs: *Registers);
}

