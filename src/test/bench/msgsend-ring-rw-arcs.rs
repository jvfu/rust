// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This test creates a bunch of tasks that simultaneously send to each
// other in a ring. The messages should all be basically
// independent.
// This is like msgsend-ring-pipes but adapted to use ARCs.

// This also serves as a pipes test, because ARCs are implemented with pipes.

extern mod std;
use std::time;
use std::arc;
use std::future;

// A poor man's pipe.
type pipe = arc::RWARC<~[uint]>;

fn send(p: &pipe, msg: uint) {
    do p.write_cond |state, cond| {
        state.push(msg);
        cond.signal();
    }
}
fn recv(p: &pipe) -> uint {
    do p.write_cond |state, cond| {
        while vec::is_empty(*state) {
            cond.wait();
        }
        state.pop()
    }
}

fn init() -> (pipe,pipe) {
    let x = arc::RWARC(~[]);
    ((&x).clone(), move x)
}


fn thread_ring(i: uint,
               count: uint,
               +num_chan: pipe,
               +num_port: pipe) {
    let mut num_chan = move Some(move num_chan);
    let mut num_port = move Some(move num_port);
    // Send/Receive lots of messages.
    for uint::range(0u, count) |j| {
        //error!("task %?, iter %?", i, j);
        let mut num_chan2 = option::swap_unwrap(&mut num_chan);
        let mut num_port2 = option::swap_unwrap(&mut num_port);
        send(&num_chan2, i * j);
        num_chan = Some(move num_chan2);
        let _n = recv(&num_port2);
        //log(error, _n);
        num_port = Some(move num_port2);
    };
}

fn main() {
    let args = os::args();
    let args = if os::getenv(~"RUST_BENCH").is_some() {
        ~[~"", ~"100", ~"10000"]
    } else if args.len() <= 1u {
        ~[~"", ~"10", ~"100"]
    } else {
        copy args
    }; 

    let num_tasks = uint::from_str(args[1]).get();
    let msg_per_task = uint::from_str(args[2]).get();

    let (num_chan, num_port) = init();
    let mut num_chan = Some(move num_chan);

    let start = time::precise_time_s();

    // create the ring
    let mut futures = ~[];

    for uint::range(1u, num_tasks) |i| {
        //error!("spawning %?", i);
        let (new_chan, num_port) = init();
        let num_chan2 = ~mut None;
        *num_chan2 <-> num_chan;
        let num_port = ~mut Some(move num_port);
        let new_future = do future::spawn
            |move num_chan2, move num_port| {
            let mut num_chan = None;
            num_chan <-> *num_chan2;
            let mut num_port1 = None;
            num_port1 <-> *num_port;
            thread_ring(i, msg_per_task,
                        option::unwrap(move num_chan),
                        option::unwrap(move num_port1))
        };
        futures.push(move new_future);
        num_chan = Some(move new_chan);
    };

    // do our iteration
    thread_ring(0, msg_per_task, option::unwrap(move num_chan), move num_port);

    // synchronize
    for futures.each |f| { future::get(f) };

    let stop = time::precise_time_s();

    // all done, report stats.
    let num_msgs = num_tasks * msg_per_task;
    let elapsed = (stop - start);
    let rate = (num_msgs as float) / elapsed;

    io::println(fmt!("Sent %? messages in %? seconds",
                     num_msgs, elapsed));
    io::println(fmt!("  %? messages / second", rate));
    io::println(fmt!("  %? μs / message", 1000000. / rate));
}
