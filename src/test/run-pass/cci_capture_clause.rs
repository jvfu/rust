// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// aux-build:cci_capture_clause.rs
// xfail-fast

// This test makes sure we can do cross-crate inlining on functions
// that use capture clauses.

#[legacy_exports];

extern mod cci_capture_clause;

use comm::recv;

fn main() {
    cci_capture_clause::foo(()).recv()
}
