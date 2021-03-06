// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

fn is_even(+x: uint) -> bool { (x % 2) == 0 }

fn main() {
    assert [1, 3].filter_to_vec(is_even) == ~[];
    assert [1, 2, 3].filter_to_vec(is_even) == ~[2];
    assert None.filter_to_vec(is_even) == ~[];
    assert Some(1).filter_to_vec(is_even) == ~[];
    assert Some(2).filter_to_vec(is_even) == ~[2];
}
