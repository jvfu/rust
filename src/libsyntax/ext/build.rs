// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use codemap::span;
use base::ext_ctxt;

fn mk_expr(cx: ext_ctxt, sp: codemap::span, expr: ast::expr_) ->
    @ast::expr {
    return @{id: cx.next_id(), callee_id: cx.next_id(),
          node: expr, span: sp};
}

fn mk_lit(cx: ext_ctxt, sp: span, lit: ast::lit_) -> @ast::expr {
    let sp_lit = @{node: lit, span: sp};
    mk_expr(cx, sp, ast::expr_lit(sp_lit))
}
fn mk_int(cx: ext_ctxt, sp: span, i: int) -> @ast::expr {
    let lit = ast::lit_int(i as i64, ast::ty_i);
    return mk_lit(cx, sp, lit);
}
fn mk_uint(cx: ext_ctxt, sp: span, u: uint) -> @ast::expr {
    let lit = ast::lit_uint(u as u64, ast::ty_u);
    return mk_lit(cx, sp, lit);
}
fn mk_u8(cx: ext_ctxt, sp: span, u: u8) -> @ast::expr {
    let lit = ast::lit_uint(u as u64, ast::ty_u8);
    return mk_lit(cx, sp, lit);
}
fn mk_binary(cx: ext_ctxt, sp: span, op: ast::binop,
             lhs: @ast::expr, rhs: @ast::expr)
   -> @ast::expr {
    cx.next_id(); // see ast_util::op_expr_callee_id
    mk_expr(cx, sp, ast::expr_binary(op, lhs, rhs))
}
fn mk_unary(cx: ext_ctxt, sp: span, op: ast::unop, e: @ast::expr)
    -> @ast::expr {
    cx.next_id(); // see ast_util::op_expr_callee_id
    mk_expr(cx, sp, ast::expr_unary(op, e))
}
fn mk_raw_path(sp: span, idents: ~[ast::ident]) -> @ast::path {
    let p : @ast::path = @{span: sp, global: false, idents: idents,
                           rp: None, types: ~[]};
    return p;
}
fn mk_raw_path_(sp: span,
                idents: ~[ast::ident],
                +types: ~[@ast::Ty])
             -> @ast::path {
    @{ span: sp, global: false, idents: idents, rp: None, types: move types }
}
fn mk_path(cx: ext_ctxt, sp: span, idents: ~[ast::ident]) ->
    @ast::expr {
    mk_expr(cx, sp, ast::expr_path(mk_raw_path(sp, idents)))
}
fn mk_access_(cx: ext_ctxt, sp: span, p: @ast::expr, m: ast::ident)
    -> @ast::expr {
    mk_expr(cx, sp, ast::expr_field(p, m, ~[]))
}
fn mk_access(cx: ext_ctxt, sp: span, p: ~[ast::ident], m: ast::ident)
    -> @ast::expr {
    let pathexpr = mk_path(cx, sp, p);
    return mk_access_(cx, sp, pathexpr, m);
}
fn mk_addr_of(cx: ext_ctxt, sp: span, e: @ast::expr) -> @ast::expr {
    return mk_expr(cx, sp, ast::expr_addr_of(ast::m_imm, e));
}
fn mk_call_(cx: ext_ctxt, sp: span, fn_expr: @ast::expr,
            args: ~[@ast::expr]) -> @ast::expr {
    mk_expr(cx, sp, ast::expr_call(fn_expr, args, false))
}
fn mk_call(cx: ext_ctxt, sp: span, fn_path: ~[ast::ident],
             args: ~[@ast::expr]) -> @ast::expr {
    let pathexpr = mk_path(cx, sp, fn_path);
    return mk_call_(cx, sp, pathexpr, args);
}
// e = expr, t = type
fn mk_base_vec_e(cx: ext_ctxt, sp: span, exprs: ~[@ast::expr]) ->
   @ast::expr {
    let vecexpr = ast::expr_vec(exprs, ast::m_imm);
    mk_expr(cx, sp, vecexpr)
}
fn mk_vstore_e(cx: ext_ctxt, sp: span, expr: @ast::expr,
               vst: ast::expr_vstore) ->
   @ast::expr {
    mk_expr(cx, sp, ast::expr_vstore(expr, vst))
}
fn mk_uniq_vec_e(cx: ext_ctxt, sp: span, exprs: ~[@ast::expr]) ->
   @ast::expr {
    mk_vstore_e(cx, sp, mk_base_vec_e(cx, sp, exprs), ast::expr_vstore_uniq)
}
fn mk_slice_vec_e(cx: ext_ctxt, sp: span, exprs: ~[@ast::expr]) ->
   @ast::expr {
    mk_vstore_e(cx, sp, mk_base_vec_e(cx, sp, exprs),
                ast::expr_vstore_slice)
}
fn mk_fixed_vec_e(cx: ext_ctxt, sp: span, exprs: ~[@ast::expr]) ->
   @ast::expr {
    mk_vstore_e(cx, sp, mk_base_vec_e(cx, sp, exprs),
                ast::expr_vstore_fixed(None))
}
fn mk_base_str(cx: ext_ctxt, sp: span, s: ~str) -> @ast::expr {
    let lit = ast::lit_str(@s);
    return mk_lit(cx, sp, lit);
}
fn mk_uniq_str(cx: ext_ctxt, sp: span, s: ~str) -> @ast::expr {
    mk_vstore_e(cx, sp, mk_base_str(cx, sp, s), ast::expr_vstore_uniq)
}
fn mk_field(sp: span, f: &{ident: ast::ident, ex: @ast::expr})
    -> ast::field {
    {node: {mutbl: ast::m_imm, ident: f.ident, expr: f.ex}, span: sp}
}
fn mk_fields(sp: span, fields: ~[{ident: ast::ident, ex: @ast::expr}]) ->
    ~[ast::field] {
    move fields.map(|f| mk_field(sp, f))
}
fn mk_rec_e(cx: ext_ctxt, sp: span,
            fields: ~[{ident: ast::ident, ex: @ast::expr}]) ->
    @ast::expr {
    mk_expr(cx, sp, ast::expr_rec(mk_fields(sp, fields),
                                  option::None::<@ast::expr>))
}
fn mk_struct_e(cx: ext_ctxt, sp: span,
               ctor_path: ~[ast::ident],
               fields: ~[{ident: ast::ident, ex: @ast::expr}]) ->
    @ast::expr {
    mk_expr(cx, sp,
            ast::expr_struct(mk_raw_path(sp, ctor_path),
                             mk_fields(sp, fields),
                                    option::None::<@ast::expr>))
}
fn mk_glob_use(cx: ext_ctxt, sp: span,
               path: ~[ast::ident]) -> @ast::view_item {
    let glob = @{node: ast::view_path_glob(mk_raw_path(sp, path),
                                          cx.next_id()),
                span: sp};
    @{node: ast::view_item_import(~[glob]),
      attrs: ~[],
      vis: ast::private,
      span: sp}
}
fn mk_local(cx: ext_ctxt, sp: span, mutbl: bool,
            ident: ast::ident, ex: @ast::expr) -> @ast::stmt {

    let pat : @ast::pat = @{id: cx.next_id(),
                            node: ast::pat_ident(ast::bind_by_value,
                                                 mk_raw_path(sp, ~[ident]),
                                                 None),
                           span: sp};
    let ty : @ast::Ty = @{ id: cx.next_id(), node: ast::ty_infer, span: sp };
    let local : @ast::local = @{node: {is_mutbl: mutbl,
                                       ty: ty,
                                       pat: pat,
                                       init: Some(ex),
                                       id: cx.next_id()},
                                span: sp};
    let decl = {node: ast::decl_local(~[local]), span: sp};
    @{ node: ast::stmt_decl(@decl, cx.next_id()), span: sp }
}
fn mk_block(cx: ext_ctxt, sp: span,
            view_items: ~[@ast::view_item],
            stmts: ~[@ast::stmt],
            expr: Option<@ast::expr>) -> @ast::expr {
    let blk = {node: {view_items: view_items,
                      stmts: stmts,
                      expr: expr,
                      id: cx.next_id(),
                      rules: ast::default_blk },
               span: sp };
    mk_expr(cx, sp, ast::expr_block(blk))
}
fn mk_block_(cx: ext_ctxt, sp: span, +stmts: ~[@ast::stmt]) -> ast::blk {
    {
        node: {
            view_items: ~[],
            stmts: move stmts,
            expr: None,
            id: cx.next_id(),
            rules: ast::default_blk
        },
        span: sp
    }
}
fn mk_simple_block(cx: ext_ctxt, span: span, expr: @ast::expr) -> ast::blk {
    let block = {
        view_items: ~[],
        stmts: ~[],
        expr: Some(expr),
        id: cx.next_id(),
        rules: ast::default_blk
    };
    { node: move block, span: span }
}
fn mk_copy(cx: ext_ctxt, sp: span, e: @ast::expr) -> @ast::expr {
    mk_expr(cx, sp, ast::expr_copy(e))
}
fn mk_managed(cx: ext_ctxt, sp: span, e: @ast::expr) -> @ast::expr {
    mk_expr(cx, sp, ast::expr_unary(ast::box(ast::m_imm), e))
}
fn mk_pat(cx: ext_ctxt, span: span, +pat: ast::pat_) -> @ast::pat {
    @{ id: cx.next_id(), node: move pat, span: span }
}
fn mk_pat_ident(cx: ext_ctxt, span: span, ident: ast::ident) -> @ast::pat {
    let path = mk_raw_path(span, ~[ ident ]);
    let pat = ast::pat_ident(ast::bind_by_value, path, None);
    mk_pat(cx, span, move pat)
}
fn mk_pat_enum(cx: ext_ctxt,
               span: span,
               path: @ast::path,
               +subpats: ~[@ast::pat])
            -> @ast::pat {
    let pat = ast::pat_enum(path, Some(move subpats));
    mk_pat(cx, span, move pat)
}
fn mk_bool(cx: ext_ctxt, span: span, value: bool) -> @ast::expr {
    let lit_expr = ast::expr_lit(@{ node: ast::lit_bool(value), span: span });
    build::mk_expr(cx, span, move lit_expr)
}
fn mk_stmt(cx: ext_ctxt, span: span, expr: @ast::expr) -> @ast::stmt {
    let stmt_ = ast::stmt_semi(expr, cx.next_id());
    @{ node: move stmt_, span: span }
}
fn mk_ty_path(cx: ext_ctxt,
              span: span,
              idents: ~[ ast::ident ])
           -> @ast::Ty {
    let ty = build::mk_raw_path(span, idents);
    let ty = ast::ty_path(ty, cx.next_id());
    let ty = @{ id: cx.next_id(), node: move ty, span: span };
    ty
}
fn mk_simple_ty_path(cx: ext_ctxt,
                     span: span,
                     ident: ast::ident)
                  -> @ast::Ty {
    mk_ty_path(cx, span, ~[ ident ])
}
fn mk_arg(cx: ext_ctxt,
          span: span,
          ident: ast::ident,
          ty: @ast::Ty)
       -> ast::arg {
    let arg_pat = mk_pat_ident(cx, span, ident);
    {
        mode: ast::infer(cx.next_id()),
        ty: ty,
        pat: arg_pat,
        id: cx.next_id()
    }
}
fn mk_fn_decl(+inputs: ~[ast::arg], output: @ast::Ty) -> ast::fn_decl {
    { inputs: move inputs, output: output, cf: ast::return_val }
}
fn mk_ty_param(cx: ext_ctxt,
               ident: ast::ident,
               bounds: @~[ast::ty_param_bound])
            -> ast::ty_param {
    { ident: ident, id: cx.next_id(), bounds: bounds }
}

