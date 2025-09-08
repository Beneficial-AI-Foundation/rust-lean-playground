// Lean compiler output
// Module: Verify.Proofs.reduce
// Imports: Init Aeneas Verify.Src.RustLeanPlayground Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_U64__shiftRight__le___cert__def__1__1;
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__7;
static lean_object* l_p___closed__2;
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_sum___at_Finset_equivBitIndices___elambda__1___spec__1(lean_object*, lean_object*);
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__5;
lean_object* l___private_Init_GetElem_0__List_get_x3fInternal___rarg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__3;
LEAN_EXPORT lean_object* l_U64__shiftRight__le___expr__def__1__1;
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__1;
uint8_t l_Std_Tactic_BVDecide_Reflect_verifyBVExpr(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat(lean_object*);
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__6;
LEAN_EXPORT lean_object* l_p;
static uint8_t l_U64__shiftRight__le___reflection__def__1__1___closed__1;
static lean_object* l_p___closed__1;
static lean_object* l_ArrayU645__to__Nat___closed__1;
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__2;
static lean_object* l_U64__shiftRight__le___cert__def__1__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__4;
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__8;
static lean_object* l_U64__shiftRight__le___expr__def__1__1___closed__9;
lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_U64__shiftRight__le___reflection__def__1__1;
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(51u);
x_4 = lean_nat_mul(x_3, x_2);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_pow(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Init_GetElem_0__List_get_x3fInternal___rarg(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_outOfBounds___rarg(x_8);
x_10 = lean_nat_mul(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_nat_mul(x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
return x_12;
}
}
}
static lean_object* _init_l_ArrayU645__to__Nat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_List_range(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_ArrayU645__to__Nat___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_ArrayU645__to__Nat___closed__1;
x_4 = l_Finset_sum___at_Finset_equivBitIndices___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ArrayU645__to__Nat___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ArrayU645__to__Nat___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_p___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("57896044618658097711785492504343953926634992332820282019728792003956564819968");
return x_1;
}
}
static lean_object* _init_l_p___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_p___closed__1;
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_p() {
_start:
{
lean_object* x_1; 
x_1 = l_p___closed__2;
return x_1;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_unsigned_to_nat(8191u);
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_U64__shiftRight__le___expr__def__1__1___closed__1;
x_3 = l_Std_Tactic_BVDecide_BVExpr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = l_U64__shiftRight__le___expr__def__1__1___closed__3;
x_3 = l_Std_Tactic_BVDecide_BVExpr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_Tactic_BVDecide_BVExpr_var___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_U64__shiftRight__le___expr__def__1__1___closed__5;
x_5 = l_Std_Tactic_BVDecide_BVExpr_extract___override(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(64u);
x_4 = l_U64__shiftRight__le___expr__def__1__1___closed__4;
x_5 = l_U64__shiftRight__le___expr__def__1__1___closed__6;
x_6 = l_Std_Tactic_BVDecide_BVExpr_append___override(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_6;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_U64__shiftRight__le___expr__def__1__1___closed__2;
x_3 = 1;
x_4 = l_U64__shiftRight__le___expr__def__1__1___closed__7;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_U64__shiftRight__le___expr__def__1__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_U64__shiftRight__le___expr__def__1__1() {
_start:
{
lean_object* x_1; 
x_1 = l_U64__shiftRight__le___expr__def__1__1___closed__9;
return x_1;
}
}
static lean_object* _init_l_U64__shiftRight__le___cert__def__1__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("3 0 1 2 0\n", 10, 10);
return x_1;
}
}
static lean_object* _init_l_U64__shiftRight__le___cert__def__1__1() {
_start:
{
lean_object* x_1; 
x_1 = l_U64__shiftRight__le___cert__def__1__1___closed__1;
return x_1;
}
}
static uint8_t _init_l_U64__shiftRight__le___reflection__def__1__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_U64__shiftRight__le___expr__def__1__1;
x_2 = l_U64__shiftRight__le___cert__def__1__1;
x_3 = l_Std_Tactic_BVDecide_Reflect_verifyBVExpr(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_U64__shiftRight__le___reflection__def__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_U64__shiftRight__le___reflection__def__1__1___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Aeneas(uint8_t builtin, lean_object*);
lean_object* initialize_Verify_Src_RustLeanPlayground(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Verify_Proofs_reduce(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Aeneas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Verify_Src_RustLeanPlayground(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ArrayU645__to__Nat___closed__1 = _init_l_ArrayU645__to__Nat___closed__1();
lean_mark_persistent(l_ArrayU645__to__Nat___closed__1);
l_p___closed__1 = _init_l_p___closed__1();
lean_mark_persistent(l_p___closed__1);
l_p___closed__2 = _init_l_p___closed__2();
lean_mark_persistent(l_p___closed__2);
l_p = _init_l_p();
lean_mark_persistent(l_p);
l_U64__shiftRight__le___expr__def__1__1___closed__1 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__1();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__1);
l_U64__shiftRight__le___expr__def__1__1___closed__2 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__2();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__2);
l_U64__shiftRight__le___expr__def__1__1___closed__3 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__3();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__3);
l_U64__shiftRight__le___expr__def__1__1___closed__4 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__4();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__4);
l_U64__shiftRight__le___expr__def__1__1___closed__5 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__5();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__5);
l_U64__shiftRight__le___expr__def__1__1___closed__6 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__6();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__6);
l_U64__shiftRight__le___expr__def__1__1___closed__7 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__7();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__7);
l_U64__shiftRight__le___expr__def__1__1___closed__8 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__8();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__8);
l_U64__shiftRight__le___expr__def__1__1___closed__9 = _init_l_U64__shiftRight__le___expr__def__1__1___closed__9();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1___closed__9);
l_U64__shiftRight__le___expr__def__1__1 = _init_l_U64__shiftRight__le___expr__def__1__1();
lean_mark_persistent(l_U64__shiftRight__le___expr__def__1__1);
l_U64__shiftRight__le___cert__def__1__1___closed__1 = _init_l_U64__shiftRight__le___cert__def__1__1___closed__1();
lean_mark_persistent(l_U64__shiftRight__le___cert__def__1__1___closed__1);
l_U64__shiftRight__le___cert__def__1__1 = _init_l_U64__shiftRight__le___cert__def__1__1();
lean_mark_persistent(l_U64__shiftRight__le___cert__def__1__1);
l_U64__shiftRight__le___reflection__def__1__1___closed__1 = _init_l_U64__shiftRight__le___reflection__def__1__1___closed__1();
l_U64__shiftRight__le___reflection__def__1__1 = _init_l_U64__shiftRight__le___reflection__def__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
