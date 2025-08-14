// Lean compiler output
// Module: IndisputableMonolith
// Imports: Init Mathlib.Data.Fintype.Basic Mathlib.Data.Fintype.Card Mathlib.Data.Fin.Basic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head___rarg(lean_object*);
static lean_object* l_IndisputableMonolith_instFintypePattern___closed__3;
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head(lean_object*);
extern lean_object* l_Bool_fintype;
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_toZ__one___boxed(lean_object*);
lean_object* l_Fintype_piFinset___at_Pi_instFintype___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi___rarg(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_toZ__one(lean_object*);
static lean_object* l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2;
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi___boxed(lean_object*);
lean_object* l_List_ofFn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_fromZ__one(lean_object*);
static lean_object* l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3;
static lean_object* l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1;
static lean_object* l_IndisputableMonolith_instFintypePattern___closed__1;
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last___boxed(lean_object*);
lean_object* l_List_finRange___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_equiv__delta__one;
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_fromZ__one___boxed(lean_object*);
static lean_object* l_IndisputableMonolith_instFintypePattern___closed__2;
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IndisputableMonolith_Chain_head___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_head___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_Chain_head(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IndisputableMonolith_Chain_last___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_Chain_last___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_Chain_last(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_2);
x_7 = lean_int_sub(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IndisputableMonolith_phi___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_phi___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_phi(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_3 = l_IndisputableMonolith_Chain_last___rarg(x_2);
lean_inc(x_1);
x_4 = l_IndisputableMonolith_phi___rarg(x_1, x_3);
x_5 = l_IndisputableMonolith_Chain_head___rarg(x_2);
x_6 = l_IndisputableMonolith_phi___rarg(x_1, x_5);
x_7 = lean_int_sub(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IndisputableMonolith_chainFlux___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_chainFlux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_chainFlux(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Bool_fintype;
return x_2;
}
}
static lean_object* _init_l_IndisputableMonolith_instFintypePattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_finRange___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IndisputableMonolith_instFintypePattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IndisputableMonolith_instFintypePattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IndisputableMonolith_instFintypePattern___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_IndisputableMonolith_instFintypePattern___closed__1;
x_3 = l_List_ofFn___rarg(x_1, x_2);
x_4 = l_IndisputableMonolith_instFintypePattern___closed__2;
x_5 = l_IndisputableMonolith_instFintypePattern___closed__3;
x_6 = l_Fintype_piFinset___at_Pi_instFintype___spec__1___rarg(x_4, x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_instFintypePattern___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_instFintypePattern___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_fromZ__one(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_fromZ__one___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_LedgerUnits_fromZ__one(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_toZ__one(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IndisputableMonolith_LedgerUnits_toZ__one___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IndisputableMonolith_LedgerUnits_toZ__one(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IndisputableMonolith_LedgerUnits_toZ__one___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IndisputableMonolith_LedgerUnits_fromZ__one___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1;
x_2 = l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one() {
_start:
{
lean_object* x_1; 
x_1 = l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IndisputableMonolith(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IndisputableMonolith_instFintypePattern___closed__1 = _init_l_IndisputableMonolith_instFintypePattern___closed__1();
lean_mark_persistent(l_IndisputableMonolith_instFintypePattern___closed__1);
l_IndisputableMonolith_instFintypePattern___closed__2 = _init_l_IndisputableMonolith_instFintypePattern___closed__2();
lean_mark_persistent(l_IndisputableMonolith_instFintypePattern___closed__2);
l_IndisputableMonolith_instFintypePattern___closed__3 = _init_l_IndisputableMonolith_instFintypePattern___closed__3();
lean_mark_persistent(l_IndisputableMonolith_instFintypePattern___closed__3);
l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1 = _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1();
lean_mark_persistent(l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__1);
l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2 = _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2();
lean_mark_persistent(l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__2);
l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3 = _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3();
lean_mark_persistent(l_IndisputableMonolith_LedgerUnits_equiv__delta__one___closed__3);
l_IndisputableMonolith_LedgerUnits_equiv__delta__one = _init_l_IndisputableMonolith_LedgerUnits_equiv__delta__one();
lean_mark_persistent(l_IndisputableMonolith_LedgerUnits_equiv__delta__one);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
