// Lean compiler output
// Module: IndisputableChain.T7
// Imports: Init Mathlib.Data.Fintype.Basic Mathlib.Data.Fin.Basic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern___lam__0(lean_object*, lean_object*);
extern lean_object* l_Bool_fintype;
lean_object* l_Fin_fintype(lean_object*);
lean_object* l_Pi_instFintype___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Bool_fintype;
x_3 = lean_alloc_closure((void*)(l_IndisputableChain_instFintypePattern___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Fin_fintype(x_1);
x_6 = l_Pi_instFintype___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IndisputableChain_instFintypePattern___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IndisputableChain_instFintypePattern___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IndisputableChain_T7(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
