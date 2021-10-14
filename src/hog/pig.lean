import tactic
open tactic
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident)

structure pig : Type :=
 (n m : ℕ)
 
structure pork : Type :=
  (p : pig)
  (roasted : p.n = p.m)
  
class test (p : pig) := (eq : p.n = p.m) 

def piki : pig := 
{ n := 3, 
  m := 3 }
  
def jakob : pig :=
{ n := 4,
  m := 3 }

def roast_piki : pork :=
{ p := piki,
  roasted := rfl }
  
#reduce has_to_pexpr pig

meta def tactic.interactive.diag_tactic (e : parse texpr) : tactic unit :=
do { t ← target, 
     p ← i_to_expr_strict ``((%%e, %%e) : %%t), 
     exact p
   }

def foo (i : ℕ) : ℕ × ℕ :=
begin
  diag_tactic (i + 3)
end

meta def tactic.interactive.roast (e : parse texpr) : tactic unit :=
do { r ← i_to_expr_strict ``(pork.mk %%e (eq.refl (%%e).n)),
     exact r
   }

meta def tactic.interactive.sautee (e : parse texpr) : tactic unit :=
do { r ← i_to_expr_strict ``(pork.mk %%e (eq.refl (%%e).n)),
     exact r
   }

meta def tactic.interactive.braise (e : parse texpr) : tactic unit :=
do { t ← to_expr ``((%%e).n = (%%e).m),
     (_, p) ← solve_aux t (tactic.reflexivity),
     r ← i_to_expr_strict ``(pork.mk %%e %%p),
     exact r
   }

def peceni_piki : pork := by roast piki
def pohani_piki : pork := by braise piki

-- def peceni_jakob : pork := by roast jakob
