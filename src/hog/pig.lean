import tactic 

structure pig : Type :=
 (n m : ℕ)
 
structure roast_pig : Type :=
  (p : pig)
  (roasted : p.n = p.m)
  
class test (p : pig) := (eq : p.n = p.m)

def piki : pig := 
{ n := 3, 
  m := 3 }
  
def jakob : pig :=
{ n := 4,
  m := 3 }
  

def roast_piki : roast_pig :=
{ p := piki,
  roasted := rfl }
  
meta def try_roasting : pig → option roast_pig :=
λ p, if eq : p.n = p.m 
then some { p := p, roasted := eq }
else none

#reduce try_roasting piki
#reduce try_roasting jakob
  