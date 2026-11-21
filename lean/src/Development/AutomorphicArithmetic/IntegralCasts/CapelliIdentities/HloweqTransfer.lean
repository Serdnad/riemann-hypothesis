import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplexNormedInstanceCompat

/-! The two discrete-series constructions use the same signature unitary group,
regular representation and lowest-weight transfer theorem. -/

namespace UpperTheory.Reformulated.B.Re4

open UpperTheory.Reformulated.B

alias Jm := Re3.Jm
def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  g.conjTranspose * Jm ε * g = Jm ε

attribute [backward_defeq] inUJ.eq_1

alias aux3 := Re3.aux3
alias aux4 := Re3.aux4
alias aux5 := Re3.aux5
alias UJ := Re3.UJ
@[reducible] alias instMeasurableSpaceUJ := Re3.instMeasurableSpaceUJ
alias aux8 := Re3.aux8
alias aux9 := Re3.aux9
alias laurent_T_neg_one_mul_T_one := Re3.laurent_T_neg_one_mul_T_one
alias muG := Re3.muG
alias algebra_smulCommClass_complex := Re3.algebra_smulCommClass_complex
@[reducible] alias L2 := Re3.L2
alias d15 := Re3.d15
alias Kset := Re3.Kset
alias complex_normed_instance_compat := Re3.complex_normed_instance_compat
@[reducible] alias umat := Re3.umat
alias rregG := Re3.rregG
alias rreg := Re3.rreg
alias d21 := Re3.d21
alias IsKStableOn := Re3.IsKStableOn
alias IsWtOn := Re3.IsWtOn
alias root := Re3.root
alias CDom := Re3.CDom
alias IsKTypeOf := Re3.IsKTypeOf
alias hloweq_transfer := Re3.hloweq_transfer

end UpperTheory.Reformulated.B.Re4
