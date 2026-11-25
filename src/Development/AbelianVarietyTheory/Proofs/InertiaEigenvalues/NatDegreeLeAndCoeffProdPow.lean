module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IntegralStatementPfA

@[expose] public section

universe u_1 u_2

namespace GlobalTheory.ProductDegreeCoefficient

open Polynomial

theorem natDegree_le_and_coeff_prod_pow {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.prod_pow_natDegree_coeff' <;> assumption

end GlobalTheory.ProductDegreeCoefficient
