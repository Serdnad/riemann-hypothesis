module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle008
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle002
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def adjSg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem adjSg_mul_self (ε : Fin n → Bool) (c : Fin n) : adjSg ε c * adjSg ε c = 1 := by
  unfold adjSg; split_ifs <;> norm_num

theorem adjSg_conj (ε : Fin n → Bool) (c : Fin n) : (starRingEnd ℂ) (adjSg ε c) = adjSg ε c := by
  unfold adjSg; split_ifs <;> simp

theorem adjSign_eq_adjSg (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSg ε a * adjSg ε b := by
  unfold adjSign adjSg
  cases ε a <;> cases ε b <;> norm_num

section R

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def adjR (ε : Fin n → Bool) (M : Submodule ℂ X) (ps : (Fin n → X) →ₗ[ℂ] X) (x : X) (u : Fin n → X) : Prop :=
  u ∈ tensSub M ∧ ∀ c, ∀ y ∈ M, inner ℂ (u c) y = adjSg ε c * inner ℂ x (ps (Pi.single c y))

variable {ε : Fin n → Bool} {M : Submodule ℂ X} {ps : (Fin n → X) →ₗ[ℂ] X}

theorem adjR_inv {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (c : Fin n) {y : X} (hy : y ∈ M) :
    inner ℂ x (ps (Pi.single c y)) = adjSg ε c * inner ℂ (u c) y := by
  rw [h.2 c y hy, ← mul_assoc, adjSg_mul_self, one_mul]

theorem adjR_unique {x : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x u') : u = u' := by
  funext c
  have hm : u c - u' c ∈ M := M.sub_mem (tset_mem.1 h.1 c) (tset_mem.1 h'.1 c)
  have h0 : inner ℂ (u c - u' c) (u c - u' c) = (0 : ℂ) := by
    rw [inner_sub_left, h.2 c _ hm, h'.2 c _ hm, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem adjR_add {x x' : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x' u') :
    adjR ε M ps (x + x') (u + u') := by
  refine ⟨(tensSub M).add_mem h.1 h'.1, fun c y hy => ?_⟩
  rw [Pi.add_apply, inner_add_left, inner_add_left, h.2 c y hy, h'.2 c y hy, mul_add]

theorem adjR_smul {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (r : ℂ) : adjR ε M ps (r • x) (r • u) := by
  refine ⟨(tensSub M).smul_mem r h.1, fun c y hy => ?_⟩
  rw [Pi.smul_apply, inner_smul_left, inner_smul_left, h.2 c y hy]
  ring

theorem adjR_linear {M' : Submodule ℂ X} (hex : ∀ x ∈ M', ∃ u, adjR ε M ps x u) :
    ∃ ι : X →ₗ[ℂ] (Fin n → X), ∀ x ∈ M', adjR ε M ps x (ι x) := by
  apply ReciprocityTheory.ChartRestriction.DS.adjR_linear <;> assumption

end R

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_tensF_mem (dual : Bool) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {u : Fin n → D} (hu : u ∈ tensSub M) (a b : Fin n) : tensF dual E a b u ∈ tensSub M := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_tensF_mem <;> assumption

theorem adjB_E (dual : Bool) (hU : IsInfUnitary ε E) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {ps : (Fin n → D) →ₗ[ℂ] D} (hps2 : ∀ a b, ∀ f ∈ tensSub M, ps (tensF dual E a b f) = E a b (ps f))
    {x : D} {u : Fin n → D} (h : adjR ε M ps x u) (a b : Fin n) :
    adjR ε M ps (E a b x) (tensF dual E a b u) := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_E <;> assumption

theorem adjB_block {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {c d : Fin n} (h : ε c ≠ ε d) :
    k c d = 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_block <;> assumption

theorem adjB_sgn {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (dual : Bool) (c d : Fin n) :
    (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε c * adjSg ε d) =
      (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) := by
  by_cases h : ε c = ε d
  · rw [show adjSg ε c * adjSg ε d = 1 by unfold adjSg; rw [h]; split_ifs <;> norm_num, mul_one]
  · rw [adjB_block hk h]
    cases dual <;> simp

theorem adjB_star_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_star_Kset <;> assumption

theorem adjB_inner (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v w : H) :
    inner ℂ (σ k v) w = inner ℂ v (σ kᴴ w) := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_inner <;> assumption

end Amb

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Mat

variable {ε : Fin n → Bool}

theorem J_mul_J_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem unitary_group_inv_eq_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g⁻¹ = Jm ε * gᴴ * Jm ε := by
  apply Matrix.inv_eq_left_inv
  unfold inUJ at hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, J_mul_J_eq_one]

theorem J_conj_entry (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (d c : Fin n) :
    (Jm ε * A * Jm ε) d c = (if ε d then 1 else -1) * A d c * (if ε c then 1 else -1) := by
  simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem J_conj_neg_mul_inv {g X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * (g * X)ᴴ * Jm ε = -(X * (Jm ε * gᴴ * Jm ε)) := by
  apply ReciprocityTheory.ChartRestriction.DS.J_conj_neg_mul_inv <;> assumption

theorem hasDerivAt_exp_curve_entry (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) c d) ((g * X) c d) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h c) d

theorem hasDerivAt_inv_exp_curve_entry {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (d c : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X))⁻¹ d c) (-(X * g⁻¹) d c) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inv_exp_curve_entry <;> assumption

end Mat

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem hasDerivAt_inner_rep_exp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (w : H) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ w (σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ w (σ g ((actM E X v : D) : H))) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inner_rep_exp <;> assumption

def oa1Phi (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual ((g⁻¹) d c) (g c d)

def oa1DPhi (dual : Bool) (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ :=
  cond dual ((-(X * g⁻¹)) d c) ((g * X) c d)

theorem hasDerivAt_tensor_phi {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool)
    (c d : Fin n) :
    HasDerivAt (fun t : ℝ => oa1Phi dual (g * NormedSpace.exp ((t : ℂ) • X)) c d) (oa1DPhi dual g X c d) 0 := by
  cases dual
  · exact hasDerivAt_exp_curve_entry g X c d
  · exact hasDerivAt_inv_exp_curve_entry hg hX d c

theorem tensor_coef_expand (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g f c) = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
  simp only [tensGrp, oa1Phi, inner_sum, inner_smul_right]

theorem hasDerivAt_tensor_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool) (η : Fin n → H)
    (f : Fin n → D) :
    HasDerivAt (fun t : ℝ => ∑ c, inner ℂ (η c)
        (tensGrp dual σ (g * NormedSpace.exp ((t : ℂ) • X)) (fun d => (f d : H)) c))
      (∑ c, ∑ d, (oa1DPhi dual g X c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E X (f d) : D) : H)))) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_tensor_coef <;> assumption

end Coef

section Eab

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tensor_dphi_complex_comb (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    oa1DPhi dual g (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) c d +
        Complex.I * oa1DPhi dual g (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) c d =
      cond dual (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) := by
  apply ReciprocityTheory.ChartRestriction.DS.tensor_dphi_complex_comb <;> assumption

theorem tensor_coef_Eab_action (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ c, inner ℂ (η c) (tensGrp dual σ x (fun d => (f d : H)) c)) g =
      ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (tensF dual E a b f d : H)) c) := by
  apply ReciprocityTheory.ChartRestriction.DS.tensor_coef_Eab_action <;> assumption

end Eab

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
