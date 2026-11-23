module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.prB_of :
    GoodZ → PrB := by
  intro hG F K _ _ _ _ _ _ d x h τ hτ ρ hρ a q had hqd e he y hy
  have mono : ∀ r : ℕ, ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) r ≤ omB ℂ K (rB ℂ K (xv x) t) r :=
    fun r => (hG F K d x h r).2.2
  have hvan : ∀ i, (Finset.univ.erase i).Nonempty →
      ∀ u ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) (d - a),
      ∀ v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a,
      (LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ) u v = 0 := by
    intro i hi u hu v hv
    have hvq : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
    have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) h τ hτ (Finset.univ.erase i) hi (d - a) a
      (by omega) v hvq).2 hv u hu
    exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) h.pd ρ hρ i _ hi (Finset.notMem_erase i _) _ hmem
  obtain ⟨ε, hε⟩ := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a))
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))
    (mono _) (mono _) hvan ((d : ℤ) - (q : ℕ))
  obtain ⟨y', hy', rfl⟩ := hy
  have key := hε e he.1 y' (by
    have e1 : (d : ℤ) - ((d : ℤ) - (q : ℕ)) - 1 = (q : ℤ) - 1 := by ring
    rw [e1]
    exact hy')
  have h0 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a)).D e = 0 := he.2
  rw [h0, map_zero, LinearMap.zero_apply] at key
  exact (smul_eq_zero_iff_eq ε).1 key.symm
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem ext_comm_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (v : M) (q : ℕ)
    (w : ExteriorAlgebra R M) (hw : w ∈ ⋀[R]^q M) :
    ExteriorAlgebra.ι R v * w = ((-1 : ℤ) ^ q) • (w * ExteriorAlgebra.ι R v) := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [mul_add, add_mul, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    have h := ExteriorAlgebra.ι_add_mul_swap (R := R) v u
    have h' : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
      eq_neg_of_add_eq_zero_left h
    rw [← mul_assoc, h', neg_mul, mul_assoc, hx, mul_smul_comm]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, mul_assoc]

private theorem ext_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (p q : ℕ)
    (y w : ExteriorAlgebra R M) (hy : y ∈ ⋀[R]^p M) (hw : w ∈ ⋀[R]^q M) :
    y * w = ((-1 : ℤ) ^ (p * q)) • (w * y) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, ext_comm_one u q w hw, smul_mul_assoc, smul_smul,
      mul_assoc, Nat.succ_mul, pow_add]

theorem UpperTheory.Gal.productCup_of_system.idJ_of :
    LatOm → LatA → DualForm → IdJ := by
  intro hOm hA hD F K _ _ _ _ _ _ d x hc τ hτ a ha j
  obtain ⟨⟨_, n, v, φ, hv, hφ, hdec⟩, hsp⟩ := hOm F K d x hc a {j} (by simp)
  have hdec' : ∀ z ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) {j}) a : Set (DR ℂ K)), z = ∑ k, φ k z • v k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hdec z hz
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
      rw [← hp, ← hq]
    | smul c p _ hp =>
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hp]
  have hG : omG x j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x j).ne_zero
  choose w hwm hwt using fun k => (hD F K d x hc τ hτ a ha (omG x j • φ k)).2
  have hwB : ∀ k, w k ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a) := by
    intro k
    refine (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ {j} (by simp) a (d - a) (by omega) (w k) (hwm k)).1 ?_
    intro y hy
    have hy' : y ∈ ⋀[K]^a Ω[K⁄ℂ] := GlobalTheory.PD.mem_deg_of_mem_omB _ _ _ hy
    rw [ext_comm a (d - a) y (w k) hy' (hwm k), map_zsmul, map_zsmul]
    refine zsmul_mem ?_ _
    rw [← hwt k y hy']
    refine ((hA F d x hc.pd {j} j (by simp)).2.1 _).2 ?_
    simpa [hG] using hφ k y hy
  refine ⟨∑ k, w k ⊗ₜ[ℂ] v k, ?_, ?_⟩
  · show _ ∈ MZ F K (xv x) a {j} {j}
    exact Submodule.sum_mem _ fun k _ => Submodule.apply_mem_map₂ _ (hwB k) (hv k)
  · intro y hy
    conv_rhs => rw [hdec' y (hsp y hy)]

    simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : muP F K τ (w k ⊗ₜ[ℂ] v k) y = (Algebra.trace F K (τ (w k * y))) ⊗ₜ[ℂ] v k := by
      simp [muP]
    rw [this, ← hwt k y hy]
    simp [mulP]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one :
    ResidueOfTraceIsFiberSum := by
  intro F L _ _ _ _ _ _ d x hc hred ρ hρ h
  obtain ⟨⟨τ, hτ⟩, -⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F L d (xv x) hc
  have hloc : locCoch ℂ L (xv x) (h : L) Finset.univ = (h : L) • vol0 ℂ L (xv x) := if_pos rfl
  have h1 : trF ℂ τ ρ (locCoch ℂ L (xv x) (h : L) Finset.univ) = ρ (Algebra.trace F L (h : L)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← h1]
  exact GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre ℂ F L d (xv x) hc τ hτ ρ hρ inferInstance hred h
end
