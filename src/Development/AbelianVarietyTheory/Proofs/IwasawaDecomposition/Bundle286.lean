module

public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle273
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle274
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle275
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DualCompletion

open Formalism.L2.G.RelativeIndexFlags

theorem hform_mulVec_left {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (t x : Fin n → A) : hform τ J (B *ᵥ t) x = ∑ a, τ (t a) * ((cT τ B * J) *ᵥ x) a := by

  simp only [hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
  map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem hform_col {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (a : Fin n) (c : A) (x : Fin n → A) :
    hform τ J (B *ᵥ Pi.single a c) x = τ c * ((cT τ B * J) *ᵥ x) a := by
  rw [hform_mulVec_left, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro h; exact (h (Finset.mem_univ a)).elim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J Λ ↔ y ∈ dualSet σ J Λ := by
  apply _root_.GlobalTheory.OverLat.mem_span_dualSet <;> assumption

theorem exists_common_den {p : ℕ} (hp : p.Prime) (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) :
    ∃ s : ℕ, ¬ p ∣ s ∧ ∀ m ∈ M, ∀ a, (s : E) * ((B⁻¹).1 *ᵥ m) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  obtain ⟨S, rfl⟩ := hM
  choose s hs H using fun m : S => (hB m.1).1 ⟨1, h1, by
    rw [Nat.cast_one, one_smul]; exact Submodule.subset_span m.2⟩
  refine ⟨∏ m, s m, fun hd => ?_, fun m hm => ?_⟩
  · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
    exact hs a ha
  · induction hm using Submodule.span_induction with
    | mem y hy =>
      intro a
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ ⟨y, hy⟩), mul_comm (s _), Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (H ⟨y, hy⟩ a)
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [Matrix.mulVec_add, Pi.add_apply, mul_add]; exact add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨c, rfl⟩ (hy a)

theorem isLocBasis_dual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {p : ℕ} (hp : p.Prime)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) (C : GL (Fin n) E) (hC : C.1 = cT (σ : E →+* E) B.1 * J) :
    IsLocBasis p (dualL (σ : E →+* E) J M : Set (Fin n → E)) C⁻¹ := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  intro x
  rw [inv_inv, hC]
  simp only [SetLike.mem_coe, mem_dualL]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht H using fun a : Fin n => (hB (B.1 *ᵥ Pi.single a 1)).2 ⟨1, h1, fun b => by
      rw [Nat.cast_one, one_mul]; exact latB_col B a b⟩
    refine ⟨(∏ a, t a) * s, fun hd => ?_, fun a => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
        exact ht a ha
      · exact hs hd
    · have h := hx _ (H a)
      rw [Formalism.UG.P.csDual_hform_smul_left, hform_col, map_one, one_mul, map_natCast, Matrix.mulVec_smul,
        Pi.smul_apply, smul_eq_mul] at h
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a), mul_comm (t a), Nat.cast_mul, Nat.cast_mul,
        mul_assoc, mul_assoc]
      exact mul_mem (natCast_mem _ _) h
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, H⟩ := exists_common_den hp M hM B hB
    refine ⟨t * s, fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim ht hs, fun m hm => ?_⟩
    have e : m = B.1 *ᵥ ((B⁻¹).1 *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    refine sum_mem fun a _ => ?_
    obtain ⟨b, hb⟩ := H m hm a
    have h2 := sig_int σ b
    rw [hb, map_mul, map_natCast] at h2
    have h3 := mul_mem h2 (hx a)
    convert h3 using 1
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    show σ _ * _ = _
    ring

theorem mem_latS_dualL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : Fin n → E ⊗[F] v.adicCompletion F) :
    w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J M) ↔
      ∀ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) u w ∈ intV E v := by
  classical
  haveI := v.isMaximal
  obtain ⟨p, -, -, hv, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB⟩ := LocB.exists_isLocBasis p E M hM.fg hM.span_eq_top
  have hu : IsUnit (cT (σ : E →+* E) B.1 * J).det := by
    rw [Matrix.det_mul, cT, Matrix.det_transpose]
    refine IsUnit.mul ?_ hJ
    have := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).map (σ : E →+* E)
    rwa [RingHom.map_det] at this
  let C : GL (Fin n) E := Matrix.GeneralLinearGroup.mk'' _ hu
  have hC : C.1 = cT (σ : E →+* E) B.1 * J := rfl
  have hD := isLocBasis_dual σ J hp M hM.fg B hB C hC
  rw [latS_of_locBasis v hp hv _ _ hD, latS_of_locBasis v hp hv _ _ hB, mem_latS_latB, map_inv, inv_inv]
  have hC' : (bc (inclE (F := F) (v.adicCompletion F)) C).1 =
      cT (sigR σ (v.adicCompletion F)) (bc (inclE (F := F) (v.adicCompletion F)) B).1 *
        J.map (inclE (F := F) (v.adicCompletion F)) := by
    show C.1.map (inclE (F := F) (v.adicCompletion F)) =
      cT (sigR σ (v.adicCompletion F)) (B.1.map (inclE (F := F) (v.adicCompletion F))) * _
    rw [hC, Matrix.map_mul]
    congr 1
  rw [hC']
  set B' := bc (inclE (F := F) (v.adicCompletion F)) B with hB'
  constructor
  · intro h u hu
    rw [mem_latS_latB] at hu
    have e : u = B'.1 *ᵥ ((B'⁻¹).1 *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    exact sum_mem fun a _ => mul_mem (sigR_mem v σ (hu a)) (h a)
  · intro h a
    have h1 := h (B'.1 *ᵥ Pi.single a 1) (by
      rw [mem_latS_latB]
      intro b
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases hb : b = a
      · subst hb; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hb]; exact zero_mem _)
    rwa [hform_col, map_one, one_mul] at h1

theorem dual_move (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : IsUnit J.det) (hL : Submodule.IsFullLattice E L)
    (hLb : Submodule.IsFullLattice E Lb) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) :
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  have hyU : cT (sigR σ (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy
  have key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z ((y⁻¹).1 *ᵥ x) =
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (y.1 *ᵥ z) x := by
    intro z x
    have e := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      y.1 z ((y⁻¹).1 *ᵥ x)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e
    exact e.symm
  intro x
  rw [mem_latS_dualL σ J hJ v L hL, mem_latS_dualL σ J hJ v Lb hLb]
  refine ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · rw [key]
    refine H _ ((hyl _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hz
  · have h1 := H _ ((hyl z).1 hz)
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1

end GlobalTheory.DualCompletion

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.kernel_vector_sum_of_isotypic_pieces : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  first | exact @GlobalTheory.decomp_kernels_isotIn | exact GlobalTheory.decomp_kernels_isotIn | (intros; apply GlobalTheory.decomp_kernels_isotIn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.smooth_admissible_unitary_mem_sup_isotypic_parts : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x})) → (∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x) → ∀ x ∈ C, x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π := by
  first | exact @GlobalTheory.SpanIsot.span_isotIn | exact GlobalTheory.SpanIsot.span_isotIn | (intros; apply GlobalTheory.SpanIsot.span_isotIn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.lift_law_implies_adelic_extension_base_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | exact GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | (intros; apply GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.mem_level_group_face_level_iff_flag_group : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  first | exact @GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | exact GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | (intros; apply GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.unitary_congruence_conj_contains_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  first | exact @GlobalTheory.CongConjugate.congConj | exact GlobalTheory.CongConjugate.congConj | (intros; apply GlobalTheory.CongConjugate.congConj <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef

variable {D : D7} {S T : HSp D} {r g : ℕ}

def IsSet (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hr : T.rank = r) (X : Data D.host.E r)
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ S.gram = 1 ∧ Even S.rank ∧ ModelW T hr X ∧ X.κ0 = -(2 * D.host.xi0) ∧
    (∀ ρ, (eT ρ).1 = tauE D ρ) ∧ IsSympl X bas

abbrev Fam (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

def negM (T : HSp D) (q : ℕ) : Matrix (Fin T.rank) (Fin T.rank) ℂ :=
  Matrix.diagonal fun a : Fin T.rank => ((-(sgn q (a : ℕ)) : ℝ) : ℂ)

def IsONeg (T : HSp D) (q : ℕ) (Z : Fam T) : Prop := ∀ ρ, (Z ρ)ᴴ * gramAt D T ρ * Z ρ = negM T q

def cartZ (T : HSp D) (q : ℕ) (Z : Fam T) : Fam T := fun ρ => Z ρ * negM T q * (Z ρ)⁻¹

def mvZ (θ : InfFam D) (h : GA D T) (Z : Fam T) : Fam T := fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * Z ρ

def frOf (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (Z : Fam T) : Frame X.Ψ r :=
  fun τ a b => Z (eT.symm τ) (Fin.cast hr.symm a) (Fin.cast hr.symm b)

def rePt (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (w : WO S T) :
    Ker.WR X S.rank :=
  fun τ k a => compAt θ (eT.symm τ) w (Fin.cast hr.symm a) k

def Zak (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r}
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (φ : TF S.rank g) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w, Ker.IsRealPt w → f w = Ker.thR X bas idx φ x (rePt θ hr eT w)

def finR (S : HSp D) (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) : WO S T :=
  Ker.finW S T (y.submatrix id (Fin.cast hr))

def latW (hr : T.rank = r) (L : Lt D.host.E r) : Lt D.host.E T.rank :=
  L.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr.symm))

def toP (S : HSp D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ X.Ψ q0 X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (eT v.1, (rowIdx hq).symm (Fin.cast hr v.2.1), v.2.2)

def fv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (q : ℕ) (Z : Fam T) (f : WO S T → ℂ)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (fun _ => 1) (cartZ T q Z) (fun _ => 1) Z f Q

def ctxOf {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hn : Even S.rank)
    (X' : Data D.host.E T.rank) (m : Ker.Match S T X') {q : ℕ} (hq : X'.p0 + q = T.rank)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') : Ker.Ctx S T :=
  ⟨ψ, hψ, θ, hθ, X', m, g, q, hq, bas', idx', hs, hn⟩

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def MarkAd (hr : T.rank = r) (l : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (h : GA D T)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T h,
    finVec T (mk a ∘ Fin.cast hr) - (finHom T h).1.mulVec (finVec T (ι a)) = (l.M : ℕ) • w

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Matched (c : Coeff l) (σ : c.F →+* ℂ) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

abbrev ptC (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) : @FrPt D.host.E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra :=
  unC (Formalism.L2.PjFree.Unf.ofPj U) k x

def FrConst (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f₀ : WO S T → ℂ) (U : Unf Xo c σ r)
    (dict : GA D T → Σ k, Frame (U.X k).Ψ r) (mu : GA D T → ℂ) (Z₀ : Fam T) (cc : U.Comp → ℂ) : Prop :=
  ∀ (h γ : GA D T), γ ∈ GQ T → ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw),
    IsSet ψ θ S T hr (U.X (dict h).1) eT bas → Matched c σ (U.X (dict h).1) idx e →
    (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom),
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩))
      (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U (dict h).1 ⟨(dict h).2, hx⟩).s th →
      ∀ w : WO S T, Ker.IsRealPt w →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          (Ker.gaussR (U.X (dict h).1) bas idx (dict h).2 (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w)) *
            ∏ b, th (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w) b))

section Field

variable {c' : Coeff l} {hle : c.F ≤ c'.F} [Algebra c.F ℂ] [Algebra c'.F ℂ] (hA : AlgOver c c' hle ℂ) {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt D.host.E r} {y : FrPt Xo c ℂ}

def fibExt (A : AnFib X bas idx e x L y) : AnFib X bas idx e x L (y.ext hle hA) :=
  ⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm,
    A.fr_per⟩

end Field

end Geo

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseZ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Fam (Wc D i) := x0Mat (R.MW i (sg0 D A))

end Rec

end GlobalTheory.OneMapRef

end
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensor_types_intertwiner_matrix_polynomials : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  first | exact @GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | exact GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | (intros; apply GlobalTheory.CompactHoweJoint.exists_joint_intertwiner <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_unitary_mul_integral_at_split_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  first | exact @GlobalTheory.UnIntApprox.exists_unitary_mul_integral | exact GlobalTheory.UnIntApprox.exists_unitary_mul_integral | (intros; apply GlobalTheory.UnIntApprox.exists_unitary_mul_integral <;> assumption)
end
