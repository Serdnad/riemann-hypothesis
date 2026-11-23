module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isLocalizationAway_of_le {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L}
    [Algebra A B] (hab : ∀ a : A, ((algebraMap A B a : B) : L) = a) (s : A) (hs : (s : L) ≠ 0)
    (hsi : (s : L)⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * (s : L) ^ N ∈ A) : IsLocalization.Away s B := by
  have hu : IsUnit (algebraMap A B s) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(s : L)⁻¹, hsi⟩, Subtype.ext (by simp [hab, hs])⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa using hu.pow n
  · intro z
    obtain ⟨N, hN⟩ := hy z z.2
    exact ⟨(⟨_, hN⟩, ⟨s ^ N, N, rfl⟩), Subtype.ext (by simp [hab])⟩
  · intro a b h
    refine ⟨1, ?_⟩
    have := congrArg (fun z : B => (z : L)) h
    simp only [hab] at this
    simp [Subtype.ext this]

theorem smooth_of_le_away {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L} (hle : A ≤ B)
    (s : L) (hsA : s ∈ A) (hs : s ≠ 0) (hsi : s⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * s ^ N ∈ A)
    [Algebra.Smooth k A] : Algebra.Smooth k B := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨s, hsA⟩ : A) B := isLocalizationAway_of_le (fun _ => rfl) _ hs hsi hy
  haveI : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (⟨s, hsA⟩ : A)
  exact Algebra.Smooth.comp k A B

section Parts

variable {k : Type} [Field k] {F K : Type} [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} {x : Fin (d + 1) → F}

theorem prod_ratio_ne_zero (h : IsPd k x) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.ne j) (h.ne i)

theorem prod_ratio_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩

theorem prod_ratio_inv_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : (∏ j ∈ I, x j / x i)⁻¹ ∈ rA k x I := by
  rw [← Finset.prod_inv_distrib]
  exact Subalgebra.prod_mem _ fun j hj => by
    rw [inv_div]; exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩

theorem rA_singleton_le {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) : rA k x {i} ≤ rA k x I :=
  Algebra.adjoin_mono fun _ ⟨i', hi', j, hy⟩ => ⟨i', by rw [Finset.mem_singleton.1 hi']; exact hi, j, hy⟩

theorem rA_isIntegrallyClosed (h : IsPd k x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsIntegrallyClosed (rA k x I) := by
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h i
  haveI : IsIntegrallyClosed (rA k x {i}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI : Algebra (rA k x {i}) (rA k x I) := (Subalgebra.inclusion (rA_singleton_le hi)).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨_, prod_ratio_mem I i⟩ : rA k x {i}) (rA k x I) :=
    isLocalizationAway_of_le (fun _ => rfl) _ (prod_ratio_ne_zero h I i) (prod_ratio_inv_mem I i)
      fun y hy => (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x h I i hi y).1 hy
  exact isIntegrallyClosed_of_isLocalization (rA k x I) (Submonoid.powers (⟨_, prod_ratio_mem I i⟩ : rA k x {i}))
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => prod_ratio_ne_zero h I i (congrArg Subtype.val h0))

theorem rA_finite (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Module.Finite (rA k x I) (integralClosure (rA k x I) K) := by
  haveI := h.fin
  haveI := h.sep
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  haveI : IsNoetherianRing (rA k x I) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).2
  haveI := rA_isIntegrallyClosed h.pd hi
  set_option synthInstance.maxHeartbeats 200000 in
    exact IsIntegralClosure.finite (rA k x I) F K (integralClosure (rA k x I) K)

theorem rB_frac (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsFractionRing (rB k K x I) K := by
  haveI := h.fin
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  exact integralClosure.isFractionRing_of_finite_extension F K

theorem rB_smooth [CharZero k] (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Algebra.Smooth k (rB k K x I) := by
  have hleB : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)).1 I (Finset.singleton_subset_iff.2 hi)
  have hloc := (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi).2
  have hsB : algebraMap F K (∏ j ∈ I, x j / x i) ∈ rB k K x {i} :=
    (integralClosure (rA k x {i}) K).algebraMap_mem ⟨_, prod_ratio_mem I i⟩
  have hsiB : (algebraMap F K (∏ j ∈ I, x j / x i))⁻¹ ∈ rB k K x I := by
    rw [← map_inv₀]; exact (integralClosure (rA k x I) K).algebraMap_mem ⟨_, prod_ratio_inv_mem I i⟩
  haveI := h.smooth i
  exact smooth_of_le_away hleB _ hsB ((map_ne_zero _).2 (prod_ratio_ne_zero h.pd I i)) hsiB fun y hy => (hloc y).1 hy

end Parts

theorem rB_finite_frac_smooth : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧
      IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  intro k _ _ F K _ _ _ _ _ _ d x h I hI
  obtain ⟨i, hi⟩ := hI
  exact ⟨rA_finite h hi, rB_frac h hi, rB_smooth h hi⟩

end GlobalTheory.PD
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_coordinates_generate_connected_levels : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n, (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧ ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_generate | exact GlobalTheory.PDivGroup.exists_coords_generate | (intros; apply GlobalTheory.PDivGroup.exists_coords_generate <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem quadExt_topology : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE
  obtain ⟨b, -, -⟩ := hE.basis
  haveI hfd : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have htr : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)
  have hN : ∀ z : E, Algebra.norm F z = (2 : F)⁻¹ * Algebra.trace F E (z * c z) := by
    intro z
    rw [← hE.algebraMap_norm z, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hNc : Continuous (Algebra.norm F : E → F) := by
    have : (Algebra.norm F : E → F) = fun z => (2 : F)⁻¹ * Algebra.trace F E (z * c z) := funext hN
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_id.mul hc))
  have hT2 : T2Space E := (GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E).t2
  have hinv : ∀ z : E, z⁻¹ = (Algebra.norm F z)⁻¹ • c z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [Algebra.smul_def, mul_assoc, mul_comm (c z) z, ← hE.algebraMap_norm z, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hI : ContinuousInv₀ E := by
    refine ⟨fun z hz => ?_⟩
    have : (Inv.inv : E → E) = fun z => (Algebra.norm F z)⁻¹ • c z := funext hinv
    rw [this]
    have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
    exact ((continuousAt_inv₀ hn).comp hNc.continuousAt).smul hc.continuousAt
  refine ⟨hfd, inferInstance, hI, hT2, hc, hNc, htr, fun α ν _ _ => ?_⟩
  haveI hM : IsModuleTopology F (Matrix α ν E) := inferInstanceAs (IsModuleTopology F (α → ν → E))
  exact ⟨hM, GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F (Matrix α ν E)⟩

end GlobalTheory
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem GlobalTheory.KSp.parFun_sieg_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχ hres
  obtain ⟨β, hβ, hsymm, -, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨hsc1, hscmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  refine ⟨?_, ?_⟩
  · intro φ
    funext x
    have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
    have h11 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
      ext i j
      by_cases h : i = j <;> simp [toBlocks₁₁, Matrix.one_apply, h]
    have h12 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
      ext i j; simp [toBlocks₁₂, one_apply]
    have hp0 : pr c Q x 0 = 0 := by rw [← hβ]; simp
    simp only [parFun, h1, h11, h12, det_one, hsc1, Matrix.mul_one, Matrix.mul_zero, hp0, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro p hp q hq φ
    funext x
    have hmul : mat c (p * q) = mat c p * mat c q := rfl
    obtain ⟨hq1, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν q hq
    have hP : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hp]; exact (fromBlocks_toBlocks _).symm
    have hQ' : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hq]; exact (fromBlocks_toBlocks _).symm
    set A := (mat c p).toBlocks₁₁
    set B := (mat c p).toBlocks₁₂
    set A' := (mat c q).toBlocks₁₁
    set B' := (mat c q).toBlocks₁₂
    set D' := (mat c q).toBlocks₂₂
    have e11 : (mat c (p * q)).toBlocks₁₁ = A * A' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have e12 : (mat c (p * q)).toBlocks₁₂ = A * B' + B * D' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have hcc : ∀ M : Matrix ν ν E, (M.map c).map c = M := fun M => by ext; simp [hE.invol]
    have hDA : D' * (A'.map c)ᵀ = 1 := by
      have h := congrArg (fun M : Matrix ν ν E => (M.map c)ᵀ) hq1
      have hm : ∀ M N : Matrix ν ν E, (M * N).map c = M.map c * N.map c := fun M N => by
        ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
      have h1c : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
        rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
      simp only [hm, Matrix.transpose_map, hcc, transpose_mul, transpose_transpose, h1c] at h
      exact h
    have hadd : ∀ u v w : Matrix α ν E, pr c Q u (v + w) = pr c Q u v + pr c Q u w := by
      intro u v w; rw [← hβ, ← hβ, ← hβ, map_add (f := _)]
    have hkey : pr c Q (x * A * A') (x * B * D') = pr c Q (x * A) (x * B) := by
      rw [← hβ, ← hβ, hadj, Matrix.mul_assoc (x * B), hDA, Matrix.mul_one]
    simp only [parFun, e11, e12, det_mul, hscmul, Matrix.mul_add, ← Matrix.mul_assoc, hadd, hkey, mul_add,
      AddChar.map_add_eq_mul]
    ring
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem finite_det_line_zero {F E : Type} [Field F] [Field E] [Algebra F E] {ν : Type} [Fintype ν] [DecidableEq ν]
    (A B : Matrix ν ν E) (r₀ : F) (h : (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by
  set M : Matrix ν ν (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C with hM
  have hev : ∀ x : E, M.det.eval x = (A + x • B).det := by
    intro x
    have h1 := RingHom.map_det (Polynomial.evalRingHom x) M
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    rw [← hev, h0, Polynomial.eval_zero]
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  refine (hfin.preimage (f := algebraMap F E) (algebraMap F E).injective.injOn).subset ?_
  intro r hr
  change M.det.eval _ = 0
  rw [hev]
  exact hr

theorem exists_herm_transversal (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))) :
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ∀ g ∈ s, ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by ext i j; simp, by simp⟩
  | insert g s _ ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih
    obtain ⟨t₁, ht₁, h₁⟩ := GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible F E c δ hE ν g
    have key : ∀ k ∈ insert g s, {r : F | (((mat c k).toBlocks₂₁ + (mat c k).toBlocks₂₂ * t₀) +
        algebraMap F E r • ((mat c k).toBlocks₂₂ * (t₁ - t₀))).det = 0}.Finite := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · refine finite_det_line_zero _ _ 1 ?_
        rw [map_one, one_smul, add_assoc, ← Matrix.mul_add, add_sub_cancel]
        exact h₁
      · refine finite_det_line_zero _ _ 0 ?_
        rw [map_zero, zero_smul, add_zero]
        exact h₀ k hk
    have hfin := Set.Finite.biUnion (insert g s).finite_toSet key
    obtain ⟨r, hr⟩ := hfin.exists_notMem
    refine ⟨t₀ + algebraMap F E r • (t₁ - t₀), ?_, ?_⟩
    · ext i j
      have e₀ : c (t₀ j i) = t₀ i j := congrFun (congrFun ht₀ i) j
      have e₁ : c (t₁ j i) = t₁ i j := congrFun (congrFun ht₁ i) j
      simp [e₀, e₁]
    · intro k hk h0
      apply hr
      refine Set.mem_biUnion (Finset.mem_coe.mpr hk) ?_
      rw [Matrix.mul_add, Matrix.mul_smul, ← add_assoc] at h0
      exact h0

theorem exists_translate_inCell : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))),
    ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  intro F _ _ E _ _ c δ hE ν _ _ s
  obtain ⟨t, ht, h⟩ := exists_herm_transversal F E c δ hE ν s
  let u : UG c (stdJ ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_UG_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, ht]⟩
  refine ⟨u, fun g hg => (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one]
  exact h g hg

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Planch

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

theorem e_zero {e : X → X → ℂ} (he : IsPair e) (y : X) : e 0 y = 1 := by
  have h := he.add 0 0 y
  rw [add_zero] at h
  have hn : e 0 y ≠ 0 := by
    intro h0
    have := he.norm 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm)

theorem conj_e {e : X → X → ℂ} (he : IsPair e) (x y : X) : starRingEnd ℂ (e x y) = e (-x) y := by
  have hn : e x y ≠ 0 := by
    intro h0
    have := he.norm x y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h1 : e (-x) y * e x y = 1 := by rw [← he.add, neg_add_cancel, e_zero he]
  have h2 : starRingEnd ℂ (e x y) * e x y = 1 := by
    rw [Complex.conj_mul', he.norm]; simp
  exact mul_right_cancel₀ hn (h2.trans h1.symm)

theorem integral_four_mul (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (hG : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) (C : ℝ) (_hC : 0 < C)
    (hinv : ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) (φ : X → ℂ) (hφ : φ ∈ SB X) :
    ∫ x, four μ e φ x * starRingEnd ℂ (four μ e φ x) ∂μ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  set Φ := four μ e φ with hΦdef
  have hΦ : Φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hec : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hec.mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨x, y⟩ hxy
      simp only [Set.mem_prod, not_and_or] at hxy
      rcases hxy with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
  have hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y) := by
    intro y
    have h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x) := by
      intro x
      rw [map_mul, Planch.conj_e he, neg_neg, he.symm]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := hinv φ hφ (-y)
    rw [neg_neg] at h2
    change starRingEnd ℂ (four μ e Φ (-y)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ
      = ∫ x, ∫ y, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext x
        rw [integral_mul_const]
        rfl
    _ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext x; ring
    _ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext y; ring

theorem lintegral_four_sq : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro X _ _ _ _ hG μ _ e he C hC hinv φ hφ
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hΦ : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_four_mul X hG μ e he C hC hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]

end GlobalTheory.KSp.Planch

end
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  first | exact @GlobalTheory.PDivLat.latt_const_equiv | exact GlobalTheory.PDivLat.latt_const_equiv | (intros; apply GlobalTheory.PDivLat.latt_const_equiv <;> assumption)
end
