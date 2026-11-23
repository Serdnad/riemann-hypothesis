module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory


set_option synthInstance.maxHeartbeats 200000 in
theorem integralClosure_projective_rA : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F),
    IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  intro k _ _ F K _ _ _ _ _ _ d x h i
  obtain ⟨hfin, -, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x h {i} (Finset.singleton_nonempty i)
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h.pd i
  haveI : IsRegularRing (rA k x {i}) := IsRegularRing.of_ringEquiv e.toRingEquiv
  haveI : IsNoetherianRing (rA k x {i}) := inferInstance
  haveI : IsDomain (rA k x {i}) := inferInstance
  haveI : IsIntegrallyClosed (rA k x {i}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {i}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI : IsRegularRing (rB k K x {i}) := GlobalTheory.isRegularRing_of_smooth k _
  haveI hB : IsRegularRing (integralClosure (rA k x {i}) K) := ‹IsRegularRing (rB k K x {i})›
  haveI : IsNoetherianRing (integralClosure (rA k x {i}) K) := inferInstance
  haveI : IsDomain (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Algebra.IsIntegral (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : FaithfulSMul (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun y : integralClosure (rA k x {i}) K => (y : K)) hab
    exact Subtype.ext ((algebraMap F K).injective this)
  haveI : Algebra.HasGoingDown (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Module.Flat (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    refine GlobalTheory.flat_of_isRegularRing_of_isRegularRing fun q hq => ?_
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under (rA k x {i})) q]
    · exact le_self_add
    all_goals first | assumption | infer_instance
  haveI : Module.FinitePresentation (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_fou : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ μ _ w φ
  obtain ⟨β, hβ, hsym, -, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI : IsTopologicalAddGroup (Matrix α ν E) := (hM α ν).2.grp
  have hh : ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) (x : Matrix α ν E),
      heisFun c ψ Q w φ x = ψ (β x w.toCols₂ + 2⁻¹ * β w.toCols₁ w.toCols₂) * φ (x + w.toCols₁) := by
    intro w φ x
    show ψ (pr c Q _ _ + 2⁻¹ * pr c Q _ _) * _ = _
    rw [← hβ, ← hβ]
  have hJ : w * stdJ ν E = fromCols (-w.toCols₂) w.toCols₁ := by
    ext i (j | j) <;> simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, fromBlocks, toCols₁, toCols₂]
  funext x
  simp only [fou]
  rw [hh, hJ]
  simp only [four, hh, toCols₁_fromCols, toCols₂_fromCols, ← hβ]
  set x₁ := w.toCols₁
  set y₁ := w.toCols₂
  rw [← integral_add_right_eq_self (μ := μ) (fun y => ψ (β x y) * (ψ (β y x₁ + 2⁻¹ * β (-y₁) x₁) * φ (y + -y₁))) y₁,
    ← integral_const_mul]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add (f := _), map_neg, LinearMap.add_apply, LinearMap.neg_apply, hsym y x₁, hsym y₁ x₁]
  ring

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hn h1 χ _ hχ _ _ μ _ b γ hb hd hG φ hφ
  obtain ⟨hfd, hring, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmod, hgood⟩ := hM α ν
  obtain ⟨β, hβ, hs, hnd, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hsc := (GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ).1
  have hP := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hn h1 β hs hnd
  have hu : IsUnit b.det := isUnit_iff_ne_zero.mpr hd
  have hi : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b hu
  have hi' : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have hbb : ∀ x y : Matrix α ν E, β (x * b) y = β x (y * b) := fun x y => by rw [hadj, hb]
  have hbi : ∀ x y : Matrix α ν E, β (x * b⁻¹) y = β x (y * b⁻¹) := fun x y => by
    have := hbb (x * b⁻¹) (y * b⁻¹)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.mul_one] at this
    exact this.symm
  have hpr : (pr c Q : Matrix α ν E → Matrix α ν E → F) = fun x y => β x y := by
    funext x y; exact (hβ x y).symm
  have hf : Continuous fun y : Matrix α ν E => ψ (2⁻¹ * β y (y * b)) := by
    have h2 : Continuous fun y : Matrix α ν E => (y, y * ((2⁻¹ : F) • b)) :=
      continuous_id.prodMk (continuous_id.matrix_mul continuous_const)
    have := hP.lc.continuous.comp h2
    refine this.congr fun y => ?_
    simp [Matrix.mul_smul]
  have hW := GlobalTheory.T.weil_formula_fourier_quadratic_character (Matrix α ν E) hgood μ _ hP (fun y => ψ (2⁻¹ * β y (y * b)))
    (fun u => ψ (-(2⁻¹ * β (u * b⁻¹) u))) (fun u => u * b⁻¹) γ hf
    (continuous_id.matrix_mul continuous_const) (fun y u => by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have h3 : β (u * b⁻¹) (y * b) = β y u := by
        rw [← hbb, Matrix.mul_assoc, hi, Matrix.mul_one, hs]
      rw [Matrix.add_mul, Matrix.mul_assoc u, hi, Matrix.mul_one]
      simp only [map_add (f := _), LinearMap.add_apply, h3]
      ring) (by simpa only [hpr] using hG) φ hφ
  funext x
  have hL : parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ) =
      fun y => ψ (2⁻¹ * β y (y * b)) * four μ (fun x y => ψ (β x y)) φ y := by
    funext y
    simp [parFun, fou, hsc, hpr]
  rw [hL]
  simp only [Pi.smul_apply, smul_eq_mul, fou, hpr]
  rw [hW x]
  simp only [parFun, four, hpr, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, det_one, hsc, Matrix.mul_one, one_mul]
  rw [mul_left_comm, ← integral_const_mul (ψ _)]
  congr 3
  funext z
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h4 : β (z * b⁻¹) x = β (x * b⁻¹) z := by rw [hbi, hs]
  simp only [Matrix.add_mul, Matrix.mul_neg, map_add (f := _), map_neg, LinearMap.add_apply, LinearMap.neg_apply, h4, ← hbi z z]
  ring

end GlobalTheory.KSp
end

section

noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem mem_of_inCell {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (hP : sieg c ν ≤ U) (hw : weyl c ν ∈ U) {g : UG c (stdJ ν E)} (hg : InCell c g) : g ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  exact U.mul_mem (U.mul_mem (hP hp) hw) (hP hq)

theorem sieg_weyl_generate : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))),
    sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  intro F _ _ E _ _ c δ hE ν _ _ U hP hw
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν {1, g}
  have h1 : u ∈ U := by
    simpa using mem_of_inCell c U hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := mem_of_inCell c U hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)

end GlobalTheory.KSp
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.conductorTimesSplitPrimes_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  first | exact @GlobalTheory.CMVal.CondExp.condQ_exponents | exact GlobalTheory.CMVal.CondExp.condQ_exponents | (intros; apply GlobalTheory.CMVal.CondExp.condQ_exponents <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_element_pos_im_under_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_section_over_ordinary_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isReduced_normalModel_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  first | (exact @GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (exact GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (intros; apply GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem rep_conj_of_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  classical
  intro p _ D g ρ ρ' htr
  obtain ⟨φ, hφ, hspan⟩ := GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings p D
  haveI := D.freeO
  haveI := D.finO
  have hdim : Module.finrank ℂ ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) = Module.finrank ℤ D.O := by
    rw [Module.finrank_pi_fintype, D.rankO]
    simp [Module.finrank_matrix, NumberField.Embeddings.card]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ hspan hdim
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ' hspan hdim
  have key : ∀ (s : ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (f : (D.F →+* ℂ) → ℂ),
      (s (fun τ => Matrix.scalar (Fin D.m) (f τ))).trace = ∑ τ, f τ * (s (Pi.single τ 1)).trace := by
    intro s f
    have : (fun τ => Matrix.scalar (Fin D.m) (f τ)) = ∑ τ, f τ • (Pi.single τ 1 : (D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) := by
      ext τ i j
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single τ]
      · simp [Pi.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp

    rw [this, map_sum, Matrix.trace_sum]
    simp [map_smul, Matrix.trace_smul]
  let χ : (D.F →+* ℂ) → (𝓞 D.F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro τ τ' h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
    ext x
    exact DFunLike.congr_fun h x
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hlin
  have heq : ∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace := by
    have := hlin (fun τ => (σ (Pi.single τ 1)).trace - (σ' (Pi.single τ 1)).trace) (by
      funext c
      have h1 := htr c
      have hφ' : φ (algebraMap (𝓞 D.F) D.O c) = fun τ => Matrix.scalar (Fin D.m) (τ (c : D.F)) := funext (hφ c)
      rw [← hσ, ← hσ', hφ', key, key] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      simp only [χ, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1)
    intro τ
    exact sub_eq_zero.mp (this τ)
  exact GlobalTheory.T.representations_equal_traces_conjugate (D.F →+* ℂ) D.m g D.m_pos σ σ' heq |>.imp fun h hh => ⟨hh.1, fun a => by rw [← hσ, ← hσ']; exact hh.2 _⟩

end GlobalTheory.UPel.HT
end
