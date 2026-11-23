module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso


open scoped MatrixOrder ComplexOrder in
theorem exists_hermitian_sqrt_mul_mul_eq {n : ℕ} (J C : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = 1) (hJh : Jᴴ = J) (hC : C.det ≠ 0)
    (h : (Cᴴ * C) * J * (Cᴴ * C) = J) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ, IsUnit s.det ∧ sᴴ = s ∧ s * s = Cᴴ * C ∧ s * J * s = J :=
  by
  letI : PartialOrder ℂ := RCLike.toPartialOrder
  letI : PartialOrder (Matrix (Fin n) (Fin n) ℂ) := Matrix.instPartialOrder
  letI : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  letI : StarOrderedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instNonnegSpectrumClass
  set H := Cᴴ * C with hHdef
  have hH : 0 ≤ H := (Matrix.posSemidef_conjTranspose_mul_self C).nonneg
  set s := CFC.sqrt H with hsdef
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg H
  have hss : s * s = H := CFC.sqrt_mul_sqrt_self H hH
  have hsh : sᴴ = s := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hdetH : H.det ≠ 0 := by
    rw [hHdef, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.mpr hC) hC
  have hdet : IsUnit s.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetH ?_
    rw [← hss, Matrix.det_mul, h0, zero_mul]
  refine ⟨s, hdet, hsh, hss, ?_⟩

  have hJHJ : H⁻¹ = J * H * J := by
    apply Matrix.inv_eq_right_inv
    calc H * (J * H * J) = H * J * H * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ]

  have ht0 : 0 ≤ J * s * J := by
    have := star_left_conjugate_nonneg hs0 J
    rwa [Matrix.star_eq_conjTranspose, hJh] at this
  have hi0 : 0 ≤ s⁻¹ := hs0.posSemidef.inv.nonneg
  have htt : J * s * J * (J * s * J) = s⁻¹ * s⁻¹ := by
    rw [← Matrix.mul_inv_rev, hss, hJHJ, ← hss]
    calc J * s * J * (J * s * J) = J * s * (J * J) * s * J := by simp only [Matrix.mul_assoc]
      _ = J * (s * s) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have heq : J * s * J = s⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ ht0 hi0).mp htt
  have h1 : s * (J * s * J) = 1 := by
    rw [heq]
    exact Matrix.mul_nonsing_inv s hdet
  calc s * J * s = s * (J * s * J) * J := by simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = J := by rw [h1, Matrix.one_mul]

theorem exists_hermitian_sqrt_mem_UJ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.det ≠ 0) (h : (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε) :
    ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  obtain ⟨s, hdet, hsh, hss, hsJs⟩ := exists_hermitian_sqrt_mul_mul_eq (Formalism.REAL.Jm ε) C
    (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) hC h
  have hu : IsUnit s := (Matrix.isUnit_iff_isUnit_det s).mpr hdet
  have hmem : hu.unit ∈ Formalism.REAL.UJ ε := by
    show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * hu.unit = Formalism.REAL.Jm ε
    rw [IsUnit.unit_spec, hsh]
    exact hsJs
  refine ⟨⟨hu.unit, hmem⟩, ?_, ?_⟩
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ = hu.unit
    rw [IsUnit.unit_spec, hsh]
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ) * hu.unit = Cᴴ * C
    rw [IsUnit.unit_spec, hss]

end GlobalTheory.LeviIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ConvKernel

section General

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y}

theorem integrable_prod_restrict [SFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (s : Set X) (hs : ν s < ⊤) :
    Integrable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) := by
  have hK' : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) ((ν.restrict s).prod μ) :=
    hK.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)
  have hm : AEStronglyMeasurable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) :=
    (hφ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hK'
  refine ⟨hm, ?_⟩
  set M : ENNReal := ENNReal.ofReal C * (ν s) ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)
    with hM
  have hMfin : M ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hs.ne
    norm_num
  have hb : ∀ g, ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) ≤ M := by
    intro g
    have e1 : ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) = eLpNorm (r g : X → ℂ) 1 (ν.restrict s) := by
      rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (r g)).restrict]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := s) (hr g)] with x hx
      rw [hx]
    have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
      (f := (r g : X → ℂ)) (by norm_num) (Lp.aestronglyMeasurable (r g)).restrict
    rw [Measure.restrict_apply_univ] at e2
    rw [e1]
    refine e2.trans ?_
    refine mul_le_mul' ?_ le_rfl
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have h3 := hC g
    rw [Lp.norm_def] at h3
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (r g))]
    exact ENNReal.ofReal_le_ofReal h3
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖φ g * K x g‖ₑ ∂(ν.restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * M ∂μ := by
        refine lintegral_mono fun g => ?_
        simp only [enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul' le_rfl (hb g)
    _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMfin
    _ < ⊤ := ENNReal.mul_lt_top hφ.2 hMfin.lt_top

theorem weak_integral_ae_eq [SigmaFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (t : Lp ℂ 2 ν)
    (ht : ∀ u : Lp ℂ 2 ν, ⟪u, t⟫_ℂ = ∫ g, φ g * ⟪u, r g⟫_ℂ ∂μ) :
    (∀ᵐ x ∂ν, Integrable (fun g => φ g * K x g) μ) ∧
      (t : X → ℂ) =ᵐ[ν] fun x => ∫ g, φ g * K x g ∂μ := by
  have hI := integrable_prod_restrict K hK r hr C hC φ hφ
  refine ⟨?_, ?_⟩
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
    exact (hI s hs).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hs => ?_) (fun s _ hs => ?_)
      (fun s hsm hs => ?_)
    · exact integrableOn_Lp_of_measure_ne_top t (by norm_num) hs.ne
    · exact (hI s hs).integral_prod_left
    · have h := ht (indicatorConstLp 2 hsm hs.ne (1 : ℂ))
      simp only [L2.inner_indicatorConstLp_one] at h
      rw [h, integral_integral_swap (f := fun x g => φ g * K x g) (hI s hs)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (ae_restrict_of_ae (hr g))

end General

theorem rconv_eq_integral : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  intro B φ T hT y
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  obtain ⟨-, -, hn, -, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SigmaFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hq : Measure.QuasiMeasurePreserving (fun p : B.I.GA × B.I.GA => p.1 * p.2)
      (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) (B.I.muA B.μf) :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_mul ((B.I.muA B.μf).restrict B.fund)
        (B.I.muA B.μf)).quasiMeasurePreserving
  exact weak_integral_ae_eq (fun x g => B.I.ext y (x * g))
    ((hext y).2.comp_quasiMeasurePreserving hq) (fun g => B.R g y) (fun g => B.R_spec g y) ‖y‖
    (fun g => (hn g y).le) φ hT.1 (T y) (fun u => hT.2 u y)

end GlobalTheory.ConvKernel
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.MeanZero

theorem continuous_mean {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasure ν] {C : Set G} (hC : IsCompact C) (hν : ν Cᶜ = 0)
    {f : G → ℂ} (hf : Continuous f) : Continuous fun y => ∫ m, f (m * y) ∂ν := by

  have hae : ∀ᵐ m ∂ν, m ∈ C := by
    rw [ae_iff]
    exact hν
  have hres : ν.restrict C = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hcont : Continuous (Function.uncurry fun (y m : G) => f (m * y)) :=
    hf.comp (continuous_snd.mul continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := ν) hcont hC
  rw [hres] at h
  exact h

theorem norm_le_of_mean_zero {X : Type} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] {D : ℕ}
    (f : Fin D → X → ℂ) (c : Fin D → ℂ) (r : ℝ) (hi : ∀ i, Integrable (f i) ν)
    (h0 : ∀ i, ∫ m, f i m ∂ν = 0) (hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  set S : ℝ := ∑ i, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hr0 : 0 ≤ r := by
    obtain ⟨m, hm⟩ := hb.exists
    exact (Real.sqrt_nonneg _).trans hm

  have hint : ∀ i ∈ (Finset.univ : Finset (Fin D)),
      Integrable (fun m => star (c i) * (c i - f i m)) ν :=
    fun i _ => ((integrable_const (c i)).sub (hi i)).const_mul (star (c i))
  have hval : ∫ m, (∑ i, star (c i) * (c i - f i m)) ∂ν = (S : ℂ) := by
    rw [integral_finsetSum _ hint, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (integrable_const _) (hi i), h0 i, integral_const]
    simp [Complex.conj_mul']

  have hbound : ∀ᵐ m ∂ν, ‖∑ i, star (c i) * (c i - f i m)‖ ≤ Real.sqrt S * r := by
    filter_upwards [hb] with m hm
    calc ‖∑ i, star (c i) * (c i - f i m)‖ ≤ ∑ i, ‖star (c i) * (c i - f i m)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖f i m - c i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star, norm_sub_rev]
      _ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖f i m - c i‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt S * r := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
  have key : S ≤ Real.sqrt S * r := by
    have h := norm_integral_le_of_norm_le (integrable_const (Real.sqrt S * r)) hbound
    rw [hval, integral_const] at h
    simpa [Complex.norm_real, abs_of_nonneg hS0] using h
  have hsq := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  nlinarith

theorem norm_le_of_cusp (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (g : ℕ)
    (W : Submodule I.E (Fin I.n → I.E)) (D : ℕ) (Fn : Fin D → I.GA → ℂ) (x : I.GA) (c : Fin D → ℂ) (r : ℝ)
    (hg : 1 ≤ g) (hW : I.IsIsot W)
    (hF : ∀ i, Continuous (Fn i) ∧ (∀ γ ∈ I.GFset, ∀ y, Fn i (γ * y) = Fn i y) ∧
      (∀ k ∈ I.Kg g, ∀ y, Fn i (y * (1, k)) = Fn i y) ∧ I.IsCuspFn (I.muA μf) (Fn i))
    (hr : ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W →
      Real.sqrt (∑ i, ‖Fn i ((ν, 1) * x) - c i‖ ^ 2) ≤ r) :
    Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ r := by
  classical
  obtain ⟨ν, hνP, hνQ, Cp, hCp, -, hνCp⟩ := GlobalTheory.T.exists_unipotentQuotient_invariant_probability I W hW
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨-, -, -, -, hpos⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  obtain ⟨hT2, hLC, hSC, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hKo, ⟨K, hK⟩, -⟩ := hKg g hg
  haveI := hT2
  haveI := hLC
  haveI := hSC

  have hU : {u : I.Gf | x.2⁻¹ * u * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    refine hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const) |>.mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel, ← hK]
    exact K.one_mem

  have horb : ∀ m ∈ I.NA W, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    intro m hm
    obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
    have hm' : γ⁻¹ * m ∈ I.NA W := by
      rw [← hN] at hγN hm ⊢
      exact N.mul_mem (N.inv_mem hγN) hm
    have hk : x.2⁻¹ * (γ⁻¹ * m).2 * x.2 ∈ I.Kg g := hγU
    have heq : ∀ i, Fn i (m * x) = Fn i (((γ⁻¹ * m).1, 1) * x) := by
      intro i
      have h1 := (hF i).2.1 γ hγF (γ⁻¹ * m * x)
      rw [← mul_assoc, mul_inv_cancel_left] at h1
      have h2 : γ⁻¹ * m * x = (((γ⁻¹ * m).1, 1) * x) * (1, x.2⁻¹ * (γ⁻¹ * m).2 * x.2) := by
        ext <;> simp [mul_assoc]
      rw [h1, h2, (hF i).2.2.1 _ hk]
    simp_rw [heq]
    exact hr _ (hsplit _ hm').1

  have hzero : ∀ i, ∫ m, Fn i (m * x) ∂ν = 0 := by
    intro i
    by_contra hne
    have hc := continuous_mean ν hCp hνCp (hF i).1
    have hopen : IsOpen {y | ∫ m, Fn i (m * y) ∂ν ≠ 0} := isOpen_ne_fun hc continuous_const
    have hae := (hF i).2.2.2 W hW ν hνQ
    rw [ae_iff] at hae
    exact (hpos _ hopen ⟨x, hne⟩).ne' hae

  have hint : ∀ i, Integrable (fun m => Fn i (m * x)) ν := by
    intro i
    have hci : Continuous fun m => Fn i (m * x) := (hF i).1.comp (continuous_id.mul continuous_const)
    obtain ⟨B, hB⟩ := hCp.exists_bound_of_continuousOn hci.continuousOn
    have hae : ∀ᵐ m ∂ν, m ∈ Cp := by
      rw [ae_iff]
      exact hνCp
    refine Integrable.of_bound hci.aestronglyMeasurable B ?_
    filter_upwards [hae] with m hm
    exact hB m hm
  have hb : ∀ᵐ m ∂ν, Real.sqrt (∑ i, ‖Fn i (m * x) - c i‖ ^ 2) ≤ r := by
    have hae : ∀ᵐ m ∂ν, m ∈ I.NA W := by
      rw [ae_iff]
      exact hνQ.2.2.1
    filter_upwards [hae] with m hm
    exact horb m hm
  exact norm_le_of_mean_zero ν (fun i m => Fn i (m * x)) c r hint hzero hb

end GlobalTheory.MeanZero
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.ReImVolume

noncomputable def reImLinear (ι : Type) (n : ℕ) :
    (ι → Fin n → ℂ) ≃ₗ[ℝ] (ι × Fin n × Bool → ℝ) where
  toFun y p := if p.2.2 then (y p.1 p.2.1).re else (y p.1 p.2.1).im
  invFun x v i := ⟨x (v, i, true), x (v, i, false)⟩
  map_add' y z := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  map_smul' c y := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  left_inv y := by
    funext v i
    simp
  right_inv x := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp

theorem volume_re_im (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume {z : ℂ | z.re ∈ A ∧ z.im ∈ B} = volume A * volume B := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (hA.prod hB).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  rw [← h]
  rfl

theorem measurePreserving_reImLinear (ι : Type) [Fintype ι] (n : ℕ) :
    MeasurePreserving (reImLinear ι n) volume volume := by
  have hm : Measurable (reImLinear ι n) :=
    (reImLinear ι n).toLinearMap.continuous_of_finiteDimensional.measurable
  refine ⟨hm, ?_⟩
  rw [volume_pi (α := fun _ : ι × Fin n × Bool => ℝ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (reImLinear ι n) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun v => Set.univ.pi fun i =>
        {z : ℂ | z.re ∈ s (v, i, true) ∧ z.im ∈ s (v, i, false)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq]
    constructor
    · intro h v i
      exact ⟨h (v, i, true), h (v, i, false)⟩
    · rintro h ⟨v, i, _ | _⟩
      · exact (h v i).2
      · exact (h v i).1
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, volume_re_im _ _ (hs _) (hs _)]

theorem exists_reIm_measurePreserving :
    ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ),
      MeasurePreserving T volume volume ∧
        ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  intro ι _ n
  let L := (reImLinear ι n).toContinuousLinearEquiv
  refine ⟨{ toAddEquiv := (reImLinear ι n).toAddEquiv
            continuous_toFun := L.continuous
            continuous_invFun := L.symm.continuous }, ?_, fun y v i => ⟨rfl, rfl⟩⟩
  exact measurePreserving_reImLinear ι n

end GlobalTheory.ReImVolume
end
