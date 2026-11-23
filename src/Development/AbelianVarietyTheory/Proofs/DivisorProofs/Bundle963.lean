module

import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle938
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle035
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Algebra.Group.Units
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

@[expose] public section

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal Matrix

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def baseGL (X : Data E r) (τ : X.Ψ) : GL (Fin r) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mat (baseFr X) τ) (PeterssonCompare.det_baseFr X τ)

theorem val_baseGL (X : Data E r) (τ : X.Ψ) : (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) = mat (baseFr X) τ := rfl


omit [NumberField E] [IsCMField E] in
theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A g : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (A * g) = gᵀ * gram τ G A * g.map (starRingEnd ℂ) := by
  rw [UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]


omit [NumberField E] [IsCMField E] in
theorem isometry_iff_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (n : Matrix (Fin r) (Fin r) ℂ)
    (P : GL (Fin r) ℂ) :
    (∀ u w, hermC τ G (n *ᵥ u) (n *ᵥ w) = hermC τ G u w) ↔
      gram τ G (n * (P : Matrix (Fin r) (Fin r) ℂ)) = gram τ G P := by
  constructor
  · intro h
    ext a b
    simp only [gram, Matrix.of_apply, UnitaryFrames.col_mul', h]
  · intro h u w
    obtain ⟨u', rfl⟩ : ∃ u', u = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ u' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    obtain ⟨w', rfl⟩ : ∃ w', w = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ w' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, UnitaryFrames.hermC_mulVec, UnitaryFrames.hermC_mulVec, h]

def toIso (X : Data E r) (g : RealGrp X) : UnitaryFrames.unitarySubgroup X :=
  ⟨fun τ => baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹, by
    intro τ
    refine (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).2 ?_
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul, gram_mul_right, val_baseGL, baseFr_mem X τ]
    exact (g τ).2⟩

def ofIso (X : Data E r) (h : UnitaryFrames.unitarySubgroup X) : RealGrp X :=
  fun τ => ⟨(baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ, by
    have hu : gram τ.1 X.Gm (((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ)) = gram τ.1 X.Gm (baseGL X τ) :=
      (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).1 (h.2 τ)
    have e : ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) =
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) *
          (((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, gram_mul_right, val_baseGL, baseFr_mem X τ] at hu
    exact hu⟩

def isoEquiv (X : Data E r) : RealGrp X ≃ₜ* UnitaryFrames.unitarySubgroup X where
  toFun := toIso X
  invFun := ofIso X
  left_inv g := by
    funext τ
    apply Subtype.ext
    show (baseGL X τ)⁻¹ * (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) * baseGL X τ = _
    group
  right_inv h := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * ((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ) * (baseGL X τ)⁻¹ = _
    group
  map_mul' g g' := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * (((g * g') τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ =
      (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) *
        (baseGL X τ * ((g' τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹)
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    group
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun τ => ?_)
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply τ))).mul continuous_const
  continuous_invFun := by
    refine continuous_pi fun τ => continuous_induced_rng.2 ?_
    exact (continuous_const.mul ((continuous_apply τ).comp continuous_subtype_val)).mul continuous_const

theorem frameOf_eq_lmulC (X : Data E r) (g : RealGrp X) :
    frameOf X g = X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) (baseFr X) := by
  funext τ
  have key : mat (frameOf X g) τ = mat (X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) :
      X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)) τ := by
    rw [PeterssonCompare.mat_frameOf, show ∀ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    mat (X.lmulC n x) τ = n τ * mat x τ from fun _ _ => rfl, ← val_baseGL]
    show _ = ((baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ : GL (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ) * _
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  exact key

theorem muF_univ_ne_zero (X : Data E r) {x0 : Frame X.Ψ r} (h : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  apply GlobalTheory.MetricWeightTest.muF_ne_zero <;> assumption

theorem exists_haarChart (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, -⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  have hx0 : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  obtain ⟨ν, hνl, hνf, hν⟩ := UnitaryInvMeasure.invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm (baseFr X) hx0
  haveI := hνl
  haveI := hνf
  haveI : (haarR X).IsHaarMeasure := by unfold haarR; infer_instance
  set e := isoEquiv X
  set μ : Measure H := (haarR X).map e with hμdef
  haveI : μ.IsHaarMeasure := e.isHaarMeasure_map (haarR X)
  have hs := Measure.isMulLeftInvariant_eq_smul ν μ
  set s := ν.haarScalarFactor μ
  set L : H → Frame X.Ψ r := fun h =>
    X.lmulC (fun τ => ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)

  have hR : ∀ F : H → ℝ≥0∞, ∫⁻ g, F (e g) ∂haarR X = ∫⁻ h, F h ∂μ := by
    intro F
    have := lintegral_map_equiv F (e.toHomeomorph.toMeasurableEquiv) (μ := haarR X)
    exact this.symm
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    exact muF_univ_ne_zero X hx0 h1.symm
  refine ⟨((s : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hs0), fun φ hφ hφb => ?_⟩
  have h1 := hν φ hφ hφb
  rw [hs, lintegral_smul_measure] at h1
  have h2 : ∫⁻ g, φ (frameOf X g) ∂haarR X = ∫⁻ h, φ (L h) ∂μ := by
    rw [← hR]
    refine lintegral_congr fun g => ?_
    rw [frameOf_eq_lmulC]
    rfl
  rw [h2, ← h1, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hs0)
    ENNReal.coe_ne_top, one_mul]

end

end GlobalTheory.FlagQuotHaar
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem degenerateWhittakerDim_zero_eq_whittakerDim {F : Type} [Field F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) : whCut ψ τ 0 = whDim ψ τ := by
  have h : ∀ g : GL (Fin r) F, edgeSum (cutEdge 0) g = edgeSum supEdge g := by
    intro g
    unfold edgeSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      if_congr (by simp [cutEdge, supEdge]) rfl rfl
  unfold whCut whDim
  rw [show (fun g : GL (Fin r) F => ψ (edgeSum (cutEdge 0) g)) = fun g => ψ (edgeSum supEdge g) from
    funext fun g => by rw [h]]

theorem numBlockSetsOfTotalSize_zero_eq_one {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  apply GlobalTheory.FinGL.numBlockSetsOfTotalSize_zero <;> assumption

theorem whDim_parInd_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ
  rw [← degenerateWhittakerDim_zero_eq_whittakerDim, GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ 0 (Or.inr rfl), numBlockSetsOfTotalSize_zero_eq_one,
    GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ]

end GlobalTheory.FinGL
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HostModel

namespace GlobalTheory.HostRamif

variable {E : Type} [Field E] [NumberField E]

theorem intCast_mem_iff {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal) (hlw : (l : 𝓞 E) ∈ w) (n : ℤ) :
    (n : 𝓞 E) ∈ w ↔ (l : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hc : IsCoprime (l : ℤ) n := ((Nat.prime_iff_prime_int.mp hl).irreducible.coprime_iff_not_dvd).2 hnd
    obtain ⟨a, b, hab⟩ := hc
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 E) = (a : 𝓞 E) * (l : 𝓞 E) + (b : 𝓞 E) * (n : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [h1]
    exact add_mem (w.mul_mem_left _ hlw) (w.mul_mem_left _ hn)
  · rintro ⟨c, rfl⟩
    push_cast
    exact w.mul_mem_right _ hlw

theorem dvd_different_iff [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) : w ∣ differentIdeal ℤ (𝓞 E) ↔ (l : ℤ) ∣ discr E := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hwp := hw.isPrime
  haveI : w.LiesOver (Ideal.span {(l : ℤ)}) := (Ideal.liesOver_span_iff hw.ne_top hp).mpr (by simpa using hlw)
  rw [← not_iff_not, not_dvd_differentIdeal_iff, not_dvd_discr_iff_forall_liesOver E (𝓞 E) hp]
  refine ⟨fun h P hP hPl => ?_, fun h => h w hw inferInstance⟩
  have hPp := hP.isPrime
  rw [← Ideal.ramificationIdx_eq_one_iff] at h ⊢
  rw [← h]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) _ _ (E ≃ₐ[ℚ] E)

variable [IsCMField E]

theorem exists_coords (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ x y : ℤ, a = x + y * H.w0 := by
  apply GlobalTheory.Models.exists_eq_of_mem_adjoin_quadratic_generator <;> assumption

theorem isSquare_iff (H : Host E) {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) (hd : l ≠ H.d) :
    IsSquare (-(H.d : ZMod l)) ↔ ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w := by
  have hwp := hw.isPrime
  haveI := Fact.mk hl
  have h1 : (1 : 𝓞 E) ∉ w := fun h => hw.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hw0 : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ _
  by_cases h2 : l = 2
  · subst h2
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 8 * k + 7 := ⟨H.d / 8, by have := H.d_mod; omega⟩
      have hsq : H.w0 * (1 - H.w0) = (k + 1) * ((2 : ℕ) : 𝓞 E) := by
        have h := H.rt_sq
        rw [rt_eq, hk] at h
        push_cast at h ⊢
        apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
        linear_combination -h
      have hm : H.w0 * (1 - H.w0) ∈ w := hsq ▸ w.mul_mem_left _ hlw
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, hw0, h, fun h' => h1 ?_⟩
        rw [cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
      · refine ⟨_, sub_mem (one_mem _) hw0, h, fun h' => h1 ?_⟩
        rw [map_sub, map_one, cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
    · generalize (-(H.d : ZMod 2)) = z
      revert z
      decide
  · have hl2 : ¬ (l : ℤ) ∣ 2 := fun h => h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by exact_mod_cast h))
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
      have hdv : (l : ℤ) ∣ -(H.d : ℤ) - s * s := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hs, sub_self]
      have hm : (H.rt - s) * (-H.rt - s) ∈ w := by
        have := (intCast_mem_iff hl hw hlw _).2 hdv
        have e : (H.rt - s) * (-H.rt - s) = -((-(H.d : ℤ) - s * s : ℤ) : 𝓞 E) := by
          push_cast
          linear_combination -H.rt_sq
        rw [e]
        exact neg_mem this
      have hnb : ¬ (H.rt - s ∈ w ∧ -H.rt - s ∈ w) := by
        rintro ⟨ha, hb⟩
        have : ((2 * s : ℤ) : 𝓞 E) ∈ w := by
          have e : ((2 * s : ℤ) : 𝓞 E) = -((H.rt - s) + (-H.rt - s)) := by push_cast; ring
          rw [e]
          exact neg_mem (add_mem ha hb)
        have hs' := (hp.dvd_or_dvd ((intCast_mem_iff hl hw hlw _).1 this)).resolve_left hl2
        have : (l : ℤ) ∣ (H.d : ℤ) := by
          have := dvd_add hdv (hs'.mul_right s)
          simpa using this
        exact hd ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 (by exact_mod_cast this))
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, sub_mem (rt_mem_adjoin H) (intCast_mem _ s), h, fun h' => hnb ⟨h, ?_⟩⟩
        rwa [map_sub, bar_rt, map_intCast] at h'
      · refine ⟨_, sub_mem (neg_mem (rt_mem_adjoin H)) (intCast_mem _ s), h, fun h' => hnb ⟨?_, h⟩⟩
        rwa [map_sub, map_neg, bar_rt, neg_neg, map_intCast] at h'
    · rintro ⟨a, ha, haw, hbw⟩
      obtain ⟨x, y, rfl⟩ := exists_coords H ha
      have hb : H.bar (x + y * H.w0) = x + y * (1 - H.w0) := by
        rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
      rw [hb] at hbw
      have hy : ¬ (l : ℤ) ∣ y := by
        intro hy
        apply hbw
        have hyw := (intCast_mem_iff hl hw hlw _).2 hy
        have e : (x : 𝓞 E) + y * (1 - H.w0) = (x + y * H.w0) + y * (1 - 2 * H.w0) := by ring
        rw [e]
        exact add_mem haw (w.mul_mem_right _ hyw)
      have hn : (l : ℤ) ∣ (2 * x + y) ^ 2 + H.d * y ^ 2 := by
        rw [← intCast_mem_iff hl hw hlw]
        have e : (((2 * x + y) ^ 2 + H.d * y ^ 2 : ℤ) : 𝓞 E) =
            (x + y * H.w0) * (4 * (x + y * (1 - H.w0))) := by
          have h := H.rt_sq
          rw [rt_eq] at h
          push_cast
          linear_combination (y : 𝓞 E) ^ 2 * h
        rw [e]
        exact w.mul_mem_right _ haw
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hn hy
      push_cast at hn
      refine ⟨(2 * x + y) / y, ?_⟩
      field_simp
      linear_combination -hn

theorem isHostField_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    EigenvectorLieDegree.IsHostField H ↔ IsAbelianGalois ℚ E ∧ AdelicDegreeTameRamification.TameAtRamified H := by
  intro E _ _ _ H
  unfold EigenvectorLieDegree.IsHostField AdelicDegreeTameRamification.TameAtRamified
  refine and_congr_right fun hab => ⟨fun h l w hl hld hw hlw => ?_, fun h w hwd => ?_⟩
  · have hne : w ≠ ⊥ := by
      rintro rfl
      exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hlw))
    obtain ⟨h1, h2⟩ := h ⟨w, hw.isPrime, hne⟩ ((dvd_different_iff hl hw hlw).2 hld)
    refine ⟨h1, fun hd => ?_, fun hd => ?_⟩
    · rcases h2 l hl hlw with h3 | h3
      · exact (isSquare_iff H hl hw hlw hd).1 h3.2
      · exact absurd h3.1 hd
    · rcases h2 l hl hlw with h3 | h3
      · exact absurd hd h3.1
      · exact fun h4 => h3.2 (Ideal.dvd_span_singleton.2 h4)
  · have hw := w.isMaximal
    refine ⟨?_, fun l hl hlw => ?_⟩
    · obtain ⟨l, hl, hlw⟩ : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ w.asIdeal := by
        haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
        letI := Ideal.Quotient.field w.asIdeal
        refine ⟨ringChar (𝓞 E ⧸ w.asIdeal), CharP.char_is_prime (𝓞 E ⧸ w.asIdeal) _, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
        exact ringChar.Nat.cast_ringChar
      exact (h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw).1
    · obtain ⟨-, h2, h3⟩ := h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw
      by_cases hd : l = H.d
      · exact Or.inr ⟨hd, fun h4 => h3 hd (Ideal.dvd_span_singleton.1 h4)⟩
      · exact Or.inl ⟨hd, (isSquare_iff H hl hw hlw hd).2 (h2 hd)⟩

end GlobalTheory.HostRamif
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  first | exact @GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | exact GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | (intros; apply GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl


end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

end Extension

end GlobalTheory.FlatDegreeCompare
end
end
