module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagonalIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionInterSubspace
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnfoldingIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

namespace UC

theorem kerPTh : KerPTh := KerPTh_of exp_series_entire latticeGaussSummable formNormEquiv
theorem kerPNonzero : KerPNonzero := KerPNonzero_of diagonalIntegral
theorem gaussIntegrable : GaussIntegrable := GaussIntegrable_of formNormEquiv
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussSumEighthPower

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V}
  {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

theorem th_congr (α' : V → ℂ) (h : ∀ x ∈ Λ, α' x = α x) {F : V → ℂ} (hF : F ∈ Th H α Λ) :
    F ∈ Th H α' Λ :=
  ⟨hF.1, fun x hx z => by rw [h x hx]; exact hF.2 x hx z⟩

theorem pull_mem (hU : UnitaryData H Λ α δ Ae) {θ : V → ℂ} (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ ∈ Th H α (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  rw [thIsom V V H H δ hU.isom Λ α (pullInv δ θ)]
  have e : (fun v => pullInv δ θ (δ v)) = θ := by
    funext v
    simp [pullInv]
  rw [e]
  exact th_congr _ hU.inv hθ

theorem exists_const (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ) :
    ∃ c : ℂ, ∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  obtain ⟨w, z, hwz⟩ := kerPNonzero V H Λ α hU.herm hU.pos hL hU.selfDual hU.semi
  obtain ⟨θ₀, hdef⟩ : ∃ θ₀ : V → ℂ, θ₀ = fun z => kerP H α Λ z w := ⟨_, rfl⟩
  have hθ₀ : θ₀ ∈ Th H α Λ := by
    rw [hdef]
    exact (kerPTh V H Λ α hU.herm hU.pos hL hU.semi w).2
  have hne : θ₀ ≠ 0 := by
    intro h
    apply hwz
    have := congrFun h z
    rw [hdef] at this
    exact this
  obtain ⟨-, hline2⟩ := lineTransport V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.selfDual
    (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.semi hU.semi' hU.idx₂ hU.idx₁ θ₀ hθ₀ hne
    (hLine θ₀ hθ₀ hne)
  obtain ⟨c, hc⟩ := hline2 _ (pull_mem hU hθ₀)
  refine ⟨c, fun θ hθ => ?_⟩
  obtain ⟨a, rfl⟩ := hLine θ₀ hθ₀ hne θ hθ
  rw [Inv.inter_smul, smul_comm, ← hc]
  rfl

theorem latA_idx_ne (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  intro h0
  rw [h0] at hidx
  have hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
  have h2 : ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hdt0)
  exact mul_ne_zero h1 h2 (by simpa using hidx.symm)

theorem sqrt_card (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) :
    Real.sqrt S.card
      = Real.sqrt (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ) * ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  rw [(repsExist V _ _ (latA_idx_ne hL hU)).2 S hS, hidx, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end Line

theorem norm_sum_phi {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
    {δ Ae : V ≃ₗ[ℂ] V} (hU : UnitaryData H Λ α δ Ae) {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ‖∑ x ∈ S, phiC H α Ae x‖ = Real.sqrt S.card := by
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  have h1 : ‖gaussC H α Ae S‖ = 1 := by
    have := congrArg norm h8
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hs : Real.sqrt S.card ≠ 0 := by
    intro h0
    rw [gaussC, h0] at h1
    simp at h1
  rw [gaussC, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h1
  field_simp at h1
  exact h1

theorem diag_integrable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (D' : Set V)
    (hb : Bornology.IsBounded D') (y : V) (hy : α y = 1 ∨ α y = -1) :
    Integrable (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') := by
  obtain ⟨c₀, C₀, hc₀, -, hform⟩ := formNormEquiv V H hH hP
  obtain ⟨u, hu, hule⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c₀) ‖y‖ (by positivity)
  have hfin : μ D' < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D') := ⟨by simpa using hfin⟩
  have hbound : ∀ x : Λ, ‖diagCoef H α y (x : V)‖ ≤ u x := by
    intro x
    rw [norm_diagCoef H α y x hy (hα.1 x x.2)]
    refine le_trans ?_ (hule x (-y) (by rw [norm_neg]))
    apply Real.exp_le_exp.mpr
    have h := (hform (y + (x : V))).1
    have e : (x : V) - -y = y + (x : V) := by abel
    rw [e]
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hpi.le]
  have hn : ∀ (x : Λ) (z : V), ‖diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))‖ ≤ u x := by
    intro x z
    rw [norm_mul, norm_char, mul_one]
    exact hbound x
  have hcont : Continuous fun z => ∑' x : Λ, diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
    refine continuous_tsum (fun x => ?_) hu hn
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_altE H hH _))
  have e : (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ))
      = fun z => ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) :=
    funext fun z => diag_expansion H hH α Λ y z
  rw [e]
  refine Integrable.of_bound hcont.aestronglyMeasurable (∑' x, u x)
    (Filter.Eventually.of_forall fun z => ?_)
  exact tsum_of_norm_bounded hu.hasSum (fun x => hn x z)

theorem const_value {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {H : Sesq V} {Λ : AddSubgroup V}
    {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V} (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae)
    (hLine : AtMostLine H α Λ) {D' : Set V}
    (hD' : IsAddFundamentalDomain (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ : AddSubgroup V) D' μ)
    (hb : Bornology.IsBounded D') {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ∃ c : ℂ, (∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ) ∧
      c * ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ * ((μ D').toReal : ℂ)
        = (∑ x ∈ S, phiC H α Ae x) *
            (((∫ z, wt H z ∂μ : ℝ) : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)) := by
  classical
  obtain ⟨c, hc⟩ := exists_const hL hU hLine
  refine ⟨c, hc, ?_⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist V Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.idx₂).1
  have hsd2 := Cay.selfDual_img H Λ δ hU.isom hU.selfDual
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  rw [← hr]
  have hpt : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ)
      = c * r * ∑ y ∈ S₂, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) := by
    intro z
    have hm := (kerPTh V H Λ α hU.herm hU.pos hL hU.semi z).2
    have h1 := congrFun (hc _ hm) z
    have h2 := interReps V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.semi' _ hm.2 S₂ hS₂ z
    have h3 : pullInv δ (fun v => kerP H α Λ v z) z = kerP H α Λ (δ.symm z) z := rfl
    rw [h3, Pi.smul_apply, h2, ← hr, sumU, smul_eq_mul] at h1
    rw [h1, ← Finset.sum_mul]
    ring
  have hint : ∀ y ∈ S₂, Integrable
      (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') :=
    fun y hy => diag_integrable μ H Λ α hU.herm hU.pos hL hU.semi D' hb y (hU.semi'.1 y (hS₂.1 y hy))
  have hleft := unfoldingIntegral V μ H Λ α δ Ae hL hU D' hD' hb S hS
  rw [(cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).2] at hleft
  rw [← hleft]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ hint]
  have hdiag := diagonalIntegral V μ H Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.herm hU.pos hL hU.selfDual hsd2
    hU.semi hU.semi' D' hD' hb
  obtain ⟨y₀, hy₀, hy₀Λ, hsum⟩ := Inv.sum_reps hS₂
    (fun y => ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ)
    (fun y hy hyΛ => by
      have := hdiag y (hS₂.1 y hy)
      rw [if_neg hyΛ] at this
      exact this)
  rw [hsum]
  have := hdiag y₀ (hS₂.1 y₀ hy₀)
  rw [if_pos hy₀Λ] at this
  rw [this]

end UC

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H.CmData

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)

variable {n : Type} [Fintype n] [DecidableEq n]

def embA (a : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun w => if w.1 = a then x w.2 else 0

theorem slice_embA (a a' : Fin 4) (x : n → ℂ) : slice a' (embA a x) = if a' = a then x else 0 := by
  ext i
  by_cases h : a' = a <;> simp [slice, embA, h]

theorem embA_mem (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) {x : n → ℂ} (hx : x ∈ Λ) : embA a x ∈ pow4 Λ := by
  intro a'
  rw [slice_embA]
  split_ifs
  · exact hx
  · exact Λ.zero_mem

theorem isSelfDual_matH_blk4_pow4 (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hsd : IsSelfDual (matH h) Λ) :
    IsSelfDual (matH (blk4 h)) (pow4 Λ) := by
  ext x
  constructor
  · intro hx a
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (embA a y) (embA_mem Λ a hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [altE, matrixForm_fourfoldBlock, slice_embA]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · intro hx y hy
    have : ∀ a, ∃ m : ℤ, altE (matH h) (slice a x) (slice a y) = (m : ℝ) := fun a => by
      have h1 : slice a x ∈ dualLat (matH h) Λ := by rw [hsd]; exact hx a
      exact h1 _ (hy a)
    choose m hm using this
    refine ⟨∑ a, m a, ?_⟩
    simp only [altE] at hm
    simp only [altE, matrixForm_fourfoldBlock, Complex.im_sum, hm]
    push_cast
    rfl

theorem selfDual_img {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V)
    (H' : Sesq W) (g : V ≃ₗ[ℂ] W) (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (Λ : AddSubgroup V)
    (hsd : IsSelfDual H Λ) : IsSelfDual H' (imgLat (g : V →ₗ[ℂ] W) Λ) := by
  ext x
  constructor
  · intro hx
    refine ⟨g.symm x, ?_, by simp⟩
    show g.symm x ∈ Λ
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g y) ⟨y, hy, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg (g.symm x) y
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [altE, this]
  · rintro ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    have h1 : x' ∈ dualLat H Λ := by rw [hsd]; exact hx'
    obtain ⟨m, hm⟩ := h1 y' hy'
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg x' y'
    simp only [altE]
    exact congrArg Complex.im this

theorem odd_b (a : ℕ) (b c : ℤ) (d : ℕ) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d) (h8 : d % 8 = 7) : Odd b := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | hb
  · exfalso
    subst hk
    have h5 : 4 * ((a : ℤ) * c) = 4 * (k * k) + d := by rw [← mul_assoc, h4]; ring
    generalize (a : ℤ) * c = s at h5
    generalize k * k = t at h5
    omega
  · exact hb

theorem stdData_cm (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (h4 : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hodd : Odd a) (h8 : d % 8 = 7) (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hg : IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ)
    (i1 : relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0) :
    StdData (cmL a b d ha hd lam hlam) (lam * a) h Λ (alphaQ (Real.sqrt d / 2) (matH h))
      (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g := by
  exact {
    per := (cmL a b d ha hd lam hlam).ω₁_mem_lattice
    half := (cmL a b d ha hd lam hlam).ω₁_div_two_notMem_lattice
    isom := hg
    alpha0 := by simp [alphaQ, qOf]
    betaStd := fun x hx => CmStdCharScale_proof a b c d ha hd lam hlam h4 hodd h8 _ x hx
    betaSemi := by
      have hsd' := selfDual_img _ _ g hg _ (isSelfDual_matH_blk4_pow4 h Λ hsd)
      refine (quadMultiplierSemicharacter _ _ (standardFormBasic _ _).2.1 b d
        (odd_b a b c d h4 h8) _ (le_of_eq hsd'.symm) ?_).2.2
      rintro x ⟨x', hx', rfl⟩
      refine ⟨cmTheta b d • x', fun a' => hst _ (hx' a'), ?_⟩
      simp
    betaAlpha := by
      intro x
      rw [← quadMultiplierRules.2 n h]
      exact quadMultiplierRules.1 _ _ _ _ _ hg _ x
    selfDual := selfDual_img _ _ g hg _ (isSelfDual_matH_blk4_pow4 h Λ hsd)
    idx₁ := i1
    idx₂ := i2
  }

end Formalism.L2.Th1.H.CmData

namespace Formalism.L2.Th1.H

theorem StdDataCm_proof : StdDataCm := by
  intro a b c d ha hd lam hlam h4 hodd h8 n _ _ h Λ g hg hsd hst i1 i2
  exact CmData.stdData_cm a b c d ha hd lam hlam h4 hodd h8 h Λ g hg hsd hst i1 i2

end Formalism.L2.Th1.H
end
end
