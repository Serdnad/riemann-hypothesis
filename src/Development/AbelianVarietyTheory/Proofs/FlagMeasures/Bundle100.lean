module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Set.PowersetCard
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitia
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

open scoped Nat Topology

noncomputable section

namespace GlobalTheory.RightDerivSmooth

variable {n : ℕ}


set_option backward.isDefEq.respectTransparency false in
theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2


set_option backward.isDefEq.respectTransparency false in
theorem inUH_exp {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := by
  have hY : ((t : ℂ) • X)ᴴ * H + H * ((t : ℂ) • X) = 0 := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX, smul_zero]
  generalize (t : ℂ) • X = Y at hY
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']


set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_entry X k j).const_mul _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_local {H X g : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (hg : inUH H g)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (e : ∀ h ∈ U, inUH H h → f h = F h) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc := hasDerivAt_mul_exp g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd : HasFDerivAt F (fderiv ℝ F g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [h0] using hgU))
  filter_upwards [h2] with t ht
  exact e _ ht (inUH_mul hg (inUH_exp hX t))

end GlobalTheory.RightDerivSmooth

section
open GlobalTheory.RightDerivSmooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  intro n H X E _ _ f hX hf
  have hder : ∀ g, inUH H g → ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), ∃ F : Matrix (Fin n) (Fin n) ℂ → E,
      IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ (∀ h ∈ U, inUH H h → f h = F h) ∧
      ∀ h ∈ U, inUH H h → rdM X f h = fderiv ℝ F h (h * X) ∧
        HasDerivAt (fun t : ℝ => f (h * NormedSpace.exp ((t : ℂ) • X))) (rdM X f h) 0 := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
    refine ⟨U, F, hU, hgU, hF, e, fun h hhU hh => ?_⟩
    have hd := hasDerivAt_local hX hh hU hhU hF e
    have hr : rdM X f h = fderiv ℝ F h (h * X) := hd.deriv
    exact ⟨hr, hr ▸ hd⟩
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, e, -⟩ := hder g hg
    have hFc : ContinuousWithinAt F {g | inUH H g} g :=
      ((hF.continuousOn).continuousAt (hU.mem_nhds hgU)).continuousWithinAt
    refine hFc.congr_of_eventuallyEq ?_ (e g hgU hg)
    filter_upwards [inter_mem_nhdsWithin {g | inUH H g} (hU.mem_nhds hgU)] with h hh
    exact e h hh.2 hh.1
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    refine ⟨U, fun h => fderiv ℝ F h (h * X), hU, hgU, ?_, fun h hhU hh => (hr h hhU hh).1⟩
    have h1 : ContDiffOn ℝ ∞ (fun h => fderiv ℝ F h) U := hF.fderiv_of_isOpen hU (le_of_eq rfl)
    have h2 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => h * X) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
    exact h1.clm_apply h2.contDiffOn
  · obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    exact (hr g hgU hg).2

end

theorem GlobalTheory.rdM_smoothOnH : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 :=
  fun n H X E _ _ f hX hf => GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group n H X E f hX hf
end
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorExp

theorem sum_dite_card {n l : ℕ} {M : Type*} [AddCommMonoid M] (f : Set.powersetCard (Fin n) l → M) :
    ∑ J : Finset (Fin n), (if h : J.card = l then f ⟨J, h⟩ else 0) = ∑ S, f S := by
  symm
  refine Finset.sum_of_injOn (fun S : Set.powersetCard (Fin n) l => S.1)
    (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro J _ hJ
    rw [dif_neg]
    intro h
    exact hJ ⟨⟨J, h⟩, by simp, rfl⟩
  · intro S _
    have h : S.1.card = l := S.2
    rw [dite_eq_left h]

theorem exp_smul_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) =
      (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun j => ((Real.exp (t * hY.eigenvalues j) : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  have h2 : Uᴴ * U = 1 := (hY.eigenvectorUnitary).2.1
  have hs : Y = U * diagonal (fun j => ((hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h3 : (t : ℂ) • Y = U * diagonal (fun j => ((t * hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hs]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  rw [h3]
  refine (Matrix.exp_units_conj (⟨U, Uᴴ, h1, h2⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).trans ?_
  rw [Matrix.exp_diagonal]
  change U * _ * Uᴴ = _
  congr 3
  funext j
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem leadMinor_exp_eq_sum (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ)
    (hl : l ≤ n) :
    ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧
      ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl =
        ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  set A : Matrix (Fin l) (Fin n) ℂ := U.submatrix (Fin.castLE hl) id with hA
  have hAA : A * Aᴴ = 1 := by
    rw [hA, conjTranspose_submatrix, ← submatrix_mul U Uᴴ _ id _ Function.bijective_id, h1]
    exact submatrix_one _ (Fin.castLE_injective hl)
  refine ⟨fun J => if h : J.card = l then
    ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro J
    dsimp only
    split_ifs <;> positivity
  · intro J hJ
    by_contra h
    exact hJ (dif_neg h)
  · rw [sum_dite_card (fun S => ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2)]
    exact GlobalTheory.sum_norm_sq_minors_eq_one A hAA
  · intro t
    have hsum : (∑ J : Finset (Fin n), (if h : J.card = l then
        ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0) *
          Real.exp (t * ∑ j ∈ J, hY.eigenvalues j)) =
        ∑ S : Set.powersetCard (Fin n) l, ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2 *
          Real.exp (t * ∑ j ∈ S.1, hY.eigenvalues j) := by
      rw [← sum_dite_card]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [hsum, exp_smul_eq hY t, leadMinor]
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
      ← conjTranspose_submatrix]
    refine (GlobalTheory.det_mul_diagonal_mul_eq_sum_minors A _ Aᴴ).trans ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← conjTranspose_submatrix, det_conjTranspose, Complex.star_def, Complex.mul_conj',
      Finset.mul_sum, Real.exp_sum]
    push_cast
    ring

end GlobalTheory.LeadMinorExp
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreDensity

theorem not_pos_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : ¬ 0 < h b := by
  intro hpos
  have hev : ∀ᶠ x in nhds b, h b / 2 < h x := by
    have h1 : ∀ᶠ x in nhdsWithin b B, h b / 2 < h x :=
      (hh b hb).eventually (lt_mem_nhds (by linarith))
    rwa [hB.nhdsWithin_eq hb] at h1
  obtain ⟨U, hUsub, hUo, hbU⟩ := mem_nhds_iff.1 (Filter.inter_mem (hB.mem_nhds hb) hev)
  obtain ⟨K, hK, hbK, hKU⟩ := exists_compact_subset hUo hbU
  have hKB : K ⊆ B := fun x hx => (hUsub (hKU hx)).1
  have hKh : ∀ x ∈ K, h b / 2 < h x := fun x hx => (hUsub (hKU hx)).2
  have hle : ∫ _ in K, h b / 2 ∂ν ≤ ∫ x in K, h x ∂ν :=
    setIntegral_mono_on (continuousOn_const.integrableOn_compact hK)
      ((hh.mono hKB).integrableOn_compact hK) hK.measurableSet (fun x hx => (hKh x hx).le)
  rw [setIntegral_const, h0 K hK hKB, smul_eq_mul] at hle
  have hKpos : 0 < ν K :=
    lt_of_lt_of_le (isOpen_interior.measure_pos ν ⟨b, hbK⟩) (measure_mono interior_subset)
  have hreal : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hK.measure_lt_top.ne
  have := mul_pos hreal (half_pos hpos)
  linarith

theorem eq_zero_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : h b = 0 := by
  have h1 := not_pos_of_setIntegral_isCompact_eq_zero ν hB hh h0 hb
  have h2 : ¬ 0 < -h b := not_pos_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => -h x) hh.neg
    (fun S hS hSB => by rw [integral_neg, h0 S hS hSB, neg_zero]) hb
  linarith [not_lt.1 h1, not_lt.1 h2]

theorem eq_of_setIntegral_isCompact_eq {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {g h : X → ℂ}
    (hg : ContinuousOn g B) (hh : ContinuousOn h B)
    (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, g x ∂ν = ∫ x in S, h x ∂ν)
    {b : X} (hb : b ∈ B) : g b = h b := by
  have hk : ContinuousOn (fun x => g x - h x) B := hg.sub hh
  have hint : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, (g x - h x) ∂ν = 0 := by
    intro S hS hSB
    rw [integral_sub ((hg.mono hSB).integrableOn_compact hS) ((hh.mono hSB).integrableOn_compact hS),
      h0 S hS hSB, sub_self]
  have hre : (g b - h b).re = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).re)
      (Complex.continuous_re.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.reCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.reCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_re]) hb
  have him : (g b - h b).im = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).im)
      (Complex.continuous_im.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.imCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.imCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_im]) hb
  have hz : g b - h b = 0 := Complex.ext (by simpa using hre) (by simpa using him)
  exact sub_eq_zero.1 hz

theorem contDensityOn_eq_fibre_integral : ∀ (V X : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (f : V → X) (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (fib : X → Measure V) (φ : V → ℝ) (g : X → ℂ), Continuous f → IsOpen B → IsFibreFamily μ f id Set.univ ν B fib → Continuous φ → HasCompactSupport φ → (∀ v, 0 ≤ φ v) → IsContDensityOn μ f id ν B (fun v => (φ v : ℂ)) g → ∀ b ∈ B, g b = ((∫ v, φ v ∂(fib b) : ℝ) : ℂ) ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (g b).re := by
  intro V X _ _ _ _ _ _ _ _ μ f ν _ _ B fib φ g hf hB hfib hφ hφc hφ0 hdens
  obtain ⟨hconc, hdis, hreg⟩ := hfib
  obtain ⟨hgc, hgint⟩ := hdens
  have hφm : Measurable φ := hφ.measurable
  obtain ⟨hφi, hGc⟩ := hreg φ hφ hφc (Set.subset_univ _)
  set G : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hG
  have hG0 : ∀ b, 0 ≤ G b := fun b => integral_nonneg (fun v => hφ0 v)
  have hlin : ∀ b ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (G b) := fun b hb =>
    (ofReal_integral_eq_lintegral_ofReal (hφi b hb) (Filter.Eventually.of_forall hφ0)).symm
  have key : ∀ S : Set X, IsCompact S → S ⊆ B →
      ∫ x in S, g x ∂ν = ∫ x in S, ((G x : ℝ) : ℂ) ∂ν := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    have hpre : MeasurableSet (f ⁻¹' S) := hf.measurable hSm

    have hL : ∫⁻ v in f ⁻¹' S, ENNReal.ofReal (φ v) ∂μ = ∫⁻ b in S, ENNReal.ofReal (G b) ∂ν := by
      have h2 := hdis ((f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)))
        ((ENNReal.measurable_ofReal.comp hφm).indicator hpre)
      rw [Measure.restrict_univ, lintegral_indicator hpre] at h2
      rw [h2, ← lintegral_indicator hSm]
      apply lintegral_congr
      intro b
      have hae : ∀ᵐ v ∂(fib b), f v = b := by
        rw [ae_iff]
        refine measure_mono_null ?_ (hconc b)
        intro v hv
        simpa using hv
      by_cases hbS : b ∈ S
      · rw [Set.indicator_of_mem hbS, ← hlin b (hSB hbS)]
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        simp [hv, hbS]
      · calc ∫⁻ v, (f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)) v ∂(fib b)
            = ∫⁻ _, 0 ∂(fib b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with v hv
              simp [hv, hbS]
          _ = S.indicator (fun b => ENNReal.ofReal (G b)) b := by
              simp [hbS]
    have hGS : IntegrableOn G S ν := (hGc.mono hSB).integrableOn_compact hS
    have hφS : ∫ v in f ⁻¹' S, φ v ∂μ = ∫ b in S, G b ∂ν := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
          hφ.aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
          hGS.integrable.aestronglyMeasurable, hL]
    have e := hgint S hS hSB
    simp only [Set.image_id] at e
    rw [← e, integral_complex_ofReal, integral_complex_ofReal, hφS]
  intro b hb
  have hgb : g b = ((G b : ℝ) : ℂ) :=
    eq_of_setIntegral_isCompact_eq ν hB hgc (Complex.continuous_ofReal.comp_continuousOn hGc) key hb
  refine ⟨hgb, ?_⟩
  rw [hlin b hb, hgb, Complex.ofReal_re]

end GlobalTheory.FibreDensity
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  first | exact @GlobalTheory.UnitriTuple.unitri_haar | exact GlobalTheory.UnitriTuple.unitri_haar | (intros; apply GlobalTheory.UnitriTuple.unitri_haar <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

namespace GlobalTheory.HermFibreLocal

theorem exists_isFibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM v μ ν hμ hν
  exact (GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM hJ μ hμ ν hν).2

end GlobalTheory.HermFibreLocal
end
