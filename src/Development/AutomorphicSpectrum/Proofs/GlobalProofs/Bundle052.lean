module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mnorm_real_smul (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : mnorm (s • X) = |s| * mnorm X := by
  unfold mnorm
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem iterate_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (GlobalTheory.T.derived_action_of_smooth_vector hG hrep ih hX).2

theorem iterate_real_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) (m : ℕ) :
    (dRep π (s • X))^[m] v = ((s : ℂ) ^ m) • (dRep π X)^[m] v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm := iterate_smooth hG hrep hs hX m
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', GlobalTheory.GKLie.dRep_smul,
      (GlobalTheory.T.derived_action_additive hG hrep hsm hsm hX hX).2.2, ← Complex.coe_smul, smul_smul, pow_succ']

theorem analytic_coeff : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H),
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ := by
  intro n G H _ _ _ π hG hU v hs hw X hX w t₀ _
  obtain ⟨r, hr, hsum⟩ := GlobalTheory.T.analytic_vector_exponential_series hG hU.1 hU.2.2 hs hw
  have hrep := hU.1
  let L : H →L[ℂ] ℂ := (innerSL ℂ w).comp (π (NormedSpace.exp (t₀ • X)))
  let a : ℕ → ℂ := fun m => ((m.factorial : ℂ)⁻¹) * L ((dRep π X)^[m] v)
  have key : ∀ s : ℝ, |s| * mnorm X < r → HasSum (fun m : ℕ => (s : ℂ) ^ m * a m)
      (⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ) := by
    intro s hs'
    have h1 := hsum (s • X) ((GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 s X hX) (by rwa [mnorm_real_smul])
    have h2 := L.hasSum h1
    have e : ⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ = L (π (NormedSpace.exp (s • X)) v) := by
      have hc : Commute (t₀ • X) (s • X) := ((Commute.refl X).smul_left t₀).smul_right s
      rw [add_smul, Matrix.exp_add_of_commute _ _ hc, hrep.2 _ (hX t₀) _ (hX s)]
      rfl
    rw [e]
    convert h2 using 2 with m
    rw [iterate_real_smul hG hrep hs hX s m]
    simp only [a, map_smul, smul_eq_mul]
    ring
  let p : FormalMultilinearSeries ℝ ℝ ℂ := fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (a m)
  have hpa : ∀ (m : ℕ) (s : ℝ), p m (fun _ => s) = (s : ℂ) ^ m * a m := by
    intro m s
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hM : 0 < mnorm X + 1 := by linarith [mnorm_nonneg X]
  have hsmall : ∀ s : ℝ, |s| < r / (mnorm X + 1) → |s| * mnorm X < r := by
    intro s h
    rw [lt_div_iff₀ hM] at h
    nlinarith [abs_nonneg s]
  set ε : ℝ := r / (mnorm X + 1) with hε
  have hεpos : 0 < ε := div_pos hr hM
  have hrad : 0 < p.radius := by
    have hs0 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hS := (key (ε / 2) (hsmall _ hs0)).summable.norm
    let ρ : NNReal := ⟨ε / 2, by linarith⟩
    have hρ : (0 : NNReal) < ρ := by
      change (0 : ℝ) < ε / 2
      linarith
    have : (ρ : ENNReal) ≤ p.radius := by
      refine p.le_radius_of_summable_norm ?_
      refine hS.congr fun m => ?_
      have hρc : ((ρ : NNReal) : ℝ) = ε / 2 := rfl
      simp [p, hρc, ContinuousMultilinearMap.norm_mkPiRing, abs_of_pos hεpos, mul_comm]
    exact lt_of_lt_of_le (by exact_mod_cast hρ) this
  have han : AnalyticAt ℝ p.sum 0 := (p.hasFPowerSeriesOnBall hrad).analyticAt
  have han2 : AnalyticAt ℝ (fun t : ℝ => p.sum (t - t₀)) t₀ :=
    AnalyticAt.comp_of_eq (g := p.sum) (f := fun t : ℝ => t - t₀) han
      (analyticAt_id.sub analyticAt_const) (by simp)
  refine han2.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ hεpos] with t ht
  have hd : |t - t₀| < ε := by simpa [Real.dist_eq] using ht
  have h3 := key (t - t₀) (hsmall _ hd)
  rw [show t₀ + (t - t₀) = t by ring] at h3
  simp only [FormalMultilinearSeries.sum, hpa]
  exact h3.tsum_eq

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem dRep_realSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H} (hu : IsSmoothVec G π u) {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → Matrix (Fin n) (Fin n) ℂ) (ha : ∀ l, a l ∈ HCSS.lieOf G)
    (h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G) :
    (∑ l ∈ s, c l • a l) ∈ HCSS.lieOf G ∧
      dRep π (∑ l ∈ s, c l • a l) u = ∑ l ∈ s, c l • dRep π (a l) u := by
  classical
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, GlobalTheory.GKLie.dRep_zero π u⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 := hsm (c x) _ (ha x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep hu hu h1 ih.1).1, ih.2, GlobalTheory.GKLie.dRep_smul]

theorem dRep_vecSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (u : ι → H) (hu : ∀ l, IsSmoothVec G π (u l)) :
    IsSmoothVec G π (∑ l ∈ s, c l • u l) ∧
      dRep π X (∑ l ∈ s, c l • u l) = ∑ l ∈ s, c l • dRep π X (u l) := by
  classical
  obtain ⟨hadd, hsm, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [dRep]⟩
    exact ⟨fun _ => 0, contDiff_const, fun z _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : IsSmoothVec G π (c x • u x) := by
      rw [← Complex.coe_smul]
      exact hsm _ _ (hu x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep h1 ih.1 hX hX).2.1, ih.2, ← Complex.coe_smul,
      (GlobalTheory.T.derived_action_additive hG hrep (hu x) (hu x) hX hX).2.2, Complex.coe_smul]

theorem sumSquares_comm {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l)
    {v : H} (hv : IsSmoothVec G π v) :
    π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G := by
    simpa using (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 0 _ (hb i0)
  have hw : IsSmoothVec G π (π k v) := (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).2.2 k hk v hv
  have hT : ∀ m, IsSmoothVec G π (dRep π (b m) (π k v)) := fun m =>
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hw (hb m)).2
  have step : ∀ i, π k (dRep π (b i) (dRep π (b i) v)) =
      ∑ l, ∑ m, (O l i * O m i) • dRep π (b l) (dRep π (b m) (π k v)) := by
    intro i
    have hsm := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv (hb i)).2
    rw [GlobalTheory.T.derived_action_conjugation hG hrep hsm (hb i) hk, GlobalTheory.T.derived_action_conjugation hG hrep hv (hb i) hk, hkb i,
      (dRep_realSum hG hrep hw Finset.univ (fun m => O m i) b hb h0).2,
      (dRep_realSum hG hrep
        (dRep_vecSum hG hrep (hb i0) Finset.univ (fun m => O m i) _ hT).1
        Finset.univ (fun l => O l i) b hb h0).2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(dRep_vecSum hG hrep (hb l) Finset.univ (fun m => O m i) _ hT).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have hdelta : ∀ l m, ∑ i, O l i * O m i = (1 : Matrix (Fin d) (Fin d) ℝ) l m := fun l m => by
    rw [← hOO]
    simp [Matrix.mul_apply]

  rw [map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hdelta, Matrix.one_apply]
  simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.derived_action_commutator : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lie_basis_coordinate_growth_bound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i)) (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w → dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w) {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C) (hbound : ∀ l : List (Fin d), ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial), WordBound G π v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smooth_vector_hermitian_form_growth : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le <;> assumption)
end
