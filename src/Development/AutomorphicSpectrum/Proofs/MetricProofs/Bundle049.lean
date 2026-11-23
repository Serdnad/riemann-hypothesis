module

import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityOfBallPotential
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle090
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem ip_sum_right (R : RiemLat E g Λ) {k : ℕ} (x : Fin g → ℂ) (a : Fin k → ℂ)
    (u : Fin k → Fin g → ℂ) : R.ip x (∑ j, a j • u j) = ∑ j, a j * R.ip x (u j) := by
  simp only [RiemLat.ip, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem ip_sum_left (R : RiemLat E g Λ) {k : ℕ} (a : Fin k → ℂ) (u : Fin k → Fin g → ℂ)
    (y : Fin g → ℂ) : R.ip (∑ i, a i • u i) y = ∑ i, star (a i) * R.ip (u i) y := by
  simp only [RiemLat.ip, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem star_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip x y) = R.ip y x := by
  have h := R.herm
  simp only [RiemLat.ip]
  rw [← star_dotProduct_star, star_mulVec, star_star, h.eq, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

theorem gram_comb (R : RiemLat E g Λ) {k l : ℕ} (T : Matrix (Fin l) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    R.gram (fun a => ∑ i, T a i • u i) = T.map star * R.gram u * Tᵀ := by
  ext a a'
  simp only [RiemLat.gram, Matrix.of_apply, ip_sum_left, ip_sum_right, Matrix.mul_apply,
    Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_comb_det (R : RiemLat E g Λ) {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    (R.gram (fun a => ∑ i, T a i • u i)).det.re = Complex.normSq T.det * (R.gram u).det.re := by
  have h1 : (T.map star).det = star T.det := by
    have : T.map star = Tᴴᵀ := by ext; simp
    rw [this, det_transpose, det_conjTranspose]
  rw [gram_comb, det_mul, det_mul, det_transpose, h1]
  have h2 : star T.det * (R.gram u).det * T.det = (Complex.normSq T.det : ℂ) * (R.gram u).det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h2, Complex.re_ofReal_mul]

theorem sum_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → V) (v : Fin k → ℂ) :
    ∑ i, v i • ∑ j, T i j • u j = ∑ j, (v ᵥ* T) j • u j := by
  simp only [Finset.smul_sum, Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem det_ne_zero_of_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V)
    (hc : LinearIndependent ℂ fun i => ∑ j, T i j • u j) : T.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvT⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.1 hc v ?_ i
  rw [sum_comb, hvT]
  simp

theorem linearIndependent_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V) (hu : LinearIndependent ℂ u)
    (hT : T.det ≠ 0) : LinearIndependent ℂ fun i => ∑ j, T i j • u j := by
  refine Fintype.linearIndependent_iff.2 fun v hv i => ?_
  rw [sum_comb] at hv
  have h0 : v ᵥ* T = 0 := funext fun j => Fintype.linearIndependent_iff.1 hu _ hv j
  have := Matrix.eq_zero_of_vecMul_eq_zero hT h0
  simp [this]

theorem differentiableOn_det {n k : ℕ} {W : Set (Fin n → ℂ)}
    {M : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) W) :
    DifferentiableOn ℂ (fun t => (M t).det) W := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_smul ?_ _
  have h1 : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun t => ∏ i ∈ s, M t (σ i) i) W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact h1 _

theorem gram_det_re_pos (R : RiemLat E g Λ) {k : ℕ} (u : Fin k → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det.re := by
  apply LevelTowerAlt.gram_det_pos <;> assumption

theorem log_gram_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  intro E _ _ _ g Λ _ _ n m W R b c t₀ hW ht₀ hb hc hbi hcs hci
  have hinj : LinearMap.ker (Fintype.linearCombination ℂ fun i => b i t₀) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Fintype.linearCombination_apply] at hv
    exact funext (Fintype.linearIndependent_iff.1 (hbi t₀ ht₀) v hv)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hφb : ∀ i, φ (b i t₀) = Pi.single i 1 := by
    intro i
    have h1 := LinearMap.congr_fun hφ (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h1
  have hφd : ∀ u : (Fin n → ℂ) → Fin g → ℂ, DifferentiableOn ℂ u W →
      ∀ j, DifferentiableOn ℂ (fun t => φ (u t) j) W := by
    intro u hu j
    have h1 : DifferentiableOn ℂ (fun t => LinearMap.toContinuousLinearMap φ (u t)) W :=
      (LinearMap.toContinuousLinearMap φ).differentiable.comp_differentiableOn hu
    exact differentiableOn_pi.1 h1 j
  let Bm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (b i t) j
  let Cm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (c i t) j
  have hdB : DifferentiableOn ℂ (fun t => (Bm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hb i) j
  have hdC : DifferentiableOn ℂ (fun t => (Cm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hc i) j
  have hT : ∀ t ∈ W, ∃ T : Matrix (Fin m) (Fin m) ℂ,
      (∀ i, c i t = ∑ j, T i j • b j t) ∧ Cm t = T * Bm t := by
    intro t ht
    have h1 := fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hcs t ht i)
    choose T hT using h1
    refine ⟨Matrix.of T, fun i => (hT i).symm, ?_⟩
    ext i j

    simp only [Cm, Bm, Matrix.of_apply, Matrix.mul_apply, ← hT i, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hB0 : Bm t₀ = 1 := by
    ext i j
    simp only [Bm, Matrix.of_apply, hφb, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨T₀, hT₀, hCT₀⟩ := hT t₀ ht₀
  have hf₀ : (Cm t₀).det ≠ 0 := by
    rw [hCT₀, hB0, mul_one]
    have h1 : (fun i => c i t₀) = fun i => ∑ j, T₀ i j • b j t₀ := funext hT₀
    exact det_ne_zero_of_comb T₀ _ (h1 ▸ hci)
  let f₀ : ℂ := (Cm t₀).det
  let q : (Fin n → ℂ) → ℂ := fun t => (Cm t).det / (Bm t).det / f₀
  let V₁ : Set (Fin n → ℂ) := W ∩ (fun t => (Bm t).det) ⁻¹' {0}ᶜ
  have hV₁ : IsOpen V₁ := hdB.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hfd : DifferentiableOn ℂ (fun t => (Cm t).det / (Bm t).det) V₁ := by
    simp only [div_eq_mul_inv]
    have hinv : DifferentiableOn ℂ (fun t => ((Bm t).det)⁻¹) V₁ :=
      DifferentiableOn.fun_inv (hdB.mono Set.inter_subset_left) fun t ht => ht.2
    exact (hdC.mono Set.inter_subset_left).mul hinv
  have hqd : DifferentiableOn ℂ q V₁ := by
    have h1 := hfd.mul_const f₀⁻¹
    simpa only [q, div_eq_mul_inv] using h1
  let V : Set (Fin n → ℂ) := V₁ ∩ q ⁻¹' Metric.ball 1 1
  have hVo : IsOpen V := hqd.continuousOn.isOpen_inter_preimage hV₁ Metric.isOpen_ball
  have hq0 : q t₀ = 1 := by
    simp only [q, f₀, hB0, det_one, div_one]
    exact div_self hf₀
  have hslit : ∀ t ∈ V, q t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖q t - 1‖ < 1 := by simpa [dist_eq_norm] using ht.2
    have h2 := Complex.mem_slitPlane_of_norm_lt_one h1
    simpa using h2
  refine ⟨V, hVo, ⟨⟨ht₀, by simp [hB0]⟩, by simp [hq0]⟩, fun t ht => ht.1.1,
    fun t => 2 * Complex.log (q t) + 2 * ((Real.log ‖f₀‖ : ℝ) : ℂ), ?_, ?_⟩
  · exact (((hqd.mono Set.inter_subset_left).clog hslit).const_mul 2).add_const _
  · intro t ht
    obtain ⟨T, hTc, hCT⟩ := hT t ht.1.1
    have hBne : (Bm t).det ≠ 0 := ht.1.2
    have hqne : q t ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
    have hdet : T.det = q t * f₀ := by
      have h1 : (Cm t).det = T.det * (Bm t).det := by rw [hCT, det_mul]
      have hf₀' : f₀ ≠ 0 := hf₀
      show T.det = (Cm t).det / (Bm t).det / f₀ * f₀
      rw [div_mul_cancel₀ _ hf₀', h1, mul_div_cancel_right₀ _ hBne]
    have hTne : T.det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero hqne hf₀
    have hcf : (fun i => c i t) = fun i => ∑ j, T i j • b j t := funext hTc
    refine ⟨hcf ▸ linearIndependent_comb T _ (hbi t ht.1.1) hTne, ?_⟩
    have hpos := gram_det_re_pos (R t) _ (hbi t ht.1.1)
    rw [hcf, gram_comb_det, Real.log_mul (by simpa using hTne) hpos.ne', add_comm, hdet]
    congr 1
    have hf₀n : ‖f₀‖ ≠ 0 := norm_ne_zero_iff.2 hf₀
    have hqn : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 hqne
    rw [Complex.normSq_eq_norm_sq, norm_mul, Real.log_pow, Real.log_mul (mul_ne_zero hqn hf₀n |> left_ne_zero_of_mul) hf₀n]
    simp [Complex.add_re, Complex.mul_re, Complex.log_re]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem mem_ptsOver_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ ptsOver ℂ P := by
  refine ⟨hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  rw [eval_map] at h
  rw [aeval_def]
  simpa [algebraMap_int_eq] using h

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem global_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  intro K _ ι _ Ω _ y J e R σ S π hπ Eh hEh ε h1 h2
  choose dg dh G Hf hG hH hd hy hne using h1
  have loc := fun x₀ : R.X => GlobalTheory.T.metric_quotient_of_multihomog_pair K ι (mCoordIdeal y) J e R σ S π hπ Eh hEh (dg x₀) (dh x₀)
    (G x₀) (Hf x₀) (hG x₀) (hH x₀) (hd x₀)
    (fun x a b => h2 x _ _ _ _ (hG x₀) (hH x₀) (hd x₀) (hy x₀) a b) x₀ (hne x₀)
  choose V N C hVo hV hN hb using loc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover V (fun x _ => (hVo x).mem_nhds (hV x))
  refine ⟨1 / (2 * (1 + ∑ x₀ ∈ t, (N x₀ : ℝ))), ∑ x₀ ∈ t, |C x₀|, by positivity, ?_⟩
  intro x hx v hv hv0
  obtain ⟨x₀, hx₀t, hxV⟩ : ∃ x₀ ∈ t, x ∈ V x₀ := by simpa using ht.2 (Set.mem_univ x)
  have hz : R.lift x x ∈ ptsOver ℂ (mCoordIdeal y) :=
    mem_ptsOver_of_mem_mcPts (R.mem x x (R.mem_U x))
  obtain ⟨hHf, hbd⟩ := hb x₀ x hxV
  have hrep := (GlobalTheory.T.multihomogeneous_value_well_defined K ι Ω y ℂ Eh.a ε (R.lift x x) v hz hv).1 _ _ _ _
    (hG x₀) (hH x₀) (hd x₀) (hy x₀)
  have hGne : aeval (R.lift x x) (G x₀) ≠ (0 : ℂ) := by
    rw [hrep]; exact mul_ne_zero hv0 hHf
  have hbd' := hbd hx hGne
  have hval : (aeval (R.lift x x) (G x₀) : ℂ) / aeval (R.lift x x) (Hf x₀) = v := by
    rw [hrep]; exact mul_div_cancel_right₀ v hHf
  rw [hval] at hbd'
  have hr : 0 ≤ rW S.L S.s (π x) := by
    have h0 := S.norm_le (π x)
    have h1 : 0 < Real.exp 1 := Real.exp_pos 1
    unfold rW
    linarith
  have hNpos : (0 : ℝ) < N x₀ := by exact_mod_cast hN x₀
  have hsum : (N x₀ : ℝ) ≤ ∑ a ∈ t, (N a : ℝ) :=
    Finset.single_le_sum (f := fun a => (N a : ℝ)) (fun a _ => Nat.cast_nonneg _) hx₀t
  have hδ : 1 / (2 * (1 + ∑ a ∈ t, (N a : ℝ))) ≤ 1 / (2 * (N x₀ : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hC : C x₀ ≤ ∑ a ∈ t, |C a| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) hx₀t)
  have hmul := mul_le_mul_of_nonneg_right hδ hr
  linarith

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.monge_ampere_density_of_ball_potential : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), ∃ c : ℝ, 0 < c ∧ ∀ t ∈ ballDom q, maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = c * ballDens q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse

theorem isOpen_posDef_hermitian {X κ : Type} [TopologicalSpace X] [Fintype κ]
    (M : X → Matrix κ κ ℂ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : κ → ℂ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (κ → ℂ) => (dotProduct (star p.2) ((M p.1).mulVec p.2)).re) :=
    Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd))
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : κ → ℂ) 1,
      0 < (dotProduct (star v) ((M x).mulVec v)).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0)).1
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul] at h1
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  have hre : 0 < (dotProduct (star v) ((M x).mulVec v)).re :=
    (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)
  have hstar : star (dotProduct (star v) ((M x).mulVec v)) = dotProduct (star v) ((M x).mulVec v) := by
    conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, (hs x).eq, ← Matrix.dotProduct_mulVec]
  have him : (dotProduct (star v) ((M x).mulVec v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
  exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  have hset : ballDom q = ⋂ τ, {t | (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef} := by
    ext t
    simp [ballDom]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => isOpen_posDef_hermitian _ ?_ fun t => ?_
  · have hm : Continuous fun t : Fin n → ℂ => ballMat q t τ :=
      continuous_matrix fun a b => continuous_apply _
    exact continuous_const.sub (hm.matrix_conjTranspose.matrix_mul hm)
  · exact (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)

theorem exists_inverse : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  intro Ψ _ j j' n q Z G hZ hbij _ _
  have hJ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  obtain ⟨-, Y, hY, hYZ⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof hJ n _ Z
    (isOpen_ballDom q) hZ hbij.injOn
  rw [hbij.image_eq] at hY
  refine ⟨Y, hY, fun t ht => ?_⟩
  obtain ⟨s, hs, hst⟩ := hbij.surjOn ht
  have hYt : Y t = s := by
    rw [← hst]
    exact hYZ s hs
  exact ⟨hYt ▸ hs, by rw [hYt, hst], hYZ t ht⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2), (∀ (L : Fin (d + 2) → HermLine ι) (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 0) (Q.v 0) (L j) (L' j)) → IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) = (N.a (Q.κ 1 k₀) : ℝ) * II K ι P (d + 2) L) ∧ ∀ (L : Fin (d + 3) → HermLine ι) (L' : Fin (d + 3) → HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 1) (Q.v 1) (L j) (L' j)) → II Q.KW Q.ιW Q.PW (d + 3) L' = 0 := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q
  obtain ⟨hFam, -, -, hCM⟩ := hII
  letI := Q.finKW
  letI := Q.finιW
  refine ⟨?_, ?_⟩
  · classical
    intro L L' N hL hLL' hN
    haveI : Q.PW.IsPrime := Q.arithW.2.1.1
    let G := GroundTheory.Heights₂.Heights.Inter.genFibreOf (Q.v 0) Q.PW
    let b : FibreBlock (Q.κ 0) := ⟨Q.κ 1 k₀, Q.new⟩
    have hb : ∀ c : FibreBlock (Q.κ 0), c = b := by
      intro c
      apply Subtype.ext
      rcases Q.all c.1 with h | h
      · exact absurd h c.2
      · exact h
    let e : Unit ≃ FibreBlock (Q.κ 0) :=
      { toFun := fun _ => b, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun c => (hb c).symm }
    let hq : (u : Unit) → Q.ιW (Q.κ 1 k₀) ≃ fibreIdx Q.ιW (Q.κ 0) (e u) := fun _ => Equiv.refl _
    let I₀ : IFamily G.Φ (fun _ : Unit => Q.ιW (Q.κ 1 k₀)) := fun V _ Ls => NumbersDVR.intNum G.Φ V Ls
    have hI₀ : IsFieldIntersection I₀ := NumbersDVR.IntNumIsFieldIntersection.full G.Φ Unit _
    let J := Targets.Relabel.pullFamily e hq I₀
    have hJ : IsFieldIntersection J := Targets.Relabel.isFieldIntersection_pull e hq hI₀
    have hP := hIn.2.2.2.1.1 II hFam K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G J L L' (fun _ => N)
      (Q.block 0) Q.arithW (by rw [Q.image 0]; exact Q.arithY) hJ hL hLL' (fun _ => hN)
    rw [Fin.append_right_eq_snoc, Q.image 0] at hP
    rw [hP]
    congr 1
    obtain ⟨V, hV⟩ := Targets.Relabel.exists_map_eq e hq (fibreIdeal (Q.κ 0) G)
    have hVd : IsProjVarF V 1 := by
      rw [← Targets.Relabel.isProjVarF_map_iff e hq, ← hV]
      exact hIn.2.2.2.1.2.2 K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G (Q.block 0) Q.arithW
        (by rw [Q.image 0]; exact Q.arithY)
    have hVs : ∃ S : Set (MRingOver G.Φ fun _ : Unit => Q.ιW (Q.κ 1 k₀)),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ V = Ideal.span S := by
      obtain ⟨T, hT, hTs⟩ := Q.fibre_line G
      refine ⟨(Targets.Relabel.ringEquiv G.Φ e hq).symm '' T, ?_, ?_⟩
      · rintro f ⟨g, hg, rfl⟩
        exact Targets.Relabel.isMultiHomog_symm e hq (hT g hg)
      · rw [← Ideal.map_span, ← hTs, hV, Ideal.map_symm, Targets.Relabel.comap_map]
    have hL1 := hIn.2.2.2.1.2.1 G.Φ _ V I₀ hVd hVs hI₀ (N.a (Q.κ 1 k₀))
    have key : (fun j : Fin 1 => fibreDeg (Q.κ 0) N.a ∘ e) = ![fun _ : Unit => N.a (Q.κ 1 k₀)] := by
      funext j u
      fin_cases j
      rfl
    show ((I₀ (Ideal.comap (Targets.Relabel.ringEquiv G.Φ e hq) (fibreIdeal (Q.κ 0) G)) 1
      fun j => fibreDeg (Q.κ 0) N.a ∘ e : ℤ) : ℝ) = _
    rw [hV, Targets.Relabel.comap_map, key, hL1]
  · intro L L' hL hLL'
    have h := hCM K ι Q.KW Q.ιW (Q.κ 1) (Q.v 1) Q.PW (d + 2) (d + 3) 0 L L' Fin.elim0 (Q.block 1)
      Q.arithW (by rw [Q.image 1]; exact Q.arithY) (by omega) hL hLL' (fun j => j.elim0)
    simpa [Fin.append_elim0] using h
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem linearIndependent_of_isUnit_gram_det :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (d : Fin m → Fin g → ℂ),
      IsUnit (R.gram d).det → LinearIndependent ℂ d := by
  intro E _ _ _ g Λ _ _ R m d hdet
  rw [Fintype.linearIndependent_iff]
  intro x hx
  have hmul : (R.gram d) *ᵥ x = 0 := by
    funext a
    have hsum : (∑ b, x b • d b) ⬝ᵥ (R.Hm *ᵥ star (d a)) = 0 := by
      rw [hx, zero_dotProduct]
    rw [sum_dotProduct] at hsum
    simp only [smul_dotProduct, smul_eq_mul] at hsum
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hsum ⊢
    rw [← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mulVec, dotProduct]
    rw [mul_comm]
  have hx0 : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero hmul
  intro i
  rw [hx0, Pi.zero_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
