module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import GroundTheory.AutomorphicForms.Bundle017
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle276
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle003
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExists
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.SetTheory.Cardinal.Free
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def UBnd {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ i, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖f i (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

structure UFam {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  left : ∀ i, IsLeftInvariant (f i)
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ i (g : AdelicGLn.AdelicGL K n) (u : U),
      f i (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = f i g

abbrev mat (y : archGroup K n) : ArchMatrix K n := ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)

structure Ker [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ) : Prop where
  cont : Continuous β
  cpt : HasCompactSupport β
  nonneg : ∀ y, 0 ≤ β y
  mass : ∫ y, β y ∂ν = 1
  lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ y y', |β y - β y'| ≤ L * ‖mat y - mat y'‖

def sm [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ y, (β y : ℂ) * f (x * infEmb K n y) ∂ν

theorem continuous_mat : Continuous (mat : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_ball {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
  have hemb : IsEmbedding (fun y : archGroup K n => mat y) :=
    Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)
  have hsub : Metric.closedBall (1 : ArchMatrix K n) ρ ⊆ Set.range (fun y : archGroup K n => mat y) := by
    intro a ha
    have h1 : ‖1 - a‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using ha) hρ
    refine ⟨⟨Units.oneSub (1 - a) h1, Subgroup.mem_top _⟩, ?_⟩
    simp [mat]
  have := (hemb.isInducing.isCompact_preimage_iff hsub).2 (isCompact_closedBall (1 : ArchMatrix K n) ρ)
  convert this using 1
  ext y
  simp [dist_eq_norm]

theorem tent_lip {A : Type*} [SeminormedAddCommGroup A] {ρ : ℝ} (hρ0 : 0 < ρ) (a b e : A) :
    |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ ρ⁻¹ * ‖a - b‖ := by
  have h1 : |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ |(1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ)| := by
    simp only [max_comm (0 : ℝ)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ) = ρ⁻¹ * (‖b - e‖ - ‖a - e‖) := by
    field_simp
    ring
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hρ0)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ0.le))
  have h3 := abs_norm_sub_norm_le (b - e) (a - e)
  rw [sub_sub_sub_cancel_right] at h3
  rw [norm_sub_rev a b]
  exact h3

theorem exists_ker [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {U : Set (archGroup K n)} (hU : U ∈ 𝓝 1) :
    ∃ β, Ker ν β ∧ tsupport β ⊆ U := by
  have hc : ContinuousAt (fun y : archGroup K n => mat y) 1 := continuous_mat.continuousAt

  have hb : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} ⊆ U := by
    have hemb : IsInducing (fun y : archGroup K n => mat y) :=
      (Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)).isInducing
    rw [hemb.nhds_eq_comap, mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    have h1 : mat (1 : archGroup K n) = 1 := rfl
    rw [h1] at ht
    obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
    refine ⟨min e (1 / 2), by positivity, by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun y hy => hsub ?_⟩
    apply hball
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hy (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hρU⟩ := hb
  set β₀ : archGroup K n → ℝ := fun y => max 0 (1 - ‖mat y - 1‖ / ρ) with hβ₀
  have hβc : Continuous β₀ :=
    continuous_const.max (continuous_const.sub ((continuous_mat.sub continuous_const).norm.div_const _))
  have hsupp : Function.support β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
    intro y hy
    by_contra h
    apply hy
    have h' : ρ < ‖mat y - 1‖ := not_le.1 h
    have : 1 < ‖mat y - 1‖ / ρ := (one_lt_div hρ0).2 h'
    exact max_eq_left (by linarith)
  have hclosed : IsClosed {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} :=
    isClosed_le (continuous_mat.sub continuous_const).norm continuous_const
  have hts : tsupport β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := closure_minimal hsupp hclosed
  have hcs : HasCompactSupport β₀ := (isCompact_ball hρ1).of_isClosed_subset (isClosed_tsupport _) hts
  have hnn : ∀ y, 0 ≤ β₀ y := fun y => le_max_left _ _
  have hpos : 0 < ∫ y, β₀ y ∂ν := by
    refine hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (x := 1) ?_
    have : β₀ 1 = 1 := by simp [hβ₀, mat]
    rw [this]; exact one_ne_zero
  set c := ∫ y, β₀ y ∂ν with hcdef
  have hcpos : 0 ≤ c⁻¹ := inv_nonneg.2 hpos.le
  have hk : Ker ν (fun y => c⁻¹ * β₀ y) := by
    refine { cont := continuous_const.mul hβc
             cpt := hcs.mul_left
             nonneg := fun y => mul_nonneg hcpos (hnn y)
             mass := ?_
             lip := ⟨c⁻¹ * ρ⁻¹, mul_nonneg hcpos (inv_nonneg.2 hρ0.le), fun y y' => ?_⟩ }
    · rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hpos.ne']
    · rw [← mul_sub, abs_mul, abs_of_nonneg hcpos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcpos
      exact tent_lip hρ0 _ _ _
  exact ⟨_, hk, (tsupport_mul_subset_right (f := fun _ => c⁻¹) (g := β₀)).trans (hts.trans hρU)⟩

end GlobalTheory.CompanionTheory.Conc

end
end

section

noncomputable section

open Polynomial
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.AnBoot

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem sr_eq_zero (x : Fin n → ℝ) {r : ℕ} (h : ¬ (0 < r ∧ r < n)) : sr x r = 0 := by
  unfold sr
  rw [dite_eq_right h]

theorem bnd_mono {φ : AdelicGLn.AdelicGL K n → ℂ} {m m' : ℕ → ℝ}
    (hm : ∀ r, 0 < r → r < n → m r ≤ m' r) (h : Bnd φ m) : Bnd φ m' := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := h ω hω hB t₀ Q hQ
  refine ⟨max C 0 * Real.exp (∑ r ∈ Finset.range n,
    (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩
  intro b hb x hx q hq
  have h1 := hC b hb x hx q hq
  have hs : ∑ r ∈ Finset.range n, m r * sr x r ≤
      (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
        ∑ r ∈ Finset.range n, m' r * sr x r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 0 < r ∧ r < n
    · rw [if_pos hr]
      have := mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))
      nlinarith
    · rw [if_neg hr, sr_eq_zero x hr]
      simp
  calc ‖φ (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := h1
    _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp ((∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
            ∑ r ∈ Finset.range n, m' r * sr x r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hs) (le_max_right _ _)
    _ = max C 0 * Real.exp (∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) *
            Real.exp (∑ r ∈ Finset.range n, m' r * sr x r) := by
        rw [Real.exp_add, mul_assoc]

theorem bnd_add {f g : AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (hf : Bnd f m) (hg : Bnd g m) :
    Bnd (fun y => f y + g y) m := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := hf ω hω hB t₀ Q hQ
  obtain ⟨D, hD⟩ := hg ω hω hB t₀ Q hQ
  refine ⟨C + D, fun b hb x hx q hq => ?_⟩
  have h1 := hC b hb x hx q hq
  have h2 := hD b hb x hx q hq
  calc ‖f (b * tor K x * q) + g (b * tor K x * q)‖
      ≤ ‖f (b * tor K x * q)‖ + ‖g (b * tor K x * q)‖ := norm_add_le _ _
    _ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) +
          D * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := add_le_add h1 h2
    _ = (C + D) * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := by ring

theorem update_le_update (m : ℕ → ℝ) (r : ℕ) {a b : ℝ} (h : a ≤ b) (s : ℕ) :
    Function.update m r a s ≤ Function.update m r b s := by
  by_cases hs : s = r
  · subst hs
    simpa using h
  · simp [Function.update_of_ne hs]

theorem bnd_step (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r (max (m r - 1) κ)) := by
  have a : Bnd (fun g => φ g - ctn r φ g) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_left _ _) s) (hD K n φ m r h0 h1 hφ h)
  have b : Bnd (ctn r φ) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_right _ _) s)
      (hC K n φ m r p κ h0 h1 hφ h hp hk hz)
  have c := bnd_add a b
  simpa using c

theorem bnd_iter (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) (k : ℕ) :
    Bnd φ (Function.update m r (max (m r - k) κ)) := by
  induction k with
  | zero =>
    refine bnd_mono (fun s _ _ => ?_) h
    by_cases hs : s = r
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | succ k ih =>
    have := bnd_step hD hC hφ h0 h1 hp hk hz ih
    rw [Function.update_self, Function.update_idem] at this
    refine bnd_mono (fun s _ _ => update_le_update m r ?_ s) this
    push_cast
    refine max_le ?_ (le_max_right _ _)
    rcases le_total (m r - k) κ with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h']
      exact le_trans (by linarith) (le_max_left _ _)

theorem bnd_one (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r κ) := by
  obtain ⟨k, hk'⟩ := exists_nat_ge (m r - κ)
  have := bnd_iter hD hC hφ h0 h1 hp hk hz h k
  rwa [max_eq_right (by linarith)] at this

theorem bootGlue : BootGlue := by
  intro hD hC K _ _ n φ M κ hφ hM hp
  have key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) →
      Bnd φ (fun r => if r ∈ s then κ r else M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hM
    | insert a s ha ih =>
      intro hs
      have h' := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      obtain ⟨h0, h1⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨p, hpm, hpk, hpz⟩ := hp a h0 h1
      have := bnd_one hD hC hφ h0 h1 hpm hpk hpz h'
      refine bnd_mono (fun r _ _ => le_of_eq ?_) this
      by_cases hr : r = a
      · subst hr
        simp
      · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
  refine bnd_mono (fun r h0 h1 => le_of_eq ?_) (key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr))
  simp [h0, h1]

end GlobalTheory.CompanionTheory.AnBoot

end
end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LatCount

theorem countable_subgroupClosure {G : Type*} [Group G] (s : Set G) (hs : s.Countable) :
    ((Subgroup.closure s : Subgroup G) : Set G).Countable := by
  open scoped Pointwise in
  have ht : (s ∪ s⁻¹).Countable := hs.union (by simpa using hs.image (·⁻¹))
  haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  have h : ((Subgroup.closure s : Subgroup G) : Set G)
      = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G)) := by
    have h1 : ((Subgroup.closure s : Subgroup G) : Set G)
        = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G) := by
      rw [← Subgroup.closure_toSubmonoid]; rfl
    rw [h1, Submonoid.closure_eq_mrange]; rfl
  rw [h]
  exact Set.countable_range _

theorem countable_lat (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Countable (PositivityTheory.Rg.Rs.An.lat K n) := by
  haveI : Countable K := GroundTheory.Global.countable_numberField K
  haveI : Countable (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (Countable (Fin n → Fin n → K))
  haveI : Countable (GL (Fin n) K) := Units.val_injective.countable
  have h1 : (Set.range (AdelicGLn.diagonal K n)).Countable := Set.countable_range _
  have h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable := by
    rw [Subgroup.coe_zpowers]
    exact Set.countable_range _
  have h3 := countable_subgroupClosure
    ((Set.range (AdelicGLn.diagonal K n)) ∪
      ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)
  have h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure
      ((Set.range (AdelicGLn.diagonal K n)) ∪
        ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
        Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) := by
    unfold PositivityTheory.Rg.Rs.An.lat
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [h4]
  exact h3.to_subtype

end GlobalTheory.CompanionTheory.LatCount
end

section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem detModule_tor_one (K : Type) [Field K] [NumberField K] (n : ℕ) :
    (detModule K n (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : ℝ)
      = Real.exp ((n : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  unfold PositivityTheory.Rg.Rs.An.tor
  rw [CuspidalSpectrum.detModule_diagUnits_posIdele]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_nat_mul]
  simp

open GroundTheory.Automorphic.Reduction in
theorem detModule_lhs (K : Type) [Field K] [NumberField K] (n : ℕ) (γ₀ : GL (Fin n) K) (m : ℤ) :
    (detModule K n (AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m) : ℝ)
      = Real.exp ((m : ℝ) * ((n : ℝ) * (Module.finrank ℚ K : ℝ))) := by
  have h1 : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
    mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)
  rw [map_mul, h1, one_mul, map_zpow]
  have hv : ∀ (s : {r : ℝ // 0 < r}) (k : ℤ), ((s ^ k : {r : ℝ // 0 < r}) : ℝ) = (s : ℝ) ^ k := by
    intro s k
    have hinv : ∀ u : {r : ℝ // 0 < r}, ((u⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ)⁻¹ := by
      intro u
      have h := congrArg Subtype.val (mul_inv_cancel u)
      rw [Positive.val_mul, Positive.val_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hpow : ∀ (u : {r : ℝ // 0 < r}) (j : ℕ), ((u ^ j : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ) ^ j := by
      intro u j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, pow_succ, Positive.val_mul, ih]
    cases k with
    | ofNat j => simp only [Int.ofNat_eq_natCast, zpow_natCast, hpow]
    | negSucc j => rw [zpow_negSucc, zpow_negSucc, hinv, hpow]
  rw [hv, detModule_tor_one, ← Real.rpow_intCast, ← Real.exp_mul, mul_comm]

open GroundTheory.Automorphic.Reduction in
theorem detModule_rhs (K : Type) [Field K] [NumberField K] (n r : ℕ) (X Y : UPos n r → 𝔸[K])
    (a q : AdelicGLn.AdelicGL K n) :
    detModule K n (unipGL X * a * q * a⁻¹ * (unipGL Y)⁻¹) = detModule K n q := by
  have h1 : detModule K n (unipGL X) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL X)
  have h2 : detModule K n (unipGL Y) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL Y)
  simp only [map_mul, map_inv, h1, h2, inv_one, one_mul, mul_one]
  rw [mul_comm (detModule K n a), mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.CompanionTheory.Latexp

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem exponent_mem_finset : ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < n → ∀ (Q : Set (AdelicGLn.AdelicGL K n)), IsCompact Q → ∃ M : Finset ℤ, ∀ (t : ℝ) (X Y : UPos n r → 𝔸[K]), ∀ q ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ), AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m = unipGL X * PositivityTheory.Rg.Rs.An.aR K n r t * q * (PositivityTheory.Rg.Rs.An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ → m ∈ M := by
  intro K _ _ n r hn Q hQ
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨a, b, ha, -, hab⟩ := Reduction.exists_pos_bounds hQ hdc (fun g _ => (detModule K n g).2)
  have hN : 0 < (n : ℝ) * (Module.finrank ℚ K : ℝ) :=
    mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 Module.finrank_pos)
  set N : ℝ := (n : ℝ) * (Module.finrank ℚ K : ℝ) with hNdef
  refine ⟨Finset.Icc ⌊Real.log a / N⌋ ⌈Real.log b / N⌉, ?_⟩
  intro t X Y q hq γ₀ m h
  have h1 := congrArg (fun g => (detModule K n g : ℝ)) h
  beta_reduce at h1
  rw [detModule_lhs, detModule_rhs] at h1
  obtain ⟨h2, h3⟩ := hab q hq
  rw [← h1] at h2 h3
  have h4 : Real.log a ≤ (m : ℝ) * N := (Real.log_le_iff_le_exp ha).2 h2
  have h5 : (m : ℝ) * N ≤ Real.log b := by
    have hb : 0 < b := lt_of_lt_of_le (Real.exp_pos _) h3
    exact (Real.le_log_iff_exp_le hb).2 h3
  rw [Finset.mem_Icc]
  constructor
  · have : Real.log a / N ≤ (m : ℝ) := (div_le_iff₀ hN).2 h4
    exact Int.cast_le.1 ((Int.floor_le _).trans this)
  · have : (m : ℝ) ≤ Real.log b / N := (le_div_iff₀ hN).2 h5
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))
end GlobalTheory.CompanionTheory.Latexp
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem chartDivisorCompare : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.proof GlobalTheory.T.segre_chart_integral_holds
    GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints.proof
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength

end GlobalTheory.CompanionTheory.Ar
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.generalized_eigenvector_exists : ∀ (Λ : Type) [Group Λ] (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Λ M), (∀ l l', ρ l * ρ l' = ρ l' * ρ l) → ∀ (U : ℕ → Subgroup Λ), Antitone U → (∀ m m', m ≤ m' → ∀ u ∈ U m, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ U m') → (∀ w : M, ∃ m, ∀ u ∈ U m, ρ u w = w) → (∀ m, FiniteDimensional ℂ ↥(⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))) → ∀ (ξ : Λ →* ℂ) (v : M), v ≠ 0 → (∀ l, v ∈ Module.End.maxGenEigenspace (ρ l) (ξ l)) → ∃ f : M →ₗ[ℂ] ℂ, f ≠ 0 ∧ ∀ l w, f (ρ l w) = ξ l * f w := by
  first | exact @GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | exact GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | (intros; apply GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character <;> assumption)
end
