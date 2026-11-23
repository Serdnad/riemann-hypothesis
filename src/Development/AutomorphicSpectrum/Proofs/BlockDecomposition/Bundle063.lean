module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOne
public import Mathlib.Data.Finset.Powerset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxIntegralSmallBall
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

theorem eventually_slice_eq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by
  obtain ⟨hF, hc⟩ := mem_SB_iff.1 F.2
  have hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ)) := hc.isCompact.image continuous_snd
  have hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)} := by
    have h2 : IsLocallyConstant
        (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2)) :=
      hF.sub (hF.comp_continuous (by fun_prop))
    have h3 := h2.isOpen_fiber 0
    simpa [Set.preimage, sub_eq_zero] using h3
  obtain ⟨U, V, hU, -, haU, hKV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := a₀)) hK
    hopen (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = a₀ := ha
      subst ha'
      rfl)
  filter_upwards [hU.mem_nhds (haU rfl)] with a ha b
  by_cases hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)
  · exact hUV (Set.mk_mem_prod ha (hKV hb))
  · have h1 : (a, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    have h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem integral_mem_SB : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
    [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B)
    [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B),
    (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  intro A B _ _ _ _ _ _ _ _ _ _ μ _ w _ F
  obtain ⟨-, hc⟩ := mem_SB_iff.1 F.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    filter_upwards [eventually_slice_eq F a₀] with a ha
    simp only [ha]
  · refine HasCompactSupport.intro (hc.isCompact.image continuous_fst) ?_
    intro a ha
    have h0 : ∀ b, (F : A × B → ℂ) (a, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
    simp only [h0, zero_mul, integral_zero]

end GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Filtration

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

noncomputable def descend (f : π.IntertwiningMap σ) (B A : Subrepresentation π)
    (h : ∀ v ∈ A.toSubmodule, f v = 0) : (subQuot B A).IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (f.toLinearMap ∘ₗ B.toSubmodule.subtype) (fun v hv => h v.1 hv)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact f.isIntertwining _ _ g v.1

theorem vanish_step (f : π.IntertwiningMap σ) {A B : Subrepresentation π}
    (hA : ∀ v ∈ A.toSubmodule, f v = 0)
    (hz : ∀ φ : (subQuot B A).IntertwiningMap σ, φ.toLinearMap = 0) :
    ∀ v ∈ B.toSubmodule, f v = 0 := by
  intro v hv
  have h1 := LinearMap.congr_fun (hz (GlobalTheory.CompanionTheory.Filtration.descend f B A hA)) (Submodule.Quotient.mk ⟨v, hv⟩)
  have h2 : (GlobalTheory.CompanionTheory.Filtration.descend f B A hA).toLinearMap (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    first
      | rfl
  rw [← h2, h1, LinearMap.zero_apply]

theorem vanish_climb {N : ℕ} (S : Fin (N + 1) → Subrepresentation π) (f : π.IntertwiningMap σ)
    (lo : ℕ) (hlo : lo < N + 1)
    (h0 : ∀ v ∈ (S ⟨lo, hlo⟩).toSubmodule, f v = 0) (hi : ℕ) (hle : lo ≤ hi) :
    ∀ (hhi : hi < N + 1),
      (∀ t : Fin N, lo ≤ t.val → t.val < hi →
        ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
      ∀ v ∈ (S ⟨hi, hhi⟩).toSubmodule, f v = 0 := by
  induction hi, hle using Nat.le_induction with
  | base =>
    intro _ _
    exact h0
  | succ k hk ih =>
    intro hhi hz
    have hkN : k < N := Nat.lt_of_succ_lt_succ hhi
    have ih' := ih (Nat.lt_succ_of_lt hkN)
      (fun t h1 h2 => hz t h1 (Nat.lt_succ_of_lt h2))
    exact GlobalTheory.CompanionTheory.Filtration.vanish_step f
      (A := S (⟨k, hkN⟩ : Fin N).castSucc) (B := S (⟨k, hkN⟩ : Fin N).succ) ih'
      (hz ⟨k, hkN⟩ hk (Nat.lt_succ_self k))

theorem intertwining_proportional :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ)
      (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
      ∀ t₀ : Fin N,
        (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) →
        (∀ t : Fin N, t ≠ t₀ →
          ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
        ∀ φ ψ : π.IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  intro G V W _ _ _ _ _ π σ N S _ hS0 hST t₀ hmult hzero φ ψ
  have happ : ∀ (f : π.IntertwiningMap σ) (v : V), f.toLinearMap v = f v :=
    fun f v => Representation.IntertwiningMap.toLinearMap_apply π σ f v
  have hbot : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S ⟨0, Nat.succ_pos N⟩).toSubmodule, f v = 0 := by
    intro f v hv
    have e0 : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by
      first
        | exact Fin.mk_zero
    rw [e0, hS0] at hv
    have hv0 : v = 0 := by
      first
        | exact (Submodule.mem_bot ℂ).1 hv
    rw [hv0, ← happ, map_zero]
  have htop : ∀ v : V, v ∈ (S (Fin.last N)).toSubmodule := by
    intro v
    rw [hST]
    first
      | exact Submodule.mem_top
  have hlow : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f =>
    GlobalTheory.CompanionTheory.Filtration.vanish_climb S f 0 (Nat.succ_pos N) (hbot f)
      t₀.val (Nat.zero_le _) (Nat.lt_succ_of_lt t₀.isLt)
      (fun t _ ht => hzero t (by rintro rfl; exact lt_irrefl _ ht))
  have hup : ∀ f : π.IntertwiningMap σ, (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → ∀ v, f v = 0 := by
    intro f hf v
    have h := GlobalTheory.CompanionTheory.Filtration.vanish_climb S f (t₀.val + 1)
      (Nat.succ_lt_succ t₀.isLt) hf N t₀.isLt (Nat.lt_succ_self N)
      (fun t h1 _ => hzero t (by rintro rfl; exact Nat.not_succ_le_self _ h1))
    exact h v (htop v)
  have hdesc : ∀ (f : π.IntertwiningMap σ) (hf : ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0) (v : V)
      (hv : v ∈ (S t₀.succ).toSubmodule),
      (GlobalTheory.CompanionTheory.Filtration.descend f (S t₀.succ) (S t₀.castSucc) hf).toLinearMap
        (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    intro f hf v hv
    first
      | rfl
  rcases hmult (GlobalTheory.CompanionTheory.Filtration.descend φ (S t₀.succ) (S t₀.castSucc) (hlow φ))
      (GlobalTheory.CompanionTheory.Filtration.descend ψ (S t₀.succ) (S t₀.castSucc) (hlow ψ)) with h | ⟨c, hc⟩
  · left
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply, happ]
    refine hup φ ?_ v
    intro w hw
    rw [← hdesc φ (hlow φ) w hw, h, LinearMap.zero_apply]
  · right
    refine ⟨c, ?_⟩
    let χ : π.IntertwiningMap σ :=
      { toLinearMap := ψ.toLinearMap - c • φ.toLinearMap
        isIntertwining' := fun g => by
          first
            | rw [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.comp_smul,
                ψ.isIntertwining' g, φ.isIntertwining' g]
            | (ext v
               have h1 := LinearMap.congr_fun (ψ.isIntertwining' g) v
               have h2 := LinearMap.congr_fun (φ.isIntertwining' g) v
               simp only [LinearMap.comp_apply] at h1 h2
               simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2,
                 map_sub, map_smul]) }
    have hχ : ∀ v, χ v = ψ v - c • φ v := by
      intro v
      rw [← happ, ← happ, ← happ]
      rfl
    have hχS : ∀ v ∈ (S t₀.succ).toSubmodule, χ v = 0 := by
      intro v hv
      rw [hχ, ← hdesc ψ (hlow ψ) v hv, ← hdesc φ (hlow φ) v hv, hc, LinearMap.smul_apply, sub_self]
    apply LinearMap.ext
    intro v
    have h := hup χ hχS v
    rw [hχ, sub_eq_zero] at h
    rw [LinearMap.smul_apply, happ, happ]
    exact h

end GlobalTheory.CompanionTheory.Filtration
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.score_tZero_eq_level_count : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n, score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.score_tZero_level | exact GlobalTheory.CompanionTheory.CoefId.score_tZero_level | (intros; apply GlobalTheory.CompanionTheory.CoefId.score_tZero_level <;> assumption)
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.score_rigidity_perm_eq_one : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ L : Fin n → ℤ, StrictAnti L → (∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) → (∀ a b, lev a = lev b → score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ)) → ∀ (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)), T ⊆ prs n → (∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) → σ = 1 ∧ T = tZero lev := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | exact GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | (intros; apply GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique <;> assumption)
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score : ∀ {n : ℕ} (z : Fin n → ℂ), ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | exact GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score <;> assumption)
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.vandermonde_squares : ∀ {n : ℕ} (z : Fin n → ℂ), (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det = (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | exact GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | (intros; apply GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq <;> assumption)
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz <;> assumption)
end

section

open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.quadratic_box_volume_bound : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound <;> assumption)
end

section

open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.quadratic_box_integral_small_ball : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a → ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0, (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) → ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.average_invariant_right_translation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | exact GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_rank_lower_left_eq_lower_right : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | exact GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank <;> assumption)
end
