module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem l1_shift_single_le {n : ℕ} (ω Λ : Fin n → ℝ) (t e : ℝ) (he : |e| ≤ 1) (c : Fin n)
    (h : ∑ a, |ω a - Λ a| ≤ t) :
    ∑ a, |(ω a + if a = c then e else 0) - Λ a| ≤ t + 1 := by
  have h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0 := by
    intro a
    split_ifs
    · have : ω a + e - Λ a = (ω a - Λ a) + e := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith)
    · simp
  calc _ ≤ ∑ a, (|ω a - Λ a| + if a = c then 1 else 0) := Finset.sum_le_sum fun a _ => h1 a
    _ = ∑ a, |ω a - Λ a| + 1 := by rw [Finset.sum_add_distrib]; simp
    _ ≤ t + 1 := by linarith

theorem algTens_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  intro M _ _ n ε E N _ _ F io pr Λ t hT
  refine ⟨fun w hw s c => ?_, fun s y hy d => ?_⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0,
        l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩
      rw [← hT.pr_comm, ← map_smul]
      congr 1
      ext i
      by_cases hi : i = c
      · subst hi
        by_cases ha : a = i
        · subst ha
          simp [dualTens, hx a, add_smul, sub_eq_add_neg]
        · have : ¬ i = a := fun h => ha h.symm
          simp [dualTens, hx a, ha, this]
      · by_cases ha : i = a
        · subst ha
          simp [dualTens, hi]
        · simp [dualTens, hi, ha]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add (f := _)]; exact add_mem hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0,
        l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩
      have h := congrFun (hT.io_comm s a a x) d
      rw [hx a, map_smul] at h
      simp only [dualTens, Pi.smul_apply] at h
      rw [eq_sub_iff_add_eq] at h
      rw [← h]
      by_cases ha : a = d
      · subst ha
        simp [add_smul]
      · have : ¬ d = a := fun h => ha h.symm
        simp [ha, this]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, Pi.smul_apply]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.WtOrth

theorem inner_eq_zero_of_ne {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right] at h
  simp only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h
  have h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha
  · exact h3

theorem exists_decomp {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by
  classical
  unfold WtNear at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ω, h1, h2⟩ := hy
    refine ⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩
    · intro ω' h
      rw [Finset.mem_singleton.mp h]; exact h1
    · intro ω'
      by_cases h : ω' = ω
      · simp only [h, if_true]; exact h2
      · intro a; simp [h]
    · intro ω' h
      have : ω' ≠ ω := fun e => h (Finset.mem_singleton.mpr e)
      simp [this]
    · simp
  | zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    obtain ⟨T', x', h1', h2', h3', h4'⟩ := hz
    refine ⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩
    · intro ω h
      rcases Finset.mem_union.mp h with h | h
      · exact h1 ω h
      · exact h1' ω h
    · intro ω a
      simp only [map_add (f := _), h2 ω a, h2' ω a, smul_add]
    · intro ω h
      rw [Finset.mem_union, not_or] at h
      simp [h3 ω h.1, h3' ω h.2]
    · rw [Finset.sum_add_distrib, h4, h4']
      congr 1
      · exact Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h
      · exact Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h
  | smul c y _ hy =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    refine ⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩
    · intro ω a
      simp only [map_smul, h2 ω a]
      exact smul_comm _ _ _
    · intro ω h
      simp [h3 ω h]
    · rw [h4, Finset.smul_sum]

theorem wtNear_orth_decomp : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, h1, h2, _, h4⟩ := exists_decomp E Λ t w hw
  exact ⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4,
    fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩

end GlobalTheory.WtOrth
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

section
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}

lemma hhJ_self_norm_le_sum_sq (ε : Fin n → Bool) (x : Fin n → M) :
    ‖hhJ ε x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  unfold hhJ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, inner_self_eq_norm_sq_to_K]
  split_ifs <;> simp

lemma hhJ_self_im_eq_zero (ε : Fin n → Bool) (x : Fin n → M) :
    (hhJ ε x x).im = 0 := by
  unfold hhJ
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : (⟪x c, x c⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (x c)
  split_ifs <;> simp [-inner_self_eq_norm_sq_to_K, h]

lemma hhJ_finsum_finsum {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by
  unfold hhJ
  simp only [Finset.sum_apply, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]

end

theorem sum_norm_hhJ_self_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  intro M _ _ n ε y In Cc Cs Nn horth hpos hIn hout
  rw [← Finset.sum_add_sum_compl In]
  have h1 : hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, hhJ ε (y s) (y s) := by
    rw [hhJ_finsum_finsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Finset.sum_eq_single_of_mem s hs fun t _ hts => horth s t (Ne.symm hts)
  have h2 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ = (∑ s ∈ In, hhJ ε (y s) (y s)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Complex.abs_re_eq_norm.mpr (hhJ_self_im_eq_zero ε (y s)), abs_of_nonneg (hpos s hs)]
  have h3 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ ≤ Cc ^ 2 * Nn := by
    rw [h2, ← h1]
    exact (Complex.re_le_norm _).trans ((hhJ_self_norm_le_sum_sq ε _).trans hIn)
  have h4 : ∑ s ∈ Inᶜ, ‖hhJ ε (y s) (y s)‖ ≤ (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    exact (hhJ_self_norm_le_sum_sq ε _).trans (hout s (Finset.mem_compl.mp hs))
  calc _ ≤ Cc ^ 2 * Nn + (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := add_le_add h3 h4
    _ = _ := by ring

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtNear_le_of_add_dist_le :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (Λ Λ' : Fin n → ℝ) (t t' : ℝ),
      t + ∑ a, |Λ a - Λ' a| ≤ t' → WtNear E Λ t ≤ WtNear E Λ' t' := by
  intro M _ _ n _ E Λ Λ' t t' h
  unfold WtNear
  apply Submodule.span_mono
  rintro x ⟨ω, hω, hx⟩
  refine ⟨ω, ?_, hx⟩
  have h1 : ∑ a, |ω a - Λ' a| ≤ ∑ a, (|ω a - Λ a| + |Λ a - Λ' a|) :=
    Finset.sum_le_sum fun a _ => abs_sub_le _ _ _
  rw [Finset.sum_add_distrib] at h1
  linarith

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_zero_of_kHighest : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (w : M), GlRel E → IsUnitary ε E → KHighest ε E (lowK ε μ) w → FiniteDimensional ℂ (kSpan ε E w) → Lev ε E μ 0 w := by
  intro M _ _ n ε E μ w hrel _ hhi hfin
  have hk : KRel ε E := glRel_kRel ε E hrel
  have hsq : ckv ε (lowK ε μ) ≤ (Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * ((0 : ℕ) : ℝ)) ^ 2 := by
    rcases le_total 0 (ckv ε (lowK ε μ)) with h | h
    · simp [Real.sq_sqrt h]
    · simp [Real.sqrt_eq_zero'.mpr h, h]
  refine ⟨⟨kSpan ε E w, hfin, ?_, mem_compact_span_self w, ?_⟩, ?_⟩
  · intro a b hab x hx
    exact compact_span_stable w a b hab x hx
  · intro x hx
    rw [compact_casimir_span_holds M n ε E (lowK ε μ) w hk hhi x hx, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hsq hx2)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    norm_cast
  · apply Submodule.subset_span
    exact ⟨lowK ε μ, by simp, hhi.1⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AdicColimit


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_of_disjoint_cover (R : Type) [CommRing R] (I : Ideal R)
    (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0})
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j)))
    (h : ∀ i, _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I T := by
  obtain ⟨r, hr⟩ : ∃ r : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T, ∀ i, (r i).left = 𝒰.f i :=
    ⟨fun i => Over.homMk (𝒰.f i) rfl, fun i => rfl⟩
  intro X f hf

  have hfi : ∀ i, ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (𝒰.f i ≫ T.hom)) ≫
      (_root_.GlobalTheory.AdicColimit.thickHom I (e + 1) (r i) ≫ f (e + 1)) = _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e := by
    intro i e
    rw [_root_.GlobalTheory.AdicColimit.thickMap_thickHom_assoc, hf]
  choose g hg hgu using fun i => h i X (fun e => _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e) (hfi i)
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) :=
        (cancel_mono (𝒰.f i)).1 pullback.condition
      rw [this]
    · haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := ⟨fun x =>
        Set.disjoint_left.1 (hd i j hij) ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, rfl⟩
          ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms g hglue, fun e => ?_, fun y hy => ?_⟩
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (_root_.GlobalTheory.AdicColimit.thickι I e T)) _ _ fun i => ?_
    change pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _ =
      pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    let φ : pullback (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ⟶
        (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I e (Over.mk (𝒰.f i ≫ T.hom))).left :=
      pullback.lift (pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i))
        (pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
        (by
          show pullback.snd _ _ ≫ 𝒰.f i ≫ T.hom = _
          rw [← Category.assoc, ← pullback.condition]
          simp only [Category.assoc]
          exact congrArg (fun k => pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ k)
            (pullback.condition (f := T.hom) (g := _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)))
    have hφ₁ : φ ≫ _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (𝒰.f i ≫ T.hom)) =
        pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := pullback.lift_fst _ _ _
    have hφ₂ : φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i) = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := by
      apply pullback.hom_ext
      · change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T =
          pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T
        rw [Category.assoc, _root_.GlobalTheory.AdicColimit.thickHom_ι, ← Category.assoc, hφ₁]
        erw [hr i]
        exact pullback.condition.symm
      · have hw := Over.w ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)).map (r i))
        change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) = _
        rw [Category.assoc]
        erw [hw]
        exact pullback.lift_snd _ _ _
    rw [← hφ₁, Category.assoc]
    erw [hg i e]
    rw [← Category.assoc, hφ₂]
  · refine 𝒰.hom_ext _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    refine hgu i _ fun e => ?_
    have hcomp := _root_.GlobalTheory.AdicColimit.thickHom_ι_assoc I e (r i) y
    rw [hr] at hcomp
    rw [← hcomp, hy]

end GlobalTheory.AdicColimit
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.AdicColimit

theorem smodEq_smul_top_map {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x y : M} (h : x ≡ y [SMOD (J • ⊤ : Submodule A M)]) :
    f x ≡ f y [SMOD (J • ⊤ : Submodule A N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  have : (J • ⊤ : Submodule A M).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨_, h, rfl⟩

theorem isAdicComplete_of_retract {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (s : N →ₗ[A] M) (p : M →ₗ[A] N) (hps : ∀ x, p (s x) = x)
    (h : IsAdicComplete J M) : IsAdicComplete J N := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have : s x = 0 := IsHausdorff.haus h.toIsHausdorff (s x) fun n => by
      simpa using smodEq_smul_top_map _ s (hx n)
    rw [← hps x, this, map_zero]
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => s (f n)) fun {m n} hmn =>
      smodEq_smul_top_map _ s (hf hmn)
    exact ⟨p L, fun n => by simpa [hps] using smodEq_smul_top_map _ p (hL n)⟩

theorem isAdicComplete_map_eval {A ι : Type} [CommRing A] (T : ι → Type) [∀ i, CommRing (T i)]
    (e : A ≃+* Π i, T i) (J : Ideal A) (h : IsAdicComplete J A) (i : ι) :
    IsAdicComplete (J.map ((Pi.evalRingHom T i).comp e.toRingHom)) (T i) := by
  classical
  letI : Algebra A (T i) := ((Pi.evalRingHom T i).comp e.toRingHom).toAlgebra
  let s : T i →ₗ[A] A :=
    { toFun t := e.symm (Pi.single i t)
      map_add' x y := by rw [Pi.single_add, map_add (f := _)]
      map_smul' a t := by
        apply e.injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          ← Pi.single_mul_right]
        rfl }
  refine (IsAdicComplete.map_algebraMap_iff J (T i)).2
    (isAdicComplete_of_retract J s (Algebra.linearMap A (T i)) (fun t => ?_) h)
  change e (e.symm (Pi.single i t)) i = t
  rw [e.apply_symm_apply, Pi.single_eq_same]

theorem isAdicColimit_finite_henselian_of_local :
    (∀ (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [IsLocalRing A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ)))) → (∀ (R : Type) [CommRing R] (I : Ideal R) (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0}), (∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j))) → (∀ i, IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) → IsAdicColimit I T) → ∀ (R : Type) [CommRing R] (I : Ideal R) (O : Type) [CommRing O] [HenselianLocalRing O] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  intro hloc hcov R _ I O _ _ A _ _ _ φ hc
  classical
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  let π (i : ι) : A →+* T i := (Pi.evalRingHom T i).comp e.toRingEquiv.toRingHom
  have hopen (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (π i))) := by
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of A)).OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => Spec (CommRingCat.of (T i))) (fun i => Spec.map (CommRingCat.ofHom (π i))) (fun x => by
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        (PrimeSpectrum.comap e.toRingEquiv.symm.toRingHom x)
      refine ⟨i, q, ?_⟩
      change PrimeSpectrum.comap e.toRingEquiv.toRingHom (PrimeSpectrum.comap (Pi.evalRingHom T i) q) = x
      rw [hq]
      ext a
      change e.symm (e a) ∈ x.asIdeal ↔ _
      rw [e.symm_apply_apply]) hopen
  refine hcov R I (Over.mk (Spec.map (CommRingCat.ofHom φ))) 𝒰 (fun i j hij => ?_) fun i => ?_
  · rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    change ι at i j
    change PrimeSpectrum (T i) at p
    change PrimeSpectrum (T j) at q
    change PrimeSpectrum.comap (π j) q = PrimeSpectrum.comap (π i) p at hq
    have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (π j) q).asIdeal := by
      change e (e.symm (Pi.single i 1)) j ∈ q.asIdeal
      rw [e.apply_symm_apply, Pi.single_eq_of_ne (i := i) (i' := j) (fun h => hij h.symm)]
      exact zero_mem _
    rw [hq] at h1
    change e (e.symm (Pi.single i 1)) i ∈ p.asIdeal at h1
    rw [e.apply_symm_apply, Pi.single_eq_same] at h1
    exact p.isPrime.one_notMem h1
  · change ι at i
    have := (hT i).1
    have key := hloc R I (T i) ((π i).comp φ) (by
      rw [← Ideal.map_map]
      exact isAdicComplete_map_eval T e.toRingEquiv _ hc i)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at key
    exact key

end GlobalTheory.AdicColimit
end
