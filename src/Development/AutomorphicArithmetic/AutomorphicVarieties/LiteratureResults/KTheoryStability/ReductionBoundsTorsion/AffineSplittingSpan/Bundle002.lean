module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle001
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
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

theorem dc_cons {m : ℕ} (G : (Fin (m + 2) → Y) → ℝ) (a : Y) (t : Fin (m + 2) → Y) :
    dc G (Fin.cons a t) = G t - dc (fun z => G (Fin.cons a z)) t := by
  unfold dc
  rw [Fin.sum_univ_succ]
  have h0 : (fun j => (Fin.cons a t : Fin (m + 3) → Y) ((0 : Fin (m + 3)).succAbove j)) = t := by
    funext j; simp
  have hs : ∀ i : Fin (m + 2), (fun j => (Fin.cons a t : Fin (m + 3) → Y) (i.succ.succAbove j)) =
      Fin.cons a (fun j => t (i.succAbove j)) := by
    intro i; funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_succAbove_succ]
  rw [h0]
  simp only [hs, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_sub {m : ℕ} (G H : (Fin (m + 1) → Y) → ℝ) (x : Fin (m + 2) → Y) :
    dc (fun z => G z - H z) x = dc G x - dc H x := by
  unfold dc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc1 (G : (Fin 1 → Y) → ℝ) (y : Fin 2 → Y) :
    dc G y = G (fun _ => y 1) - G (fun _ => y 0) := by
  unfold dc
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h0 : (fun j : Fin 1 => y ((0 : Fin 2).succAbove j)) = fun _ => y 1 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  have h1 : (fun j : Fin 1 => y ((Fin.succ 0 : Fin 2).succAbove j)) = fun _ => y 0 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  rw [h0, h1]; simp; ring

def prism (φ : Y → Y) : (m : ℕ) → ((Fin (m + 2) → Y) → ℝ) → (Fin (m + 1) → Y) → ℝ
  | 0, F, x => F (Fin.cons (x 0) (φ ∘ x))
  | m + 1, F, x => F (Fin.cons (x 0) (φ ∘ x)) - prism φ m (fun z => F (Fin.cons (x 0) z)) (Fin.tail x)

theorem prism_sub (φ : Y → Y) : ∀ (m : ℕ) (F G : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 1) → Y),
    prism φ m (fun z => F z - G z) x = prism φ m F x - prism φ m G x
  | 0, F, G, x => rfl
  | m + 1, F, G, x => by
    simp only [prism]
    rw [prism_sub φ m]
    ring

theorem prism_zero (φ : Y → Y) : ∀ (m : ℕ) (x : Fin (m + 1) → Y),
    prism φ m (fun _ => (0 : ℝ)) x = 0
  | 0, x => rfl
  | m + 1, x => by
    simp only [prism]
    rw [prism_zero φ m]
    ring

theorem prism_base (φ : Y → Y) (F : (Fin 2 → Y) → ℝ) (x : Fin 2 → Y) :
    dc (prism φ 0 F) x + prism φ 1 (dc F) x = F (φ ∘ x) - F x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = Fin.cons a (fun _ : Fin 1 => b) := ⟨x 0, x 1, by
    funext j; refine Fin.cases rfl (fun k => ?_) j; rw [Fin.fin_one_eq_zero k]; rfl⟩
  simp only [prism, Fin.cons_zero, Fin.tail_cons]
  simp only [Fin.comp_cons]
  simp only [dc_cons, dc1]
  simp only [Fin.cons_zero, Fin.cons_one, Function.comp_def]
  ring

theorem prism_htpy (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 2) → Y),
    dc (prism φ m F) x + prism φ (m + 1) (dc F) x = F (φ ∘ x) - F x := by
  intro m
  induction m with
  | zero => exact prism_base φ
  | succ m ih =>
    intro F x
    obtain ⟨a, t, rfl⟩ : ∃ a t, x = Fin.cons a t := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [dc_cons]
    have hK : (fun z => prism φ (m + 1) F (Fin.cons a z)) =
        fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z))) - prism φ m (fun w => F (Fin.cons a w)) z := by
      funext z; simp only [prism, Fin.cons_zero, Fin.tail_cons, Fin.comp_cons]
    rw [hK, dc_sub]
    have h2 : prism φ (m + 2) (dc F) (Fin.cons a t) =
        dc F (Fin.cons a (φ ∘ Fin.cons a t)) - prism φ (m + 1) (fun z => dc F (Fin.cons a z)) t := by
      simp only [prism, Fin.cons_zero, Fin.tail_cons]
    rw [h2]
    have h3 : (fun z => dc F (Fin.cons a z)) = fun z => F z - dc (fun w => F (Fin.cons a w)) z := by
      funext z; exact dc_cons F a z
    rw [h3, prism_sub, Fin.comp_cons, dc_cons, dc_cons]
    have h4 : dc (fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z)))) t =
        dc (fun w => F (Fin.cons a (Fin.cons (φ a) w))) (φ ∘ t) := rfl
    rw [h4]
    linarith [ih (fun z => F (Fin.cons a z)) t]

theorem prism_smul {P : Type} [Group P] (φ : P → P) (k : P) (hφ : ∀ y, φ (k * y) = k * φ y) :
    ∀ (m : ℕ) (F : (Fin (m + 2) → P) → ℝ) (x : Fin (m + 1) → P),
      prism φ m F (fun i => k * x i) = prism φ m (fun z => F (fun i => k * z i)) x
  | 0, F, x => by
    simp only [prism]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hφ]
  | m + 1, F, x => by
    simp only [prism]
    have e1 : (Fin.cons (k * x 0) (φ ∘ fun i => k * x i) : Fin (m + 3) → P) =
        fun i => k * (Fin.cons (x 0) (φ ∘ x) : Fin (m + 3) → P) i := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hφ]
    rw [e1]
    congr 1
    have e2 : (Fin.tail fun i => k * x i) = fun i => k * Fin.tail x i := rfl
    rw [e2, prism_smul φ k hφ m]
    congr 1
    funext z
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

end
end

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {P : Type} [Group P]

def levSum (t : P) (lev : P → ℤ) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) : ℝ :=
  if 0 ≤ lev (y 0) then ∑ j ∈ Finset.range (lev (y 0)).toNat, w (fun i => t ^ (-((j : ℤ) + 1)) * y i)
  else -∑ j ∈ Finset.range (-lev (y 0)).toNat, w (fun i => t ^ (j : ℤ) * y i)

theorem levSum_spec (t : P) (lev : P → ℤ) (hlev : ∀ z, lev (t * z) = lev z + 1) {n : ℕ}
    (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) :
    levSum t lev w (fun i => t * y i) - levSum t lev w y = w y := by
  unfold levSum
  have e : ∀ k : ℤ, (fun i => t ^ k * (t * y i)) = fun i => t ^ (k + 1) * y i := by
    intro k
    funext i
    rw [← mul_assoc, ← zpow_add_one]
  simp only [hlev, e]
  generalize lev (y 0) = a
  rcases le_or_gt 0 a with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [if_pos (by omega), if_pos h]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, Int.toNat_natCast, Finset.sum_range_succ']
    have ex : ∀ j : ℕ, -(((j + 1 : ℕ) : ℤ) + 1) + 1 = -((j : ℤ) + 1) := by
      intro j
      push_cast
      ring
    simp only [ex]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero h
    rcases m with _ | k
    · rw [if_pos (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [show (-(Int.negSucc (k + 1) + 1)).toNat = k + 1 by omega,
        show (-Int.negSucc (k + 1)).toNat = k + 1 + 1 by omega, Finset.sum_range_succ' _ (k + 1)]
      have ex : ∀ j : ℕ, ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by
        intro j
        push_cast
        rfl
      simp only [ex]
      simp

theorem levSum_inv (t : P) (lev : P → ℤ) (S : Set P) (hS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z)
    (hc : ∀ g ∈ S, g * t = t * g) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (hw : InvS S w) :
    InvS S (levSum t lev w) := by
  intro g hg y
  unfold levSum
  simp only [hS g hg]
  have hk : ∀ k : ℤ, (fun i => t ^ k * (g * y i)) = fun i => g * (t ^ k * y i) := by
    intro k; funext i
    rw [← mul_assoc, ← mul_assoc, ((Commute.zpow_right (hc g hg) k)).eq]
  simp only [hk, hw g hg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

section

noncomputable section

open Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def gpoly (Λ : ℂ) : ℝ[X] := X ^ 2 - C (2 * Λ.re) * X + C (Complex.normSq Λ)

theorem gpoly_eval_one (Λ : ℂ) : (gpoly Λ).eval 1 = Complex.normSq (1 - Λ) := by
  simp only [gpoly, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem mapOp_apply {A : Type} (φ : A → A) (m : ℕ) (F : (Fin m → A) → ℝ) (y : Fin m → A) :
    mapOp φ m F y = F fun i => φ (y i) := rfl

theorem kill_one {A : Type} (φ : A → A) (m : ℕ) (E : (Fin m → A) → ℂ) (Λ z : ℂ)
    (hE : ∀ y, E (fun i => φ (y i)) = Λ * E y) :
    aeval (mapOp φ m) (gpoly Λ) (fun y => (z * E y).re) = 0 := by
  simp only [gpoly, map_add (f := _), map_sub, map_mul, aeval_X, aeval_C, map_pow]
  funext y
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mapOp_apply,
    hE, Pi.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kill_sum {A : Type} (φ : A → A) (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → (Fin m → A) → ℂ) (Λ z : ι → ℂ) (hE : ∀ j y, E j (fun i => φ (y i)) = Λ j * E j y)
    (F : (Fin m → A) → ℝ) (hF : ∀ y, (F y : ℂ) = ∑ j, z j * E j y) :
    aeval (mapOp φ m) (∏ j, gpoly (Λ j)) F = 0 := by
  have hF' : F = ∑ j, fun y => (z j * E j y).re := by
    funext y
    rw [Finset.sum_apply, ← Complex.re_sum, ← hF y, Complex.ofReal_re]

  rw [hF', map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply,
    kill_one φ m (E j) (Λ j) (z j) (hE j), map_zero]

theorem cup_kill {A : Type} [Group A] (φ : A →* A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ι → Additive A → ℂ) (lam : ι → ℂ)
    (hβ : ∀ j x, β j (Additive.ofMul (φ x)) = lam j * β j (Additive.ofMul x))
    (hspan : ∀ α : Additive A →+ ℝ, ∃ c : ι → ℂ, ∀ x, (α x : ℂ) = ∑ j, c j * β j x) (q : ℕ)
    (α : Fin (q + 1) → (Additive A →+ ℝ)) :
    aeval (mapOp φ (q + 2)) (∏ J : Fin (q + 1) → ι, gpoly (∏ i, lam (J i))) (cupH α) = 0 := by
  choose c hc using hspan
  let d : Fin (q + 1) → (Fin (q + 2) → A) → Additive A :=
    fun i y => Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ)
  let E : (Fin (q + 1) → ι) → (Fin (q + 2) → A) → ℂ := fun J y => ∏ i, β (J i) (d i y)
  let Λ : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, lam (J i)
  let z : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, c (α i) (J i)
  have hE : ∀ J y, E J (fun i => φ (y i)) = Λ J * E J y := by
    intro J y
    simp only [E, Λ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : d i (fun k => φ (y k)) = Additive.ofMul (φ ((y i.castSucc)⁻¹ * y i.succ)) := by
      simp only [d, map_mul, map_inv]
    rw [this, hβ]
  have hF : ∀ y, (cupH α y : ℂ) = ∑ J, z J * E J y := by
    intro y
    have h1 : (cupH α y : ℂ) = ∏ i, ∑ j, c (α i) j * β j (d i y) := by
      rw [cupH, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => hc (α i) _
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [z, E]
    rw [Finset.prod_mul_distrib]
  exact kill_sum (⇑φ) (q + 2) E Λ z hE (cupH α) hF

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

section

noncomputable section

open NumberField InfinitePlace Pointwise

namespace PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem place_pos (v : (𝓞 L)ˣ) (w : InfinitePlace L) : 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) := w.pos_iff.mpr (by simp)

def lchar (a : InfinitePlace L → ℕ) : (𝓞 L)ˣ →* Multiplicative ℝ where
  toFun v := Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Units.val_mul, map_mul, map_mul, Real.log_mul (place_pos x w).ne' (place_pos y w).ne']
    ring

theorem lchar_eq_one_iff (a : InfinitePlace L → ℕ) (v : (𝓞 L)ˣ) :
    lchar a v = 1 ↔ ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
  have hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    fun w => pow_pos (place_pos v w) _
  have hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    Finset.prod_pos fun w _ => hpos w
  have hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) =
      ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))) := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _
  rw [ofAdd_eq_one, ← hlog]
  constructor
  · intro h
    rw [← Real.exp_log hP, h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

theorem lchar_nontrivial (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ∃ v, lchar a v ≠ 1 := by
  classical
  have hcard : ∑ w, a w < Fintype.card (InfinitePlace L) := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by
    by_contra h
    push_neg at h
    have h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w :=
      Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)
    simp at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by
    by_contra h
    push_neg at h
    have h0 : ∑ w, a w = 0 := Finset.sum_eq_zero fun w _ => by
      have := h w
      omega
    omega
  have hne : w₂ ≠ w₁ := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L w₁
  refine ⟨u, fun h => ?_⟩
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h
  rw [ofAdd_eq_one] at h
  have hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) <
      ∑ _w : InfinitePlace L, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = w₁
      · subst hw
        simp [hw₁]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le
    · exact ⟨w₂, Finset.mem_univ _,
        mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩
  rw [Finset.sum_const_zero, h] at hlt
  exact lt_irrefl _ hlt

theorem lchar_ker_not_finiteIndex (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ¬ (lchar a).ker.FiniteIndex := by
  intro hfi
  obtain ⟨v, hv⟩ := lchar_nontrivial hC a ha hm
  apply hv
  have hmem := (lchar a).ker.pow_index_mem v
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hidx : (lchar a).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0 := by
    rw [hmem]
    rfl
  rw [toAdd_pow, nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hidx
  · exact toAdd_eq_zero.mp h1

end PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

open PositivityTheory.KB.SplitAffineSpectral.unitAtAlt in
theorem PositivityTheory.KB.SplitAffineSpectral.unit : PositivityTheory.KB.SplitAffineSpectral.Unit := by
  unfold PositivityTheory.KB.SplitAffineSpectral.Unit
  intro L _ _ hC m hm
  classical
  by_contra hcon
  push_neg at hcon
  let s : Finset (InfinitePlace L → ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
      fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]
      obtain ⟨a, ha0, ham, hprod⟩ := hcon v
      refine ⟨a, ?_, ?_⟩
      · simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun w => ?_, ha0, ham⟩
        have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
        omega
      · exact (MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))
  simp only [s, Finset.mem_filter] at hk
  exact lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi
end
end
