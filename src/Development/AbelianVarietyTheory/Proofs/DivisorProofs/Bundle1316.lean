module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush.LowMul

variable {K : Type} [Field K] {n : ℕ}

def Lo (L : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → L i j = 0

def AL (E : Fin n → Fin n → Prop) (C : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → ¬ E i j → C i j = 0

theorem al_mul {E : Fin n → Fin n → Prop} (hE : ∀ i j k, E k j → k ≤ i → i < j → E i j)
    {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C) : AL E (L * C) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hL i k h, zero_mul]
  · rw [hC k j (lt_of_le_of_lt h hij) (fun he => hn (hE i j k he h hij)), mul_zero]

theorem mul_al {E : Fin n → Fin n → Prop} (hE : ∀ i j l, E i l → j ≤ l → i < j → E i j)
    {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R) : AL E (C * R) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l j with h | h
  · rw [hR l j h, mul_zero]
  · rw [hC i l (lt_of_lt_of_le hij h) (fun he => hn (hE i j l he h hij)), zero_mul]

theorem diag_mul {E : Fin n → Fin n → Prop} {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C)
    (x : Fin n) (hx : ∀ k, k < x → ¬ E k x) : (L * C) x x = L x x * C x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hC k x h (hx k h), mul_zero]
  · rw [hL x k h, zero_mul]

theorem mul_diag {E : Fin n → Fin n → Prop} {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R)
    (x : Fin n) (hx : ∀ l, x < l → ¬ E x l) : (C * R) x x = C x x * R x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun l hl => ?_
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hR l x h, mul_zero]
  · rw [hC x l h (hx l h), zero_mul]

theorem lo_diag_ne {M : Matrix (Fin n) (Fin n) K} (hM : Lo M) (hd : M.det ≠ 0) (i : Fin n) : M i i ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular M (fun i j h => hM i j (OrderDual.toDual_lt_toDual.1 h))] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

section Pair
variable {a b : Fin n} {L C R : Matrix (Fin n) (Fin n) K}

theorem lower_index_pair_unique (hab : (b : ℕ) = a + 1) : ∀ i j k : Fin n, (k = a ∧ j = b) → k ≤ i → i < j → (i = a ∧ j = b) := by
  rintro i j k ⟨rfl, rfl⟩ h1 h2
  refine ⟨Fin.ext ?_, rfl⟩
  rw [Fin.le_iff_val_le_val] at h1; rw [Fin.lt_iff_val_lt_val] at h2; omega

theorem l_aa (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a a = L a a * C a a :=
  diag_mul hL hC a fun _ _ e => absurd (congrArg Fin.val e.2) (by omega)

theorem l_ab (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a b = L a a * C a b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single a fun k hk => ?_
  have hk' : (k : ℕ) ≠ a := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hk' with h | h
  · rw [hC k b (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hk e.1), mul_zero]
  · rw [hL a k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_ba (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b a = L b a * C a a + L b b * C b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k a (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_bb (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b b = L b a * C a b + L b b * C b b := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k b h (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem r_aa (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a a = C a a * R a a + C a b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 h) (fun e => hlb e.2), zero_mul]

theorem r_ab (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a b = C a b * R b b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single b fun l hl => ?_
  have hl' : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hR l b (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hl e.2), zero_mul]

theorem r_ba (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b a = C b a * R a a + C b b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC b l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hne e.1.symm), zero_mul]

theorem r_bb (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b b = C b b * R b b :=
  mul_diag hC hR b fun _ _ e => absurd (congrArg Fin.val e.1) (by omega)

end Pair

section Root
variable {ι : Type} {m : ι → ℕ} {τ : ι} {a b : Fin (m τ)}

theorem root_lower_pair_unique_left (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j k : Fin (m σ),
    ((⟨σ, k⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → k ≤ i → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j k ⟨h1, h2⟩ hki hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨congrArg (Sigma.mk _) (Fin.ext ?_), rfl⟩
  rw [Fin.le_iff_val_le_val] at hki; rw [Fin.lt_iff_val_lt_val] at hij; omega

theorem root_lower_pair_unique_right (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j l : Fin (m σ),
    ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, l⟩ : Root m) = ⟨τ, b⟩) → j ≤ l → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j l ⟨h1, h2⟩ hjl hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨rfl, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
  rw [Fin.le_iff_val_le_val] at hjl; rw [Fin.lt_iff_val_lt_val] at hij; omega

end Root

end GlobalTheory.FlagPush.LowMul

namespace GlobalTheory.FlagPush


open LowMul in
theorem almostLow_mul_entries : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  intro ι m τ a b hab K _ S T C hS hT hC
  have hSl : ∀ σ, Lo (S σ) := fun σ i j h => (hS σ).2.2.2 i j i.isLt h
  have hTl : ∀ σ, Lo (T σ) := fun σ i j h => (hT σ).2.2.2 i j i.isLt h
  have hCr : ∀ σ, AL (fun i j => (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) (C σ) :=
    fun σ => hC.2.2 σ
  have hCt : AL (fun i j => i = a ∧ j = b) (C τ) := fun i j h hn =>
    hC.2.2 τ i j h fun e => hn ⟨eq_of_heq (Sigma.mk.inj_iff.1 e.1).2, eq_of_heq (Sigma.mk.inj_iff.1 e.2).2⟩
  have hP : AL (fun i j => i = a ∧ j = b) (S τ * C τ) := al_mul (lower_index_pair_unique hab) (hSl τ) hCt
  have h3 : (S * C * T) τ a b = S τ a a * C τ a b * T τ b b := by
    show (S τ * C τ * T τ) a b = _
    rw [r_ab hab hP (hTl τ), l_ab hab (hSl τ) hCt]
  refine ⟨⟨fun σ => ?_, ?_, fun σ => ?_⟩, fun x hxa hxb => ?_, h3, ?_⟩
  · show (S σ * C σ * T σ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hS.det_ne σ) (hC.1 σ)) (hT.det_ne σ)
  · rw [h3]
    exact mul_ne_zero (mul_ne_zero (lo_diag_ne (hSl τ) (hS.det_ne τ) a) hC.2.1) (lo_diag_ne (hTl τ) (hT.det_ne τ) b)
  · exact mul_al (root_lower_pair_unique_right hab σ) (al_mul (root_lower_pair_unique_left hab σ) (hSl σ) (hCr σ)) (hTl σ)
  · show (S x.1 * C x.1 * T x.1) x.2 x.2 = _
    rw [mul_diag (al_mul (root_lower_pair_unique_left hab x.1) (hSl x.1) (hCr x.1)) (hTl x.1) x.2 (fun _ _ e => hxa e.1),
      diag_mul (hSl x.1) (hCr x.1) x.2 (fun _ _ e => hxb e.2)]
  · show (S τ * C τ * T τ) a a * (S τ * C τ * T τ) b b - (S τ * C τ * T τ) a b * (S τ * C τ * T τ) b a =
      S τ a a * S τ b b * (C τ a a * C τ b b - C τ a b * C τ b a) * (T τ a a * T τ b b)
    rw [r_aa hab hP (hTl τ), r_bb hab hP (hTl τ), r_ab hab hP (hTl τ), r_ba hab hP (hTl τ),
      l_aa hab (hSl τ) hCt, l_bb hab (hSl τ) hCt, l_ab hab (hSl τ) hCt, l_ba hab (hSl τ) hCt]
    ring

end GlobalTheory.FlagPush
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem glueMeas_zero_dens {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) : glueMeas e (fun _ _ => 0) = 0 := by
  have h : ∀ i, chartMeas (e i) (fun _ => 0) = 0 := by
    intro i
    unfold chartMeas
    have : ((fun _ : Y => (0 : ENNReal)) ∘ (e i).symm) = 0 := rfl
    rw [this, withDensity_zero, Measure.map_zero]
  unfold glueMeas
  simp only [h]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

theorem hasInt_zero {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y) : HasInt e (fun _ _ => 0) S 0 := by
  unfold HasInt
  simp only [mul_zero, ENNReal.ofReal_zero, glueMeas_zero_dens]
  simp

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mdbar_neg_cut_conn_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    {G₀ G₁ : V n → Matrix r r ℂ} {v : V n} (hρ : DifferentiableAt ℝ ρ v) (h₀ : MContDiffAt 2 G₀ v)
    (u₀ : IsUnit (G₀ v).det) (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) :
    (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b))
      = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  funext a b
  have c₀ : MContDiffAt 1 (fun x => conn G₀ x (coordVec a)) v := h₀.conn u₀ (by norm_num) _
  have c₁ : MContDiffAt 1 (fun x => conn G₁ x (coordVec a)) v := h₁.conn u₁ (by norm_num) _
  have hρ' : DifferentiableAt ℝ (fun x => (ρ x : ℂ)) v := Complex.ofRealCLM.differentiableAt.comp v hρ
  have hs : mdbar (fun x => conn G₁ x (coordVec a) - conn G₀ x (coordVec a)) v (coordVec b) =
      mdbar (fun x => conn G₁ x (coordVec a)) v (coordVec b) -
        mdbar (fun x => conn G₀ x (coordVec a)) v (coordVec b) := by
    simp only [sub_eq_add_neg]
    rw [mdbar_add c₁ c₀.neg, mdbar_neg]
  rw [mdbar_neg (fun x => (ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a))),
    mdbar_smul hρ' (c₁.sub c₀), hs]
  simp only [Pi.sub_apply, Pi.smul_apply, curvAt, cutForm, curv, smul_sub, smul_neg]
  abel

end GlobalTheory.GoodTop
end
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_mixTop :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
      {K : _root_.ReciprocityTheory.L2DbarEstimates.V n → Fin n → _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) →
        ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop (K x)) v := by
  intro n r _ _ K v hK
  unfold _root_.GlobalTheory.GoodTop.mixTop
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem goodPatch_image : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  intro F _ σ X m E O H e S A W c h
  refine ⟨e.isOpen_image_of_subset_source h.isOpen h.sub, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨z, ⟨hO, hW⟩, rfl⟩
      exact ⟨⟨z, hW, rfl⟩, (h.mem z hW).1 hO⟩
    · rintro ⟨⟨z, hW, rfl⟩, hv⟩
      exact ⟨z, ⟨(h.mem z hW).2 hv, hW⟩, rfl⟩
  · intro K hK hKW
    haveI : CompactSpace (CxPts X.str σ) := CxPts.compactSpace σ X.isProjOver
    exact hK.isCompact.image_of_continuousOn (e.continuousOn.mono (hKW.trans h.sub))

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_prod_perm_mul_comm {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (A : Fin n → Matrix r r ℂ)
    (P : Matrix r r ℂ) (π : Equiv.Perm (Fin n)) :
    ∑ p : Fin n → r, ∏ i, (A i * P) (p i) (p (π i)) = ∑ p : Fin n → r, ∏ i, (P * A i) (p i) (p (π i)) := by
  simp only [Matrix.mul_apply]
  have h1 : ∀ f : Fin n → r → ℂ, ∏ i, ∑ j, f i j = ∑ s : Fin n → r, ∏ i, f i (s i) := fun f => by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [h1]
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl r)) _ _ fun t => ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.prod_mul_distrib, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp, id]
  rw [mul_comm, Equiv.prod_comp π fun i => P (t i) (p i)]

theorem mixTop_conj {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ)
    (hP : IsUnit P.det) : mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  unfold mixTop
  congr 1
  have hdet : ∀ M : Fin n → Fin n → ℂ, (Matrix.of M).det =
      ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, M i (w i) := fun M => by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [← Finset.mul_sum]
  congr 2
  rw [sum_prod_perm_mul_comm (fun i => P⁻¹ * K i (u i) (w i)) P π]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem mixTop_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  intro n r _ _ K j L L'
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  unfold mixTop
  rw [← mul_add]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  rw [key, key, key, ← mul_add, ← Matrix.det_updateRow_add]
  rfl

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

open GlobalTheory.GoodTop

namespace GlobalTheory.GoodTop

theorem mixTop_update_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n)
    (t : ℂ) (L : EndValuedForm11Coeffs n r) :
    mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  have h2 : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j (t • L) i (u i) b (p i) (p (π i))).det =
        t * (Matrix.of fun i b => Function.update K j L i (u i) b (p i) (p (π i))).det := by
    intro p π u
    rw [key, key, ← Matrix.det_updateRow_smul]
    rfl
  unfold mixTop
  simp only [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  ring

end GlobalTheory.GoodTop
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  first | exact @GlobalTheory.QLogInj.main | exact GlobalTheory.QLogInj.main | (intros; apply GlobalTheory.QLogInj.main <;> assumption)
end
