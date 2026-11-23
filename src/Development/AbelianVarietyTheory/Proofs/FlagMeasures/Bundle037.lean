module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle028
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClass

theorem exists_inv {E : Type} [CommRing E] {σ : Type} [SetLike σ E] [SubringClass σ E] (O : σ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hO : ∀ i j, A i j ∈ O) (ht : ∀ i j, j < i → A i j = 0)
    (hd : ∀ i, A i i = 1) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ i j, B i j ∈ O) ∧ (∀ i j, j < i → B i j = 0) ∧ (∀ i, B i i = 1) ∧
      A * B = 1 ∧ B * A = 1 := by
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
  have hM : M.BlockTriangular id := fun i j h => Subtype.ext (ht i j h)
  have hMd : ∀ i, M i i = 1 := fun i => Subtype.ext (hd i)
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hM]; simp [hMd]
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  let _ : Invertible M := Matrix.invertibleOfIsUnitDet M hu
  have hI : (M⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hA : M.map (SubringClass.subtype O) = A := rfl
  refine ⟨(M⁻¹).map (SubringClass.subtype O), fun i j => (M⁻¹ i j).2, fun i j h => ?_, fun i => ?_, ?_, ?_⟩
  · have : M⁻¹ i j = 0 := hI h
    simp [Matrix.map_apply, this]
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hMd, one_mul] at h
    · simp [Matrix.map_apply, h]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · have : M i k = 0 := hM hk
        rw [this, zero_mul]
      · have : M⁻¹ k i = 0 := hI hk
        rw [this, mul_zero]
    · simp
  · rw [← hA, ← Matrix.map_mul, h1]; simp
  · rw [← hA, ← Matrix.map_mul, h2]; simp

theorem sum_comp {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) E) (g p q : Fin n → V) (hp : ∀ j, p j = ∑ i, A i j • g i)
    (hq : ∀ j, q j = ∑ i, B i j • p i) (j : Fin n) : q j = ∑ i, (A * B) i j • g i := by
  rw [hq]
  simp only [hp, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne_zero : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

theorem intM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem cong_iff {n : ℕ} (t : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = t * c) ↔ ∃ C, IsIntM L C ∧ A' - A = t • C := by
  constructor
  · intro h
    choose C hC hC' using h
    exact ⟨C, hC, by ext i j; exact hC' i j⟩
  · rintro ⟨C, hC, h⟩ i j
    exact ⟨C i j, hC i j, congrFun (congrFun h i) j⟩

theorem refl_mem (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩, fun j => ?_,
    fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

omit [TopologicalSpace E] in
theorem tri_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : ∀ i j, j < i → (A * B) i j = 0 := fun i j h => by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hB' : B.BlockTriangular id := fun i j h => hB i j h
  exact hA'.mul hB' h

omit [TopologicalSpace E] in
theorem diag_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA i l hl, zero_mul]
    · rw [hB l i hl, mul_zero]
  · simp

theorem trans_mem {g g' : Fin (r + 1) → S.V} {p q : S.FrP} (hp : p ∈ S.frameCls g g')
    (hq : q ∈ S.frameCls p.1 p.2) : q ∈ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨B, B', hB, hB', kt, kd, kc, k1, k2⟩ := hq
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨D, hD, kc⟩ := (cong_iff _ _ _).1 kc
  refine ⟨A * B, A' * B', intM_mul hA hB, intM_mul hA' hB', fun i j h => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_,
    sum_comp A B g p.1 q.1 h1 k1, sum_comp A' B' g' p.2 q.2 h2 k2⟩
  · exact tri_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1) i j h
  · exact tri_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2) i j h
  · rw [diag_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1), (hd i).1, (kd i).1, one_mul]
  · rw [diag_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2), (hd i).2, (kd i).2, one_mul]
  · refine (cong_iff _ _ _).2 ⟨C * B' + A * D, fun i j => ?_, ?_⟩
    · exact add_mem (intM_mul hC hB' i j) (intM_mul hA hD i j)
    · rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, ← kc, sub_mul, mul_sub]; abel

theorem symm_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    (g, g') ∈ S.frameCls p.1 p.2 := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨B, hB, bt, bd, hAB, hBA⟩ := exists_inv L.O A hA (fun i j h => (ht i j h).1) (fun i => (hd i).1)
  obtain ⟨B', hB', bt', bd', hAB', hBA'⟩ :=
    exists_inv L.O A' hA' (fun i j h => (ht i j h).2) (fun i => (hd i).2)
  refine ⟨B, B', hB, hB', fun i j h => ⟨bt i j h, bt' i j h⟩, fun i => ⟨bd i, bd' i⟩, ?_, fun j => ?_,
    fun j => ?_⟩
  · refine (cong_iff _ _ _).2 ⟨-(B' * C * B), fun i j => ?_, ?_⟩
    · exact neg_mem (intM_mul (intM_mul hB' hC) hB i j)
    · rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, mul_sub, sub_mul, hBA', mul_assoc, hAB]
      simp
  · have := sum_comp A B g p.1 (fun j => ∑ i, B i j • p.1 i) h1 (fun _ => rfl) j
    rw [this, hAB]; simp [Matrix.one_apply]
  · have := sum_comp A' B' g' p.2 (fun j => ∑ i, B' i j • p.2 i) h2 (fun _ => rfl) j
    rw [this, hAB']; simp [Matrix.one_apply]

theorem Mof_le {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    S.Mof p.1 p.2 ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  have hsm : ∀ c ∈ L.O, ∀ v ∈ S.Mof g g', c • v ∈ S.Mof g g' := fun c hc v hv =>
    (S.Mof g g').smul_mem ⟨c, hc⟩ hv
  have hg : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hg' : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have hth : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
  choose C hC hC' using hc
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1]
    exact sum_mem fun i _ => hsm _ (hA i j) _ (hg i)
  · have : algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) =
        ∑ i, (A' i j • (algebraMap F E S.th⁻¹ • (g' i - g i)) + C i j • g i) := by
      rw [h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hCi : C i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hC', ← mul_assoc, hth, one_mul]
      rw [hCi]; module
    show algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) ∈ S.Mof g g'
    rw [this]
    exact sum_mem fun i _ => add_mem (hsm _ (hA' i j) _ (hg' i)) (hsm _ (hC i j) _ (hg i))

theorem smul_mem (h : S.GLV) {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    h • p ∈ S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  refine ⟨A, A', hA, hA', ht, hd, hc, fun j => ?_, fun j => ?_⟩
  · show h (p.1 j) = _
    rw [h1]; simp
  · show h (p.2 j) = _
    rw [h2]; simp

theorem smul_cls (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem S h hq
  · intro hp
    have := smul_mem S h⁻¹ hp
    refine ⟨h⁻¹ • p, ?_, smul_inv_smul h p⟩
    have e : ∀ v : S.V, h⁻¹ (h v) = v := fun v => h.symm_apply_apply v
    simpa only [e] using this

theorem frame_classes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g'
  refine ⟨refl_mem S g g', fun p hp => ⟨?_, ?_⟩, fun h => smul_cls S h g g'⟩
  · ext q
    exact ⟨fun hq => trans_mem S hp hq, fun hq => trans_mem S (symm_mem S hp) hq⟩
  · exact le_antisymm (Mof_le S hp) (Mof_le S (p := (g, g')) (symm_mem S hp))

end GlobalTheory.HL.FrameClass
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameTri

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x a : Fin n → E) :
    hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (c : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * hf L Hm (g i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem coeff_of_mem (g : Fin (r + 1) → S.V) {j : ℕ} {v : S.V} (hv : v ∈ S.spanTo g j) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), j ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun a ha => ?_, ?_⟩
    · have hi' : (i : ℕ) < j := hi
      have : a ≠ i := by rintro rfl; omega
      simp [this]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨a • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

section
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include hg hd in
theorem linInd : LinearIndependent E g := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have key : ∀ y, ∑ a, c a * hf L S.Hm (g a) y = 0 := by
    intro y
    rw [← hf_sum_left, hc]; simp [hf]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := key (g (Fin.last r))
    simp only [hg, and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have hu : IsUnit (-algebraMap F E t) := (t.isUnit.map (algebraMap F E)).neg
    exact (hu.mul_left_eq_zero).1 h
  · have h := key (gs j)
    simpa [hd] using h

include hg in
theorem last_mem_perp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := hi
    have : i ≠ Fin.last r := by rintro rfl; simp at hi'
    simp [hg, this]
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [hf_smul_right, hx, mul_zero]

include hg in
theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) :
    n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨_, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h3.2 _ (last_mem_perp S g t hg)
  · have h := (Subgroup.mem_iInf.1 h2 j).2 (g j.castSucc) (mem_spanTo S g (by simp))
    exact h

include hg in
theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {v : S.V} (hv : v ∈ S.spanTo g j) :
    n v ∈ S.spanTo g j := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < j := hi
    have h := Submodule.add_mem _ (spanTo_mono S g hi'.le (sub_mem S g t hg hn i)) (mem_spanTo S g hi')
    simpa using h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

include hg in
theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (v : S.V) :
    n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem S g t hg hn j⟩
  have h' := map_mem S g t hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n v) = v := n.symm_apply_apply v
  rwa [e] at h'

include hg in
theorem spanTo_comp {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) :
    S.spanTo (fun b => n (g b)) j = S.spanTo g j := by
  have h : S.spanTo (fun b => n (g b)) j = (S.spanTo g j).map (n : S.V →ₗ[E] S.V) := by
    unfold Frames.spanTo
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [h]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem S g t hg hn j hx
  · intro hv
    refine ⟨n.symm v, ?_, by simp⟩
    apply (map_mem_iff S g t hg hn j _).1
    simpa using hv

include hg in
theorem exists_tri {n : S.GLV} (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  choose c hc hc' using fun j => coeff_of_mem S g (sub_mem S g t hg hn j)
  refine ⟨Matrix.of fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i (le_of_lt hij), hij.ne']
  · simp [hc i i le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← hc' j, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp

end

end GlobalTheory.HL.FrameTri

namespace GlobalTheory.HL

theorem frame_unipotent_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → LinearIndependent E g ∧ ∀ n ∈ S.Nof g, (∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (g j) = ∑ i, s i j • g i) ∧ (∀ j, S.spanTo (fun b => n (g b)) j = S.spanTo g j) ∧ (∀ j, ∀ v, n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j) ∧ ∀ v, n v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs h
  obtain ⟨t, hg, hd⟩ : ∃ t : Fˣ, (∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0) ∧
      ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S.T, S.gram, S.dual⟩
    · exact ⟨S.T', S.gram', S.dual'⟩
  exact ⟨FrameTri.linInd S g gs t hg hd, fun n hn => ⟨FrameTri.exists_tri S g t hg hn,
    FrameTri.spanTo_comp S g t hg hn, FrameTri.map_mem_iff S g t hg hn, hn.2.1⟩⟩

end GlobalTheory.HL
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagUnipotent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L H x (a - b) = hf L H x a - hf L H x b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem pow_eq_zero_of_mem_Nof {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (f : Fin (r + 1) → S.V) (g : S.GLV) (hg : g ∈ S.Nof f) :
    ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  obtain ⟨⟨hiso, hfl⟩, hmid⟩ := hg
  have hfl' : ∀ j, j < r → g ∈ unipOn (S.spanTo f (j + 1)) (S.spanTo f j) := fun j hj =>
    (Subgroup.mem_iInf.1 hfl) ⟨j, hj⟩
  set A : S.V →ₗ[E] S.V := (g : S.V →ₗ[E] S.V) - 1 with hA
  have hAv : ∀ v, A v = g v - v := fun v => rfl
  have h0 : S.spanTo f 0 = ⊥ := by simp [Frames.spanTo]
  have ha : ∀ j, j ≤ r → ∀ v, (A ^ j) v ∈ perp L S.Hm (S.spanTo f j) := by
    intro j
    induction j with
    | zero =>
      intro _ v y hy
      rw [h0, Submodule.mem_bot] at hy
      simp [hy, hf]
    | succ j ih =>
      intro hj v x hx
      obtain ⟨h1, h2⟩ := hfl' j hj
      have hw := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply, hAv]
      generalize (A ^ j) v = w at hw
      obtain ⟨y, rfl⟩ := g.surjective x
      have h3 : hf L S.Hm w (g y - y) = 0 := hw _ (h2 y ((h1 y).1 hx))
      have h4 : hf L S.Hm (g w) (g y) = hf L S.Hm w y := hiso w y
      rw [hf_sub_right] at h3
      rw [hf_sub_left, h4]
      linear_combination -h3
  have hc : ∀ j, j ≤ r → ∀ v ∈ S.spanTo f j, (A ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [h0, Submodule.mem_bot] at hv
      simp [hv]
    | succ j ih =>
      intro hj v hv
      rw [pow_succ, Module.End.mul_apply, hAv]
      exact ih (by omega) _ ((hfl' j hj).2 v hv)
  refine LinearMap.ext fun v => ?_
  have e : 2 * r + 1 = r + (1 + r) := by omega
  rw [e, pow_add, pow_add, pow_one, Module.End.mul_apply, Module.End.mul_apply, hAv]
  exact hc r le_rfl _ (hmid.2 _ (ha r le_rfl v))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 :=
  fun _ _ _ S g hg => pow_eq_zero_of_mem_Nof S S.f g hg

end GlobalTheory.FlagUnipotent
end
end

section

open Matrix Finset Real

theorem _root_.GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred : ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 → ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) → min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  first | exact @GlobalTheory.cumulant_lower_bound_of_bounded_centred | exact GlobalTheory.cumulant_lower_bound_of_bounded_centred | (intros; apply GlobalTheory.cumulant_lower_bound_of_bounded_centred <;> assumption)
end
