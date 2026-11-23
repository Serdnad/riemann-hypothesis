module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle001
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin sg)
open CompanionTheory.D.LK.Car (ann_apply cre_apply sg_erase tw_self)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cn n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sg_conj (i : Pos n) (A : Finset (Pos n)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

theorem sg_erase_self (i : Pos n) {A : Finset (Pos n)} (h : i ∈ A) : sg i (A.erase i) = sg i A := by
  rw [sg_erase i h, tw_self, one_mul]

theorem ip_cre (i : Pos n) (x z : Cn n V) : ip (cre i x) z = ip x (ann i z) := by
  unfold ip
  have h1 : ∀ A : Finset (Pos n), ⟪cre i x A, z A⟫_ℂ =
      if i ∈ A then sg i A * ⟪x (A.erase i), z A⟫_ℂ else 0 := fun A => by
    rw [cre_apply]
    split_ifs
    · rw [inner_smul_left, sg_conj]
    · simp
  have h2 : ∀ A : Finset (Pos n), ⟪x A, ann i z A⟫_ℂ =
      if i ∈ A then 0 else sg i A * ⟪x A, z (insert i A)⟫_ℂ := fun A => by
    rw [ann_apply]
    split_ifs
    · simp
    · rw [inner_smul_right]
  simp only [h1, h2]
  rw [← Finset.sum_filter, Finset.sum_ite, Finset.sum_const_zero, zero_add]
  refine Finset.sum_bij' (fun A _ => A.erase i) (fun A _ => insert i A) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp
  · intro A hA
    simp
  · intro A hA
    exact Finset.insert_erase (by simpa using hA)
  · intro A hA
    exact Finset.erase_insert (by simpa using hA)
  · intro A hA
    have hA' : i ∈ A := by simpa using hA
    rw [sg_erase_self i hA', Finset.insert_erase hA']

theorem ip_conj (x z : Cn n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold ip

  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm _ _

theorem ip_ann (i : Pos n) (x z : Cn n V) : ip (ann i x) z = ip x (cre i z) := by
  rw [← ip_conj, ← ip_cre, ip_conj]

theorem ip_cre_ann (i k : Pos n) (x z : Cn n V) :
    ip ((cre k * ann i : Module.End ℂ (Cn n V)) x) z = ip x ((cre i * ann k : Module.End ℂ (Cn n V)) z) := by
  simp only [Module.End.mul_apply]
  rw [ip_cre, ip_ann]

theorem ip_add_left (x y z : Cn n V) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]

theorem ip_add_right (x y z : Cn n V) : ip x (y + z) = ip x y + ip x z := by
  simp only [ip, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem ip_smul_left (c : ℂ) (x z : Cn n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_left, Finset.mul_sum]

theorem ip_smul_right (c : ℂ) (x z : Cn n V) : ip x (c • z) = c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_right, Finset.mul_sum]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cn n V) (z : Cn n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  simp only [ip, Finset.sum_apply, sum_inner]
  exact Finset.sum_comm

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cn n V) (f : ι → Cn n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  simp only [ip, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem adC_conj (p q : Fin n) (i k : Pos n) : (starRingEnd ℂ) (adC p q i k) = adC p q i k := by
  unfold adC
  split_ifs <;> simp

theorem adC_swap (p q : Fin n) (i k : Pos n) : adC p q i k = adC q p k i := by
  have e1 : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ↔ (p = k.1.1 ∧ i.1 = (q, k.1.2)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  have e2 : (i.1.2 = p ∧ k.1 = (i.1.1, q)) ↔ (k.1.2 = q ∧ i.1 = (k.1.1, p)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  unfold adC
  simp only [e1, e2]

theorem ip_adL (p q : Fin n) (x z : Cn n V) : ip (adL p q x) z = ip x (adL q p z) := by
  simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, ip_sum_left, ip_sum_right, ip_smul_left,
    ip_smul_right, adC_conj, ip_cre_ann]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [adC_swap]

theorem ip_lift {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) {p q : Fin n}
    (h : ε p = ε q) (x z : Cn n V) : ip (lift n (E p q) x) z = ip x (lift n (E q p) z) :=
  Finset.sum_congr rfl fun A _ => hU p q h (x A) (z A)

theorem lF_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  intro n ε V _ _ E hU p q h x z
  change ip (lF E p q x) z = ip x (lF E q p z)
  simp only [lF, LinearMap.add_apply, ip_add_left, ip_add_right]
  rw [ip_lift hU h, ip_adL]

end GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.FarReg.BdProd

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_sq (k : Pos n) : (cre k * cre k : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply, CompanionTheory.D.LK.Car.cre_apply]
  by_cases h : k ∈ A <;> simp [h]

theorem cre_anti (i j : Pos n) : (cre i * cre j : Module.End ℂ (Cn n V)) = -(cre j * cre i) :=
  eq_neg_of_add_eq_zero_left (CompanionTheory.D.LK.Car.cre_cre i j)

theorem cre_mul_prod_of_mem {k : Pos n} {l : List (Pos n)} (h : k ∈ l) :
    (cre k * (l.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
  induction l with
  | nil => simp at h
  | cons g t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hk : k = g
    · subst hk
      rw [← mul_assoc, cre_sq, zero_mul]
    · have h1 := ih ((List.mem_cons.1 h).resolve_left hk)
      rw [← mul_assoc, cre_anti, neg_mul, mul_assoc, h1, mul_zero, neg_zero]

theorem term_comm (k i g : Pos n) :
    (cre k * ann i * cre g - cre g * (cre k * ann i) : Module.End ℂ (Cn n V)) = if i = g then cre k else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) i g
  rw [mul_assoc, eq_sub_of_add_eq h1, mul_sub, ← mul_assoc (cre k) (cre g), cre_anti k g, neg_mul, mul_assoc (cre g),
    sub_neg_eq_add, add_sub_cancel_right]
  split_ifs <;> simp

theorem adL_cre (p q : Fin n) (g : Pos n) :
    (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) = ∑ k : Pos n, adC p q g k • cre k := by
  have h : (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i * cre g - cre g * (cre k * ann i)) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm]
  rw [Finset.sum_eq_single g]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem lF_cre (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (g : Pos n) :
    (lF E p q * cre g : Module.End ℂ (Cn n V)) = cre g * lF E p q + ∑ k : Pos n, adC p q g k • cre k := by
  have h1 : (lift n (E p q) * cre g : Module.End ℂ (Cn n V)) = cre g * lift n (E p q) :=
    LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre (E p q) g x
  rw [← adL_cre, lF, add_mul, mul_add, h1]
  abel

theorem lF_prod (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : List (Pos n))
    (h : ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ k : Pos n,
      adC p q f k ≠ 0 → k ∈ post) :
    (lF E p q * (l.map cre).prod : Module.End ℂ (Cn n V)) = (l.map cre).prod * lF E p q := by
  induction l with
  | nil => simp
  | cons g t ih =>
    have ht := ih fun pre f post e k hk => h (g :: pre) f post (by rw [e]; rfl) k hk
    have hz : ((∑ k : Pos n, adC p q g k • cre k) * (t.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : adC p q g k = 0
      · rw [hk, zero_smul, zero_mul]
      · rw [smul_mul_assoc, cre_mul_prod_of_mem (h [] g t rfl k hk), smul_zero]
    rw [List.map_cons, List.prod_cons, ← mul_assoc, lF_cre, add_mul, hz, add_zero, mul_assoc, ht, mul_assoc]

theorem bd_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  intro n V _ _ E hC l x
  induction l with
  | nil => intro _ _; simp
  | cons f t ih =>
    intro hcl hx
    have ih' := ih (fun pre g post e a ha k hk =>
      hcl (f :: pre) g post (by rw [e]; rfl) a (List.mem_cons_of_mem _ ha) k hk)
      (fun e he => hx e (List.mem_cons_of_mem _ he))
    have hf : lF E f.1.1 f.1.2 (((t.map cre).prod : Module.End ℂ (Cn n V)) x) = 0 := by
      have h1 := lF_prod E f.1.1 f.1.2 t (fun pre g post e k hk =>
        hcl (f :: pre) g post (by rw [e]; rfl) f List.mem_cons_self k hk)
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply] at h2
      rw [h2, hx f List.mem_cons_self, map_zero]
    have h3 := LinearMap.congr_fun (hC f) (((t.map cre).prod : Module.End ℂ (Cn n V)) x)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hf, ih'] at h3
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, map_smul]
    rw [eq_neg_of_add_eq_zero_left h3, mul_neg_one, neg_smul, map_smul]

end GlobalTheory.CompanionTheory.FarReg.BdProd
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Cartan

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem anticommutator_triple_product {R : Type*} [Ring R] (K Aj Ai C d₁ d₂ : R) (h₁ : Ai * C + C * Ai = d₁)
    (h₂ : Aj * C + C * Aj = d₂) (h₃ : K * C + C * K = 0) :
    K * Aj * Ai * C + C * (K * Aj * Ai) = K * Aj * d₁ - K * d₂ * Ai := by
  subst h₁ h₂
  have h : C * K = -(K * C) := eq_neg_of_add_eq_zero_right h₃
  have h' : C * (K * Aj * Ai) = -(K * C * Aj * Ai) := by
    rw [← mul_assoc, ← mul_assoc, h]; noncomm_ring
  rw [h']
  noncomm_ring

theorem tri_anti (i j k e : Pos n) :
    (cre k * ann j * ann i * cre e + cre e * (cre k * ann j * ann i) : Module.End ℂ (Cn n V)) =
      (if i = e then cre k * ann j else 0) - (if j = e then cre k * ann i else 0) := by
  rw [anticommutator_triple_product _ _ _ _ _ _ (CompanionTheory.D.LK.Car.ann_cre i e) (CompanionTheory.D.LK.Car.ann_cre j e)
    (CompanionTheory.D.LK.Car.cre_cre k e)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem cre_mul_lift (φ : Module.End ℂ V) (e : Pos n) :
    (cre e * (lift n φ : Module.End ℂ (Cn n V)) : Module.End ℂ (Cn n V)) = (lift n φ : Module.End ℂ (Cn n V)) * cre e :=
  LinearMap.ext fun x => (CompanionTheory.D.LK.lift_cre φ e x).symm

theorem part_one (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    ((∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0 :
      Module.End ℂ (Cn n V)) = lift n (E e.1.1 e.1.2) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ i : Pos n,
      ((if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) :
        Module.End ℂ (Cn n V)) = if i = e then (lift n (E e.1.1 e.1.2) : Module.End ℂ (Cn n V)) else 0 := by
    intro i
    rw [if_pos (rfl : cpt (allT n) i), ← mul_assoc (cre e), cre_mul_lift, mul_assoc, mul_assoc, ← mul_add,
      CompanionTheory.D.LK.Car.ann_cre]
    by_cases hi : i = e
    · subst hi; simp
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

theorem sum_anti {R : Type*} [Ring R] (T P Q : Pos n → Pos n → Pos n → R) (c : R)
    (h : ∀ i j k, T i j k * c + c * T i j k = P i j k - Q i j k) :
    (∑ i, ∑ j, ∑ k, T i j k) * c + c * ∑ i, ∑ j, ∑ k, T i j k =
      ∑ i, ∑ j, ∑ k, P i j k - ∑ i, ∑ j, ∑ k, Q i j k := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, h, Finset.sum_sub_distrib]

theorem part_two (e : Pos n) :
    ((∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0 : Module.End ℂ (Cn n V)) = adL e.1.1 e.1.2 := by
  have h : ∀ i j k : Pos n,
      ((if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) : Module.End ℂ (Cn n V)) =
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0) -
        (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0) := by
    intro i j k
    by_cases ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
    · rw [if_pos ⟨rfl, rfl, ht⟩, tri_anti]
      obtain ⟨t1, t2, t3⟩ := ht
      congr 1
      · by_cases hi : i = e
        · subst hi
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hi, if_neg fun c => hi c.1]
      · by_cases hj : j = e
        · subst hj
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hj, if_neg fun c => hj c.1]
    · rw [if_neg fun c => ht c.2.2, zero_mul, mul_zero, add_zero, if_neg, if_neg, sub_zero]
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
  rw [sum_anti _ _ _ _ h]
  have s₁ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V))) =
      ∑ j : Pos n, ∑ k : Pos n,
        (if e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V)) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have s₂ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V))) =
      ∑ i : Pos n, ∑ k : Pos n,
        (if i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [s₁, s₂]
  simp only [adL, adC, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]

theorem cartan (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  have h₁ := part_one E e
  have h₂ := part_two (V := V) e
  unfold bd lF
  rw [add_mul, mul_add, add_add_add_comm, h₁, h₂]

end GlobalTheory.CompanionTheory.Cartan
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExh

theorem adC_mem_omU {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hε : ε p = ε q)
    (hl : lev p = lev q) {i k : Pos n} (hc : adC p q i k ≠ 0) (hi : i ∈ omU ε lev) :
    k ∈ omU ε lev ∧ k ≠ i := by
  have hcase : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adC, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := (mem_filter.1 hi).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε p = ε i.1.2; rw [hε, e1, h1]
    · rw [e2]; show lev p < lev i.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε i.1.1 = ε q; rw [h1, e1, hε]
    · rw [e2]; show lev i.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem lF_single_omU : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  intro n ε lev V _ _ E γ u hu p q hpq hε hl
  have hE : E p q u = 0 := hu.2 p q hpq hε
  have h1 : lift n (E p q) (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases e : A = omU ε lev
    · subst e
      rw [Pi.single_eq_same]
      exact hE
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adL p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hc : adC p q i k = 0
    · rw [hc, zero_smul]
    suffices h : cre k (ann i (Pi.single (omU ε lev) u : Cn n V)) = 0 by rw [h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := CompanionTheory.D.LK.cre_ne h
    obtain ⟨-, h4⟩ := CompanionTheory.D.LK.ann_ne h3
    have e : insert i (B.erase k) = omU ε lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hi : i ∈ omU ε lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hki⟩ := adC_mem_omU hpq hε hl hc hi
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hki h5
    · exact notMem_erase _ _ h5
  show lift n (E p q) _ + adL p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.RgExh
end
end
