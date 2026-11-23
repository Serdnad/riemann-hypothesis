module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open scoped BigOperators
open Polynomial

namespace GlobalTheory.BlockDet

def blk {B : Type} {g n : ℕ} (M : Fin g → Fin g → Matrix (Fin n) (Fin n) B) :
    Matrix (Fin g × Fin n) (Fin g × Fin n) B :=
  Matrix.of fun pa qb => M pa.1 qb.1 pa.2 qb.2

def splitIdx (g n : ℕ) : Fin n ⊕ (Fin g × Fin n) ≃ Fin (g + 1) × Fin n where
  toFun := Sum.elim (fun a => (0, a)) (fun pa => (pa.1.succ, pa.2))
  invFun := fun pa => Fin.cases (motive := fun _ => Fin n ⊕ (Fin g × Fin n)) (Sum.inl pa.2)
    (fun p => Sum.inr (p, pa.2)) pa.1
  left_inv := by rintro (a | ⟨p, a⟩) <;> simp
  right_inv := by
    rintro ⟨p, a⟩
    refine Fin.cases ?_ (fun p => ?_) p <;> simp

theorem det_one_add_smul_blk_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B)
    (A : Subring (Matrix (Fin n) (Fin n) B)) (hdet : ∀ a ∈ A, a.det ∈ S) (e : B)
    (he : IsNilpotent e) (heA : ∀ a ∈ A, e • a ∈ A) (g : ℕ) :
    ∀ Θ : Fin g → Fin g → Matrix (Fin n) (Fin n) B, (∀ p q, Θ p q ∈ A) →
      (1 + e • blk Θ).det ∈ S := by
  induction g with
  | zero => intro Θ _; rw [Matrix.det_isEmpty]; exact S.one_mem
  | succ g ih =>
    intro Θ hΘ
    have hnil : IsNilpotent (⟨e • Θ 0 0, heA _ (hΘ 0 0)⟩ : A) := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k, Subtype.ext ?_⟩
      simp [_root_.smul_pow, hk]
    obtain ⟨w, hw⟩ := hnil.isUnit_one_add
    set u : Matrix (Fin n) (Fin n) B := ((w⁻¹ : Aˣ) : A).1 with hu
    have huA : u ∈ A := ((w⁻¹ : Aˣ) : A).2
    have hw' : ((w : A) : Matrix (Fin n) (Fin n) B) = 1 + e • Θ 0 0 := by rw [hw]; rfl
    letI : Invertible (1 + e • Θ 0 0) :=
      ⟨u, by rw [← hw', hu, ← Subring.coe_mul]; simp, by rw [← hw', hu, ← Subring.coe_mul]; simp⟩
    have hinv : ⅟(1 + e • Θ 0 0) = u := rfl
    let Bm : Matrix (Fin n) (Fin g × Fin n) B := Matrix.of fun a qb => Θ 0 qb.1.succ a qb.2
    let Cm : Matrix (Fin g × Fin n) (Fin n) B := Matrix.of fun pa b => Θ pa.1.succ 0 pa.2 b
    have h1 : (1 + e • blk Θ).submatrix (splitIdx g n) (splitIdx g n) =
        Matrix.fromBlocks (1 + e • Θ 0 0) (e • Bm) (e • Cm)
          (1 + e • blk (fun p q => Θ p.succ q.succ)) := by
      ext (a | ⟨p, a⟩) (b | ⟨q, b⟩) <;>
        simp [splitIdx, blk, Bm, Cm, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
    have h2 : (1 + e • blk (fun p q => Θ p.succ q.succ)) - (e • Cm) * u * (e • Bm) =
        1 + e • blk (fun p q => Θ p.succ q.succ - e • (Θ p.succ 0 * u * Θ 0 q.succ)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_sub_assoc, ← smul_sub]
      congr 2
    rw [← Matrix.det_submatrix_equiv_self (splitIdx g n), h1, Matrix.det_fromBlocks₁₁, hinv, h2]
    refine S.mul_mem (hdet _ (A.add_mem A.one_mem (heA _ (hΘ 0 0)))) (ih _ fun p q => ?_)
    exact A.sub_mem (hΘ _ _) (heA _ (A.mul_mem (A.mul_mem (hΘ _ _) huA) (hΘ _ _)))

def swapM {O X : Type} {n : ℕ} (a : X → Matrix (Fin n) (Fin n) O) :
    Matrix (Fin n) (Fin n) (X → O) :=
  Matrix.of fun i j x => a x i j

theorem det_sum_smul_mem {O X B : Type} [CommRing O] [CommRing B] (T : Subalgebra O (X → O))
    {n : ℕ} (ι : (X → O) →+* B) (S : Subring B) (hS : ∀ t ∈ T, ι t ∈ S) {m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O)
    (h : ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
      (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T)
    (c : Fin m → B) (hc : ∀ k, c k ∈ S) :
    (∑ k, c k • (swapM (a k)).map ι).det ∈ S := by
  set D : MvPolynomial (Fin m) (X → O) := Matrix.det
    (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (swapM (a k)).map MvPolynomial.C)
    with hD
  have hco : ∀ d, AddMonoidAlgebra.coeff D d ∈ T := by
    intro d
    convert h d using 1
    funext x
    have : AddMonoidAlgebra.coeff D d x =
        AddMonoidAlgebra.coeff (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) D) d := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [this, hD, RingHom.map_det]
    have hm : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        (swapM (a k)).map MvPolynomial.C).map (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map (MvPolynomial.C (σ := Fin m)) := by
      ext i j
      simp [swapM, Matrix.sum_apply]
    exact congrArg (fun M => AddMonoidAlgebra.coeff (Matrix.det M) d) hm
  have hev : (∑ k, c k • (swapM (a k)).map ι).det = MvPolynomial.eval₂Hom ι c D := by
    rw [hD, RingHom.map_det]
    congr 1
    ext i j : 1
    simp [Matrix.sum_apply]
  rw [hev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hco d)) (S.prod_mem fun k _ => S.pow_mem (hc k) _)

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T) → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, Θ p q ∈ R) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro O X _ T n R hR g Θ hΘ
  set N := Fintype.card (Fin g × Fin n) with hN
  let I : Ideal (X → O)[X] := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : (X → O)[X] →+* (X → O)[X] ⧸ I := Ideal.Quotient.mk I
  let ι : (X → O) →+* (X → O)[X] ⧸ I := π.comp Polynomial.C
  let S : Subring ((X → O)[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.val.toRingHom)).range
  have hS : ∀ t ∈ T, ι t ∈ S := fun t ht => ⟨Polynomial.C ⟨t, ht⟩, by simp [ι]⟩
  have heS : π Polynomial.X ∈ S := ⟨Polynomial.X, by simp⟩
  have he : IsNilpotent (π Polynomial.X) :=
    ⟨N + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)⟩
  let G : Set (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    {M | ∃ a ∈ R, (swapM a).map ι = M}
  have hone : (1 : Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) ∈ G := by
    refine ⟨1, R.one_mem, ?_⟩
    have : swapM (1 : X → Matrix (Fin n) (Fin n) O) = 1 := by
      ext i j x
      simp [swapM, Matrix.one_apply, apply_ite (fun f : X → O => f x)]
    rw [this, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hmul : ∀ M ∈ G, ∀ M' ∈ G, M * M' ∈ G := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, R.mul_mem ha hb, ?_⟩
    rw [← Matrix.map_mul]
    congr 1
    ext i j x
    simp [swapM, Matrix.mul_apply]
  let A : Subalgebra S (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    (Submodule.span S G).toSubalgebra (Submodule.subset_span hone) (by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨M, hM, M', hM', rfl⟩
      exact hmul M hM M' hM')
  have hdet : ∀ a ∈ A.toSubring, a.det ∈ S := by
    intro a ha
    obtain ⟨m, c, f, rfl⟩ := Submodule.mem_span_set'.1 (show a ∈ Submodule.span S G from ha)
    choose b hb hbf using fun k => (f k).2
    have := det_sum_smul_mem T ι S hS b (hR m b hb) (fun k => c k) (fun k => (c k).2)
    simp only [hbf] at this
    exact this
  have key := det_one_add_smul_blk_mem S A.toSubring hdet (π Polynomial.X) he
    (fun a ha => A.smul_mem ha (⟨_, heS⟩ : S)) g (fun p q => (swapM (Θ p q)).map ι)
    (fun p q => Submodule.subset_span (R := S) (s := G) ⟨_, hΘ p q, rfl⟩)
  set M : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O) := blk fun p q => swapM (Θ p q) with hM
  set F : (X → O)[X] := Matrix.det ((Polynomial.X : (X → O)[X]) • M.map Polynomial.C +
    (1 : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O)).map Polynomial.C) with hF
  have hπ : (1 + π Polynomial.X • blk fun p q => (swapM (Θ p q)).map ι).det = π F := by
    rw [hF, RingHom.map_det, Matrix.map_one _ (map_zero _) (map_one _), map_add (f := _), map_one, add_comm]
    congr 2
  rw [hπ] at key
  obtain ⟨t, ht⟩ := key
  have hdvd : Polynomial.X ^ (N + 1) ∣ t.map T.val.toRingHom - F :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ht)
  have hc := Polynomial.X_pow_dvd_iff.1 hdvd N (Nat.lt_succ_self N)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, hF, hN, Polynomial.coeff_det_X_add_C_card,
    sub_eq_zero] at hc
  have hmem : M.det ∈ T := by rw [← hc]; exact (t.coeff _).2
  convert hmem using 1
  funext x
  exact ((Pi.evalRingHom (fun _ : X => O) x).map_det M).symm

end GlobalTheory.BlockDet
end

section

noncomputable section

namespace GlobalTheory.NormUnits

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

def intRing : Subring K where
  carrier := Metric.closedBall 0 1
  mul_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem norm_le_one (x : intRing K) : ‖(x : K)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2

def maxIdeal : Ideal (intRing K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖(a : K) + b‖ < 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by show ‖((0 : intRing K) : K)‖ < 1; simp
  smul_mem' c x hx := by
    show ‖(c : K) * x‖ < 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one K c)).trans_lt hx

theorem mem_maxIdeal (x : intRing K) : x ∈ maxIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

instance maxIdeal_isMaximal : (maxIdeal K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => by rw [mem_maxIdeal] at h; simp at h, fun J x hle hx hxJ => ?_⟩
  rw [mem_maxIdeal, not_lt] at hx
  have h1 : ‖(x : K)‖ = 1 := le_antisymm (norm_le_one K x) hx
  have hx0 : (x : K) ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  let y : intRing K := ⟨(x : K)⁻¹, mem_closedBall_zero_iff.2 (by rw [norm_inv, h1, inv_one])⟩
  have hyx : y * x = 1 := Subtype.ext (by simp [y, inv_mul_cancel₀ hx0])
  rw [← hyx]; exact J.mul_mem_left y hxJ

theorem finite_res [LocallyCompactSpace K] : Finite (intRing K ⧸ maxIdeal K) := by
  haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
  haveI : CompactSpace (intRing K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : K) 1)
  have hopen : IsOpen ((maxIdeal K : Set (intRing K))) := by
    have e : ((maxIdeal K : Set (intRing K))) = Subtype.val ⁻¹' Metric.ball (0 : K) 1 := by
      ext x; simp [mem_maxIdeal]
    rw [e]; exact Metric.isOpen_ball.preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen (maxIdeal K).toAddSubgroup hopen

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits
open MvPolynomial

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

abbrev Res : Type := intRing K ⧸ maxIdeal K

instance : Field (Res K) := Ideal.Quotient.field _

theorem totalDegree_C_mul_X_mul_X {k : Type} [Field k] (r : k) (i j : Fin 3) :
    (C r * (X i * X j) : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]

theorem exists_point_mod [LocallyCompactSpace K] (s t c : K) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ∃ a b z : K, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖z‖ ≤ 1 ∧ (‖a‖ = 1 ∨ ‖b‖ = 1 ∨ ‖z‖ = 1) ∧
      ‖a ^ 2 + s * a * b + t * b ^ 2 - c * z ^ 2‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let k := Res K
  let π : intRing K →+* k := Ideal.Quotient.mk _
  let S : intRing K := ⟨s, mem_closedBall_zero_iff.2 hs⟩
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  let Cc : intRing K := ⟨c, mem_closedBall_zero_iff.2 hc⟩
  set p := ringChar k
  haveI : CharP k p := ringChar.charP k
  obtain ⟨n, hpp, -⟩ := FiniteField.card (K := k) p
  let f : MvPolynomial (Fin 3) k := C 1 * (X 0 * X 0) + C (π S) * (X 0 * X 1) + C (π T) * (X 1 * X 1) +
    C (-π Cc) * (X 2 * X 2)
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have h1 := totalDegree_C_mul_X_mul_X (1 : k) 0 0
    have h2 := totalDegree_C_mul_X_mul_X (π S) 0 1
    have h3 := totalDegree_C_mul_X_mul_X (π T) 1 1
    have h4 := totalDegree_C_mul_X_mul_X (-π Cc) 2 2
    have := (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le h1 h2)) h3)) h4)
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt this (by norm_num)
  have hdvd := char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    Fintype.card_pos_iff.2 ⟨⟨0, by simp [f]⟩⟩
  have h1lt : 1 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, by simp [f]⟩
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  choose l hl using fun i => Ideal.Quotient.mk_surjective (I := maxIdeal K) (x.1 i)
  have hval : π (l 0 * l 0 + S * (l 0 * l 1) + T * (l 1 * l 1) + (-Cc) * (l 2 * l 2)) = 0 := by
    have := x.2
    simp only [f, eval_add, eval_mul, eval_C, eval_X, one_mul] at this
    simp only [map_add, map_mul, map_neg, π, hl]
    linear_combination this
  have hmem := (Ideal.Quotient.eq_zero_iff_mem).1 hval
  rw [mem_maxIdeal] at hmem
  have hunit : ∀ i, x.1 i ≠ 0 → ‖((l i : intRing K) : K)‖ = 1 := by
    intro i hi
    refine le_antisymm (norm_le_one K _) (not_lt.1 fun h => hi ?_)
    rw [← hl i]; exact (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 h)
  refine ⟨l 0, l 1, l 2, norm_le_one K _, norm_le_one K _, norm_le_one K _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    fin_cases i
    · exact Or.inl (hunit 0 hi)
    · exact Or.inr (Or.inl (hunit 1 hi))
    · exact Or.inr (Or.inr (hunit 2 hi))
  · convert hmem using 2
    simp only [S, T, Cc, Subring.coe_add, Subring.coe_mul, Subring.coe_neg]
    ring

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

theorem exists_sqrt_mod [LocallyCompactSpace K] (t : K) (ht : ‖t‖ ≤ 1) (h2 : ‖(2 : K)‖ < 1) :
    ∃ r : K, ‖r‖ ≤ 1 ∧ ‖r ^ 2 - t‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  have h2k : (2 : Res K) = 0 := by
    have h11 : (((1 + 1 : intRing K)) : K) = 2 := by
      rw [Subring.coe_add, Subring.coe_one]; norm_num
    have : (Ideal.Quotient.mk (maxIdeal K) (1 + 1) : Res K) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 (by rw [h11]; exact h2))
    rw [map_add (f := _), map_one] at this
    rw [← one_add_one_eq_two]; exact this
  have hchar : ringChar (Res K) = 2 := by
    have hd : ringChar (Res K) ∣ 2 := ringChar.dvd (by exact_mod_cast h2k)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two hchar (Ideal.Quotient.mk (maxIdeal K) T)
  obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨l, norm_le_one K l, ?_⟩
  have h0 : Ideal.Quotient.mk (maxIdeal K) (l * l - T) = 0 := by
    rw [map_sub, map_mul, ← hy, sub_self]
  have hm := (mem_maxIdeal K _).1 ((Ideal.Quotient.eq_zero_iff_mem).1 h0)
  simpa [sq, T] using hm

end GlobalTheory.NormUnits
end
end

section

namespace GlobalTheory.AevalCommute

theorem pow_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (n : ℕ) (y : M) :
    J ((ν ^ n) y) = (μ ^ n) (J y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hνμ]

theorem aeval_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (hJ : ∀ (c : O) (y : M), J (c • y) = algebraMap O k c • J y)
    (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, hJ, pow_apply_comm J ν μ hνμ]

theorem main : ∀ {O : Type} [inst : CommRing O] {k : Type} [inst_1 : Field k] [inst_2 : Algebra O k] {M V : Type} [inst_3 : AddCommGroup M] [inst_4 : Module O M] [inst_5 : AddCommGroup V] [inst_6 : Module k V] (J : M →+ V), (∀ (c : O) (y : M), (J : M → V) (c • y) = (Algebra.algebraMap O k : O → k) c • (J : M → V) y) → ∀ (ν : Module.End O M) (μ : Module.End k V), (∀ (y : M), (J : M → V) ((ν : M → M) y) = (μ : V → V) ((J : M → V) y)) → ∀ (f : Polynomial O) (y : M), (J : M → V) (((Polynomial.aeval ν : Polynomial O → Module.End O M) f : M → M) y) = ((Polynomial.aeval μ : Polynomial k → Module.End k V) (Polynomial.map (Algebra.algebraMap O k) f) : V → V) ((J : M → V) y) :=
  fun J hJ ν μ hνμ f y => aeval_apply_comm J hJ ν μ hνμ f y

end GlobalTheory.AevalCommute
end

section

namespace GlobalTheory.AevalIntertwine

theorem aeval_intertwine : ∀ {K M N : Type} [inst : Field K] [inst_1 : AddCommGroup M] [inst_2 : Module K M] [inst_3 : AddCommGroup N] [inst_4 : Module K N] (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N), (∀ (x : M), (f : M → N) ((A : M → M) x) = (B : N → N) ((f : M → N) x)) → ∀ (p : Polynomial K) (x : M), (f : M → N) (((Polynomial.aeval A : Polynomial K → Module.End K M) p : M → M) x) = ((Polynomial.aeval B : Polynomial K → Module.End K N) p : N → N) ((f : M → N) x) := by
  intro K M N _ _ _ _ _ f A B h p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  · intro p q hp hq x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  · intro n a ih x
    have e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V),
        Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y
          = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y) := by
      intro V _ _ E y
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e, e, ih, h]

end GlobalTheory.AevalIntertwine
end

section

namespace GlobalTheory.PowerMembershipInertiaEigenvalues

theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add (f := _), LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
end

section

namespace GlobalTheory.CommuteInvLeft

theorem commute_inv_left : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  have h' : x * y = y * x := h
  show xi * y = y * xi
  calc xi * y = xi * y * (x * xi) := by rw [h1, mul_one]
    _ = xi * (y * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * y) * xi := by rw [h']
    _ = (xi * x) * y * xi := by simp only [mul_assoc]
    _ = y * xi := by rw [h2, one_mul]

end GlobalTheory.CommuteInvLeft
end
