module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Development.EtaleCohomology.DivisorCycles.Bundle002
public import Development.EtaleCohomology.DivisorCycles.Bundle001
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.GradePf

section
variable {C : Type} [Field C] {N n : ℕ}

noncomputable def adX (X : Mat C N) : Module.End C (Mat C N) :=
  LinearMap.mulLeft C X - LinearMap.mulRight C X

lemma adX_apply (X Y : Mat C N) : adX X Y = X * Y - Y * X := by
  simp [adX]

lemma pow_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (k : ℕ) : ∀ Y ∈ g, (f ^ k) Y ∈ g := by
  induction k with
  | zero => intro Y hY; simpa using hY
  | succ k ih => intro Y hY; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih Y hY)

lemma aeval_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (q : C[X]) : ∀ Y ∈ g, aeval f q Y ∈ g := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro Y hY; simp only [map_add (f := _), LinearMap.add_apply]; exact g.add_mem (hp Y hY) (hq Y hY)
  | monomial k a =>
    intro Y hY
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact g.smul_mem _ (pow_mem f g hf k Y hY)

lemma pow_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (k : ℕ) :
    (f ^ k) Z = c ^ k • Z := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

lemma aeval_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (q : C[X]) :
    aeval f q Z = q.eval c • Z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_eig f Z c h, smul_smul,
      eval_monomial]

lemma lac_key [CharZero C] {e : Fin n → C} (hL : IsLac e) {i j k l : Fin n} (hij : i ≠ j)
    (h : e i - e j = e k - e l) : k = i ∧ l = j := by
  have inj := isLac_inj hL
  have h' : e i + e l = e k + e j := by linear_combination h
  by_contra hne
  have hki : k ≠ i := by
    intro hk; rw [hk] at h'
    exact hne ⟨hk, inj (by linear_combination h')⟩
  have hlj : l ≠ j := by
    intro hl; rw [hl] at h'
    exact hne ⟨(inj (by linear_combination h')).symm, hl⟩
  have hkl : k ≠ l := by
    intro hk; rw [hk] at h; exact hij (inj (by linear_combination h))
  by_cases hil : i = l
  · subst hil
    by_cases hkj : k = j
    · subst hkj
      exact hki (inj (mul_left_cancel₀ (two_ne_zero (α := C)) (by linear_combination -h')))
    · have := hL {i} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hki.symm, hij⟩)
      apply this
      rw [Finset.card_pair hkj, Finset.sum_pair hkj]; simp; linear_combination h'
  · by_cases hkj : k = j
    · subst hkj
      have := hL {i, l} {k} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hij, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil]; simp; linear_combination h'
    · have := hL {i, l} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨⟨hki.symm, hij⟩, hkl.symm, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil, Finset.card_pair hkj, Finset.sum_pair hkj]
      rw [h']
end

end LateralTheory.DivDb.GradePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.GradePf

theorem Grade_of : Grade := by
  intro C _ _ N n p e g hS hL hg Y hY i j hij
  set X := ∑ i, e i • p i with hXdef
  have hco := hS.1
  have hid : ∀ k, p k * p k = p k := fun k => hco.idem k
  have hor : ∀ k l, k ≠ l → p k * p l = 0 := fun k l h => hco.ortho h
  have hsum : ∑ k, p k = 1 := hco.complete
  have hXp : ∀ k, X * p k = e k • p k := by
    intro k; rw [hXdef, Finset.sum_mul]; simp only [smul_mul_assoc]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor b k hb, smul_zero]
    · simp
  have hpX : ∀ k, p k * X = e k • p k := by
    intro k; rw [hXdef, Finset.mul_sum]; simp only [mul_smul_comm]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor k b (Ne.symm hb), smul_zero]
    · simp
  have hdec : Y = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
    have : (∑ k, p k) * Y * (∑ l, p l) = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
      rw [Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]; simp_rw [Finset.mul_sum]
    rw [← this, hsum, one_mul, mul_one]
  have heig : ∀ kl : Fin n × Fin n, adX X (p kl.1 * Y * p kl.2) = (e kl.1 - e kl.2) • (p kl.1 * Y * p kl.2) := by
    intro kl
    rw [adX_apply, ← mul_assoc, ← mul_assoc, hXp, mul_assoc (p kl.1 * Y), hpX]
    simp [sub_smul, smul_mul_assoc, mul_smul_comm]
  have hstab : ∀ Z ∈ g, adX X Z ∈ g := fun Z hZ => by rw [adX_apply]; exact hg Z hZ
  let q : C[X] := ∏ kl ∈ (Finset.univ : Finset (Fin n × Fin n)).erase (i, j), (Polynomial.X - Polynomial.C (e kl.1 - e kl.2))
  have hq : aeval (adX X) q Y = q.eval (e i - e j) • (p i * Y * p j) := by
    conv_lhs => rw [hdec]

    rw [map_sum]
    simp_rw [aeval_eig (adX X) _ _ (heig _)]
    rw [Finset.sum_eq_single (i, j)]
    · intro b _ hb
      have : q.eval (e b.1 - e b.2) = 0 := by
        simp only [q, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩) (by simp)
      rw [this, zero_smul]
    · simp
  have hq0 : q.eval (e i - e j) ≠ 0 := by
    simp only [q, eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro kl hkl
    simp only [eval_sub, eval_X, eval_C]
    intro h0
    have := lac_key hL hij (sub_eq_zero.mp h0)
    exact (Finset.mem_erase.mp hkl).1 (Prod.ext this.1 this.2)
  have hm := g.smul_mem (q.eval (e i - e j))⁻¹ (aeval_mem (adX X) g hstab q Y hY)
  rwa [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul] at hm

end LateralTheory.DivDb
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FiniteSubrepresentation

variable {K : Type} [Field K] {N n : ℕ}

theorem pow_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (k : ℕ) : X ^ k * T = T * Y ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem aeval_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (q : Polynomial K) : Polynomial.aeval X q * T = T * Polynomial.aeval Y q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, pow_tw X Y T h]

end LateralTheory.DivDb.FiniteSubrepresentation

theorem LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of : LateralTheory.DivDb.FinSub := by
  intro Γ K _ _ N n ρ r A B hS hρ
  obtain ⟨hBA, hAr, hspan⟩ := hS
  have hinj : ∀ w : Fin n → K, A *ᵥ w = 0 → w = 0 := by
    intro w hw
    have := congrArg (B *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, hBA] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨W'', hc, hs⟩ := hρ (W.map (Matrix.mulVecLin A)) (by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨(r g : Matrix (Fin n) (Fin n) K) *ᵥ w, hW g w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAr g])
    refine ⟨W''.comap (Matrix.mulVecLin A), ?_, ?_⟩
    · constructor
      · rw [Submodule.disjoint_def]
        intro w hw hw'
        apply hinj
        have h1 : A *ᵥ w ∈ W.map (Matrix.mulVecLin A) := ⟨w, hw, rfl⟩
        exact (Submodule.disjoint_def.mp hc.disjoint) _ h1 hw'
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        have hv : A *ᵥ v ∈ W.map (Matrix.mulVecLin A) ⊔ W'' := by rw [hc.sup_eq_top]; trivial
        obtain ⟨y, ⟨w, hw, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
        rw [Submodule.mem_sup]
        refine ⟨w, hw, v - w, ?_, by abel⟩
        show A *ᵥ (v - w) ∈ W''
        rw [Matrix.mulVec_sub, ← hyz]
        simpa [Matrix.mulVecLin_apply] using hz
    · intro g v hv
      show A *ᵥ ((r g : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ W''
      rw [Matrix.mulVec_mulVec, ← hAr g, ← Matrix.mulVec_mulVec]
      exact hs g _ hv
  · apply le_antisymm
    · simpa using Matrix.rank_le_width A
    · have := Matrix.rank_mul_le_right B A
      rw [hBA, Matrix.rank_one] at this
      simpa using this
  · intro g
    rw [Matrix.mul_assoc, hAr g, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · intro g q
    constructor
    · intro h
      have h2 := aeval_tw _ _ A (hAr g) q
      rw [h, Matrix.zero_mul] at h2
      have h3 := congrArg (B * ·) h2
      simpa [← Matrix.mul_assoc, hBA] using h3.symm
    · intro h
      apply hspan
      intro T hT
      rw [aeval_tw _ _ T (hT g) q, h, Matrix.mul_zero]
end

section

open Matrix

namespace LateralTheory.DivDb.MatrixUnitConstruction
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

def Pr (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) (x y : Mat C N) : Prop :=
  x ∈ A ∧ y ∈ A ∧ p i * x * p j = x ∧ p j * y * p i = y ∧ x * y = p i ∧ y * x = p j

def rel (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) : Prop := ∃ x y, Pr A p i j x y

section
variable {A : Subalgebra C (Mat C N)} {p : Fin n → Mat C N}

lemma idem (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq

lemma idemL (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, idem hp i]

lemma sand_left (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : p i * x = x := by
  conv_lhs => rw [← h]
  simp only [mul_assoc, idemL hp i]
  simpa only [mul_assoc] using h

lemma sand_right (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : x * p j = x := by
  conv_lhs => rw [← h]
  rw [mul_assoc (p i * x), idem hp j, h]

lemma pr_ne (hp : Sys p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : x ≠ 0 := by
  rintro rfl
  exact hp.2 i (by rw [← h.2.2.2.2.1, zero_mul])

lemma pr_symm {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : Pr A p j i y x :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma pr_refl (hp : Sys p) (hc : Corner A p) (i : Fin n) : Pr A p i i (p i) (p i) :=
  ⟨hc.1 i, hc.1 i, by rw [idem hp i, idem hp i], by rw [idem hp i, idem hp i], idem hp i, idem hp i⟩

lemma pr_trans (hp : Sys p) {i j k : Fin n} {x y x' y' : Mat C N} (h : Pr A p i j x y)
    (h' : Pr A p j k x' y') : Pr A p i k (x * x') (y' * y) := by
  refine ⟨A.mul_mem h.1 h'.1, A.mul_mem h'.2.1 h.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, sand_left hp h.2.2.1, mul_assoc, sand_right hp h'.2.2.1]
  · rw [← mul_assoc, sand_left hp h'.2.2.2.1, mul_assoc, sand_right hp h.2.2.2.1]
  · rw [show x * x' * (y' * y) = x * (x' * y') * y by simp only [mul_assoc], h'.2.2.2.2.1,
      sand_right hp h.2.2.1, h.2.2.2.2.1]
  · rw [show y' * y * (x * x') = y' * (y * x) * x' by simp only [mul_assoc], h.2.2.2.2.2,
      sand_right hp h'.2.2.2.1, h'.2.2.2.2.2]

lemma partner (hp : Sys p) (hc : Corner A p) (hA : NoNil A) {i j : Fin n} {Y : Mat C N}
    (hYA : Y ∈ A) (hYl : p i * Y = Y) (hYr : Y * p j = Y) (hY0 : Y ≠ 0) :
    ∃ w, Pr A p i j Y w := by
  obtain ⟨b, hb, hnil⟩ : ∃ b ∈ A, ¬ IsNilpotent (b * Y) := by
    by_contra h
    push Not at h
    exact hY0 (hA Y hYA h)
  have hwA : p j * b * p i ∈ A := A.mul_mem (A.mul_mem (hc.1 j) hb) (hc.1 i)
  obtain ⟨c, hc1⟩ := hc.2 (Y * b) (A.mul_mem hYA hb) i
  obtain ⟨d, hd1⟩ := hc.2 (b * Y) (A.mul_mem hb hYA) j
  have hYw : Y * (p j * b * p i) = c • p i := by
    rw [← hc1]
    calc Y * (p j * b * p i) = (Y * p j) * b * p i := by simp only [mul_assoc]
      _ = (p i * Y) * b * p i := by rw [hYr, hYl]
      _ = p i * (Y * b) * p i := by simp only [mul_assoc]
  have hwY : (p j * b * p i) * Y = d • p j := by
    rw [← hd1]
    calc p j * b * p i * Y = p j * b * (p i * Y) := by simp only [mul_assoc]
      _ = p j * b * (Y * p j) := by rw [hYl, hYr]
      _ = p j * (b * Y) * p j := by simp only [mul_assoc]
  have e1 : Y * (p j * b * p i) * Y = c • Y := by rw [hYw, smul_mul_assoc, hYl]
  have e2 : Y * (p j * b * p i) * Y = d • Y := by rw [mul_assoc, hwY, mul_smul_comm, hYr]
  have hcd : c = d := by
    by_contra h
    have h3 : (c - d) • Y = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact hY0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnil
    refine ⟨2, ?_⟩
    have h0 : Y * b * Y = 0 := by
      have : Y * b * Y = Y * (p j * b * p i) * Y := by
        rw [show Y * (p j * b * p i) * Y = (Y * p j) * b * (p i * Y) by simp only [mul_assoc], hYr, hYl]
      rw [this, e1, zero_smul]
    rw [pow_two, show b * Y * (b * Y) = b * (Y * b * Y) by simp only [mul_assoc], h0, mul_zero]
  refine ⟨c⁻¹ • (p j * b * p i), hYA, A.smul_mem hwA _, ?_, ?_, ?_, ?_⟩
  · rw [hYl, hYr]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, idem hp i, idemL hp j]
  · rw [mul_smul_comm, hYw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [smul_mul_assoc, hwY, ← hcd, smul_smul, inv_mul_cancel₀ hc0, one_smul]

lemma oneDim (hp : Sys p) (hc : Corner A p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y)
    {a : Mat C N} (ha : a ∈ A) : ∃ c : C, p i * a * p j = c • x := by
  obtain ⟨c, hc1⟩ := hc.2 (a * p j * y) (A.mul_mem (A.mul_mem ha (hc.1 j)) h.2.1) i
  refine ⟨c, ?_⟩
  have hy : y * p i = y := sand_right hp h.2.2.2.1
  have h1 : p i * a * p j * y = c • p i := by
    calc p i * a * p j * y = p i * a * p j * (y * p i) := by rw [hy]
      _ = p i * (a * p j * y) * p i := by simp only [mul_assoc]
      _ = c • p i := hc1
  calc p i * a * p j = p i * a * p j * p j := by rw [mul_assoc (p i * a) (p j) (p j), idem hp j]
    _ = p i * a * p j * (y * x) := by rw [h.2.2.2.2.2]
    _ = (p i * a * p j * y) * x := by simp only [mul_assoc]
    _ = c • x := by rw [h1, smul_mul_assoc, sand_left hp h.2.2.1]

lemma rel_equiv (hp : Sys p) (hc : Corner A p) : Equivalence (rel A p) := by
  refine ⟨fun i => ⟨_, _, pr_refl hp hc i⟩, ?_, ?_⟩
  · rintro i j ⟨_, _, h⟩
    exact ⟨_, _, pr_symm h⟩
  · rintro i j k ⟨_, _, h⟩ ⟨_, _, h'⟩
    exact ⟨_, _, pr_trans hp h h'⟩

end

open Classical in
theorem MatUnits_of : MatrixUnits₂ := by
  intro C _ N n A p hp hc hA
  have heq := rel_equiv hp hc
  let s : Setoid (Fin n) := ⟨rel A p, heq⟩
  obtain ⟨r, hr, hreq⟩ : ∃ r : Fin n → Fin n, (∀ i, ∃ x y, Pr A p i (r i) x y) ∧
      ∀ i j, rel A p i j → r i = r j :=
    ⟨fun i => (Quotient.mk s i).out, fun i => heq.symm (Quotient.mk_out (s := s) i),
      fun i j h => congrArg Quotient.out (Quotient.sound (s := s) h)⟩
  choose X Y hXY using hr
  have pairE : ∀ i j, rel A p i j → Pr A p i j (X i * Y j) (X j * Y i) := by
    intro i j h
    have h2 := hXY j
    rw [← hreq i j h] at h2
    exact pr_trans hp (hXY i) (pr_symm h2)
  refine ⟨fun i j => if rel A p i j then X i * Y j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).1
    · simp only [if_neg h]; exact A.zero_mem
  · intro i
    simp only [if_pos (heq.refl i)]
    exact (hXY i).2.2.2.2.1
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).2.2.1
    · simp only [if_neg h, mul_zero, zero_mul]
  · intro i j hne
    have h : rel A p i j := by
      by_contra h
      simp only [if_neg h] at hne
      exact hne rfl
    simp only [if_pos (heq.symm h)]
    exact pr_ne hp (pairE j i (heq.symm h))
  · intro i j k h1 h2
    have hij : rel A p i j := by
      by_contra h
      simp only [if_neg h] at h1
      exact h1 rfl
    have hjk : rel A p j k := by
      by_contra h
      simp only [if_neg h] at h2
      exact h2 rfl
    have hik := heq.trans hij hjk
    simp only [if_pos hij, if_pos hjk, if_pos hik]
    refine ⟨?_, pr_ne hp (pairE i k hik)⟩
    rw [show X i * Y j * (X j * Y k) = X i * (Y j * X j) * Y k by simp only [mul_assoc],
      (hXY j).2.2.2.2.2, ← hreq i j hij, sand_right hp (hXY i).2.2.1]
  · intro a ha i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact oneDim hp hc (pairE i j h) ha
    · refine ⟨0, ?_⟩
      simp only [if_neg h, smul_zero]
      by_contra h'
      obtain ⟨w, hw⟩ := partner (i := i) (j := j) hp hc hA (A.mul_mem (A.mul_mem (hc.1 i) ha) (hc.1 j))
        (by simp only [mul_assoc, idemL hp i]) (by rw [mul_assoc _ (p j), idem hp j]) h'
      exact h ⟨_, _, hw⟩

end LateralTheory.DivDb.MatrixUnitConstruction
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.CycleCountPf
open LateralTheory.DivDb

def CycSpec : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Disj y π p →
  ∃ l : Fin n → C, Function.Injective l ∧ ∀ j, y.charpoly.IsRoot (l j) ∧
    ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0

def FixScal : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C), Sys p → (∀ j, y * p j = p (π j) * y) → Deg n y →
  Disj y π p → Function.Injective l →
  (∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0) →
  ∀ i, π i = i → ∃ c : C, y * p i = c • p i

theorem CycleCount_of (h1 : CycSpec) (h2 : FixScal) : CycleCount := by
  intro C _ _ _ N n p y π hp hy hyp hdeg hd
  obtain ⟨l, hl, hr⟩ := h1 C N n p y π hp hy hyp hd
  exact ⟨⟨l, hl, fun j => (hr j).1⟩, h2 C N n p y π l hp hyp hdeg hd hl (fun j => (hr j).2)⟩

end LateralTheory.DivDb.CycleCountPf
end

section

namespace LateralTheory.Fin.SpecLie
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
end
