module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChart
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003

@[expose] public section

section

namespace GlobalTheory.HatTaylorPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Polynomial

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def ev (f : ℕ → A) (P : A[X]) : A := P.sum fun j a => f j * a

omit [Algebra ℂ A] in
theorem ev_add (f : ℕ → A) (P Q : A[X]) : ev f (P + Q) = ev f P + ev f Q :=
  Polynomial.sum_add_index _ _ _ (by simp) (by simp [mul_add])

omit [Algebra ℂ A] in
theorem ev_monomial (f : ℕ → A) (n : ℕ) (a : A) : ev f (monomial n a) = f n * a :=
  Polynomial.sum_monomial_index _ _ (by simp)

omit [Algebra ℂ A] in
theorem ev_mul (f g : ℕ → A) (P Q : A[X]) (z : A) (h : ∀ j, z * g j = ev (fun i => f (j + i)) P) :
    z * ev g Q = ev f (P * Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [ev_add, mul_add, mul_add, ev_add, hp, hq]
  | monomial n b =>
    rw [ev_monomial, ← mul_assoc, h]
    clear h
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [ev_add, add_mul, add_mul, ev_add, hp, hq]
    | monomial k a => rw [monomial_mul_monomial, ev_monomial, ev_monomial, mul_assoc, add_comm]

omit [Algebra ℂ A] in
theorem ev_eq_sum (f : ℕ → A) (P : A[X]) (n : ℕ) (h : P.natDegree < n) :
    ev f P = ∑ j ∈ Finset.range n, f j * P.coeff j :=
  Polynomial.sum_over_range' _ (by simp) n h

omit [Algebra ℂ A] in
theorem mul_ev (z : A) (f : ℕ → A) (P : A[X]) : z * ev f P = ev (fun i => z * f i) P := by
  simp [ev, Polynomial.sum, Finset.mul_sum, mul_assoc]

def Deg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ P : A[X], P.natDegree ≤ D ∧ (∀ s : ℂ, Z (Y + s) = ev (fun j => algebraMap ℂ A (s ^ j)) P) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ev (fun j => m (q + j)) P

variable {L : LevelData A r} {Y : ℂ}

theorem Deg.mono {D E : ℕ} {Z : ℂ → A} (h : Deg L Y D Z) (hDE : D ≤ E) : Deg L Y E Z := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.trans hDE, h2⟩

theorem Deg.add {D : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y D W) :
    Deg L Y D (fun y => Z y + W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P + Q, (natDegree_add_le _ _).trans (max_le h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_add, ← h2, ← k2]
  · rw [ev_add, ← h3 m hm, ← k3 m hm, add_mul]

theorem Deg.mul {D E : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y E W) :
    Deg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P * Q, natDegree_mul_le.trans (add_le_add h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · show Z (Y + s) * W (Y + s) = _
    rw [k2]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [← Algebra.commutes, h2, mul_ev]
    simp only [pow_add, map_mul]
  · show Z Y * W Y * m q = _
    rw [mul_assoc, k3 m hm]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [h3 m hm]
    simp only [add_assoc]

theorem deg_const (a : A) (ha : ∀ m : ℕ → A, MulRel L m → ∀ q, a * m q = m q * a) :
    Deg L Y 0 (fun _ => a) := by
  refine ⟨monomial 0 a, natDegree_monomial_le _, fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_monomial]; simp
  · rw [ev_monomial, ha m hm]; rfl

theorem deg_fn {a : A} (ha : a ∈ L.fns) : Deg L Y 0 (fun _ => a) :=
  deg_const a fun _ hm q => ((hm q).1 a ha).eq

theorem deg_lin (Z : ℂ → A) (b : A) (h1 : ∀ s, Z (Y + s) = Z Y + algebraMap ℂ A s * b)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * b) : Deg L Y 1 Z := by
  refine ⟨monomial 0 (Z Y) + monomial 1 b, (natDegree_add_le _ _).trans
    (max_le ((natDegree_monomial_le _).trans zero_le_one) (natDegree_monomial_le _)), fun s => ?_,
    fun m hm q => ?_⟩
  · rw [ev_add, ev_monomial, ev_monomial, h1]; simp
  · rw [ev_add, ev_monomial, ev_monomial, h2 m hm]; rfl

theorem deg_list (l : List A) (hl : ∀ a ∈ l, a ∈ L.fns) : Deg L Y 0 (fun _ => l.prod) := by
  induction l with
  | nil => exact deg_const _ (by simp)
  | cons a l ih =>
    simpa using (deg_fn (hl a (by simp))).mul (ih fun b hb => hl b (by simp [hb]))

theorem deg_Tl (l : Fin r) (i j : Fin 2) : Deg L Y 1 (fun y => L.Tl y l i j) := by
  have hc : L.c l ∈ L.fns := by simp [LevelData.fns]
  have hci : L.ci l ∈ L.fns := by simp [LevelData.fns]
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl]
  · refine deg_lin _ 1 (fun s => ?_) fun m hm q => ?_
    · simp [add_right_comm]
    · simp [add_mul, mul_add, (hm q).2.1 l, Algebra.commutes, add_assoc]
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact ((hm q).1 _ hc).neg_left.eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    simpa using ((hm q).1 _ hci).eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact (Commute.zero_left (m q)).eq

theorem deg_prod (l : List (Fin r)) (i j : Fin 2) :
    Deg L Y l.length (fun y => (l.map (L.Tl y)).prod i j) := by
  induction l generalizing i j with
  | nil =>
    refine deg_const ((1 : Matrix (Fin 2) (Fin 2) A) i j) fun m _ q => ?_
    rw [Matrix.one_apply]; split_ifs <;> simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    rw [add_comm l.length 1]
    exact ((deg_Tl a i 0).mul (ih 0 j)).add ((deg_Tl a i 1).mul (ih 1 j))

theorem deg_Tprod (i j : Fin 2) : Deg L Y r (fun y => L.Tprod y i j) := by
  have h := deg_prod (L := L) (Y := Y) (List.finRange r).reverse i j
  simp only [List.length_reverse, List.length_finRange] at h
  simpa only [LevelData.Tprod, List.ofFn_eq_map, List.map_reverse] using h

theorem forwardTaylorDegree_one_leftLetter : Deg L Y 1 L.l0 := by
  refine deg_lin _ (-(L.ζb * L.GGi)) (fun s => ?_) fun m hm q => ?_
  · simp only [LevelData.l0, add_right_comm Y s, map_add (algebraMap ℂ A) (Y + 1 / 2) s]
    noncomm_ring
  · have c1 : ∀ q, Commute (L.ζb * L.GGi) (m q) := fun q =>
      ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))
    have c2 : Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) (m q) :=
      (Algebra.commute_algebraMap_left _ _).mul_left (c1 q)
    rw [LevelData.l0, sub_mul, neg_mul, (hm q).2.2.2.1, c2.eq, (c1 (q + 1)).eq]
    noncomm_ring

theorem deg_Ahat : Deg L Y r L.Ahat := by
  have h := (deg_list (L := L) (Y := Y) (List.ofFn L.c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_Tprod 0 0)
  rw [zero_add] at h
  exact h

theorem forwardTaylorDegree_plusHatR : Deg L Y (r + 1) L.R0 := by
  have h := ((deg_list (L := L) (Y := Y) (List.ofFn L.cb) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_fn (a := L.GG) (by simp [LevelData.fns]))).mul
    ((forwardTaylorDegree_one_leftLetter.mul (deg_Tprod 0 0)).add ((deg_Tprod 1 0).mono (Nat.le_add_left _ _)))
  rw [zero_add, zero_add, add_comm 1 r] at h
  exact h

theorem taylor_plus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨P, h1, h2, h3⟩ := deg_Ahat (L := L) (Y := Y)
  obtain ⟨Q, k1, k2, k3⟩ := forwardTaylorDegree_plusHatR (L := L) (Y := Y)
  have hP : P.natDegree < r + 2 := by omega
  have hQ : Q.natDegree < r + 2 := by omega
  refine ⟨P.coeff, Q.coeff, fun s => ?_, fun s => ?_, fun m hm q => ⟨?_, ?_⟩⟩
  · rw [h2, ev_eq_sum _ _ _ hP]; simp only [Algebra.smul_def]
  · rw [k2, ev_eq_sum _ _ _ hQ]; simp only [Algebra.smul_def]
  · rw [h3 m hm, ev_eq_sum _ _ _ hP]
  · rw [k3 m hm, ev_eq_sum _ _ _ hQ]

end

end GlobalTheory.HatTaylorPlus
end

section

namespace GlobalTheory.HatNF.TaylorMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def Dg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (x : ι → A), (∀ i, d i ≤ D) ∧
    (∀ s : ℂ, Z (Y - s) = ∑ i, s ^ d i • x i) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ i, m (q + d i) * x i

variable {L : LevelData A r} {Y : ℂ}

theorem Dg.mono {D E : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) (hDE : D ≤ E) : Dg L Y E Z := by
  obtain ⟨ι, hι, d, x, hd, h1, h2⟩ := h
  exact ⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩

theorem Dg.add {D : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y D W) :
    Dg L Y D (fun y => Z y + W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩
  · rintro (i | j)
    exacts [hd i, he j]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']
  · simp only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem Dg.mul {D E : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y E W) :
    Dg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2,
    fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩
  · dsimp only
    rw [hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, pow_add]
  · dsimp only
    rw [mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, show q + e j + d i = q + (d i + e j) by omega]

theorem dg_const (f : A) (hf : ∀ m : ℕ → A, MulRel L m → ∀ q, Commute f (m q)) :
    Dg L Y 0 (fun _ => f) := ⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp,
    fun m hm q => by simp [(hf m hm q).eq]⟩

theorem dg_lin (Z : ℂ → A) (u : A) (h1 : ∀ s, Z (Y - s) = Z Y + s • u)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * u) : Dg L Y 1 Z := ⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp,
    fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩

theorem Dg.out {D : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) :
    ∃ X : ℕ → A, (∀ s : ℂ, Z (Y - s) = ∑ j ∈ Finset.range (D + 1), s ^ j • X j) ∧
      ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ j ∈ Finset.range (D + 1), m (q + j) * X j := by
  obtain ⟨ι, _, d, x, hd, h1, h2⟩ := h
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1) :=
    fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩
  · rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  · rw [h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]

theorem comm_c {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.c l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cb {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cb l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cbi {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cbi l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_GG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute L.GG (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_zG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute (L.ζ * L.GGi) (m q) := ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))

theorem comm_prod {g : Fin r → A} {a : A} (h : ∀ l, Commute (g l) a) : Commute (List.ofFn g).prod a := Commute.list_prod_left _ _ fun x hx => by
    simp only [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact h l

theorem dg_Tvl (l : Fin r) (i j : Fin 2) : Dg L Y 1 (fun y => L.Tvl y l i j) := by
  fin_cases i <;> fin_cases j
  · show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)
    refine dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)
    · rw [map_sub, smul_neg, Algebra.smul_def, mul_one]
      abel
    · rw [sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]
      abel
  · show Dg L Y 1 (fun _ => -L.cb l)
    exact (dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one
  · show Dg L Y 1 (fun _ => L.cbi l)
    exact (dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one
  · show Dg L Y 1 (fun _ => (0 : A))
    exact (dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one

theorem dg_list (ls : List (Fin r)) (i j : Fin 2) :
    Dg L Y ls.length (fun y => (ls.map (L.Tvl y)).prod i j) := by
  induction ls generalizing i j with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    exact dg_const _ fun m hm q => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    exact (Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)

theorem dg_Tvprod (i j : Fin 2) : Dg L Y r (fun y => L.Tvprod y i j) := by
  have h := dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j
  rw [List.length_reverse, List.length_ofFn] at h
  have e : (fun y => L.Tvprod y i j) =
      fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j := by
    funext y
    simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
    rfl
  rw [e]
  exact h

theorem backwardTaylorDegree_one_mirrorLetter : Dg L Y 1 L.m0 := by
  show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))
  refine dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)
  · rw [show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]
    abel
  · have e1 := (hm q).2.2.2.2
    have c1 := (comm_zG hm q).eq
    have c2 := (comm_zG hm (q + 1)).eq
    have c3 := Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)
    have e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q =
        -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q) := by noncomm_ring
    rw [e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]
    noncomm_ring

theorem dg_Ahatv : Dg L Y (r + 1) L.Ahatv := by
  have hc : Dg L Y 0 (fun _ => L.Drb) := dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l
  exact (hc.mul (dg_Tvprod 0 0)).mono (by omega)

theorem backwardTaylorDegree_minusHatR : Dg L Y (r + 1) L.R0v := by
  have hc : Dg L Y 0 (fun _ => L.Dr * L.GG) :=
    dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)
  have hA : Dg L Y r (fun y => L.Avr y) := dg_Tvprod 0 0
  have hB : Dg L Y (1 + r) (fun y => L.Bvr y) := (dg_Tvprod 1 0).mono (by omega)
  exact (hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)

theorem taylor_minus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨Xa, ha1, ha2⟩ := (dg_Ahatv (L := L) (Y := Y)).out
  obtain ⟨Xr, hr1, hr2⟩ := (backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out
  exact ⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩

end GlobalTheory.HatNF.TaylorMinus
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem exists_mulEquiv_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩


open scoped CategoryTheory.Obj in
theorem exists_mulEquiv_ptTieF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hxF
  letI := H.starRing
  subst hxF
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) ≫ (I.G.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (I.G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨eA, hA⟩ := exists_mulEquiv_of_isGrpPullback gpG (TFK (R := T.V) F)
  obtain ⟨e2, h2⟩ := exists_mulEquiv_of_isGrpPullback I.m2.cart (TFK (R := T.V) F)
  obtain ⟨e1, h1⟩ := exists_mulEquiv_of_isGrpPullback I.m1.cart (TFK (R := T.V) F)
  refine ⟨(eA.trans e2.symm).trans e1, fun x b => ⟨?_, ?_⟩, fun a x => ?_⟩
  · rintro ⟨r, hr, hr1, hr2⟩
    let r' : TFK (R := T.V) F ⟶ I.t'.G := Over.homMk r hr
    have h3 : e2 r' = eA x := Over.OverMorphism.ext (by
      rw [h2, hA]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc]))
    show b = e1 (e2.symm (eA x))
    rw [← h3, e2.symm_apply_apply]
    exact Over.OverMorphism.ext (hr1.symm.trans (h1 r').symm)
  · rintro rfl
    refine ⟨(e2.symm (eA x)).left, Over.w _, (h1 _).symm, ?_⟩
    refine (h2 _).symm.trans ?_
    rw [e2.apply_symm_apply, hA, Over.comp_left, Category.assoc]
  · have h3 : e2.symm (eA (x ≫ P.oA.act a)) = e2.symm (eA x) ≫ I.t'.act.act a := by
      rw [MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hA, h2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, actA, I.m2.act a,
        ← Category.assoc _ I.m2.cm.F, ← h2, e2.apply_symm_apply, hA, Category.assoc, Category.assoc]
    show e1 (e2.symm (eA (x ≫ P.oA.act a))) = e1 (e2.symm (eA x)) ≫ Xo.univ.t.act.act a
    rw [h3]
    apply Over.OverMorphism.ext
    rw [h1, Over.comp_left, Over.comp_left, h1, Category.assoc, Category.assoc, I.m1.act a]

end GlobalTheory.PtTie
end
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.smallTorsion_killed_by_prime_powers : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  first | exact @GlobalTheory.MomOne.smallTors | exact GlobalTheory.MomOne.smallTors | (intros; apply GlobalTheory.MomOne.smallTors <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.exists_normalised_multiplicativeChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  first | exact @GlobalTheory.MomOne.Norm.exists_normalised_chart | exact GlobalTheory.MomOne.Norm.exists_normalised_chart | (intros; apply GlobalTheory.MomOne.Norm.exists_normalised_chart <;> assumption)
end
