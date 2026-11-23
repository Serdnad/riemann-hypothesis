module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

namespace GlobalTheory

open Finset GlobalTheory.KeyKa

private theorem kaForm_prod_zpow {G : Type} [CommGroup G] (a : G) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, zpow_add]

theorem tComb_rescale {R : Type} [CommRing R] (g n l Pr : ℕ) (t a : Rˣ) (lam be : ℕ → Rˣ)
    (hl : g * n < l) (hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ Pr) :
    tComb g n l Pr (t * ∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)))
      (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) *
        a ^ (8 * (l - j * n) ^ (4 * g + 2)))
      = tComb g n l Pr t lam *
        a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
  unfold tComb
  rw [mul_pow]
  simp only [mul_zpow, prod_mul_distrib]
  have hB : (∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
      ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) = 1 := by
    rw [← prod_pow, ← prod_mul_distrib]
    refine prod_eq_one fun j hj => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero (be j) using 2
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  have hA : ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) =
      a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
    rw [prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul], kaForm_prod_zpow,
      ← alternating_sum_choose_mul_sub_pow g n l hl.le, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  calc _ = t ^ (4 * Pr ^ (3 * g + 2)) *
        (∏ j ∈ range (g + 1), lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ((∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
          ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
            ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
          ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) := by ac_rfl
    _ = _ := by rw [hB, hA, mul_one]

theorem tComb_mul_left {R : Type} [CommRing R] (g n l Pr : ℕ) (t c : Rˣ) (lam : ℕ → Rˣ) :
    tComb g n l Pr (t * c) lam = tComb g n l Pr t lam * c ^ (4 * Pr ^ (3 * g + 2)) := by
  unfold tComb
  rw [mul_pow]
  exact mul_right_comm _ _ _

private theorem kaForm_monomial_eq_of_exponent_relations {G : Type} [CommGroup G] (X X' J u dl a : G) (N k : ℕ)
    (z1 z2 z3 α e1 e2 e3 : ℤ) (hu : z1 * N * e1 + z2 * N * e2 + z3 * e3 = 0)
    (hdl : 2 * N * e1 + 2 * N * e2 + 2 * e3 = 0) (ha : α * e1 + α * e2 + k = 0) :
    (X * (u ^ z1) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e1 * (X' * (u ^ z2) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e2 *
      (J * u ^ z3 * dl ^ 2) ^ e3 * a ^ k = X ^ e1 * X' ^ e2 * J ^ e3 := by
  have eU : u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hu, zpow_zero]
  have eD : dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hdl, zpow_zero]
  have eA : a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ) = 1 := by
    rw [← zpow_add, ← zpow_add, ha, zpow_zero]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  calc _ = X ^ e1 * X' ^ e2 * J ^ e3 * (u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3)) *
        (dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3)) *
        (a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ)) := by simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = _ := by rw [eU, eD, eA, mul_one, mul_one, mul_one]

theorem kaForm_homogeneous :
    ∀ (R : Type) [CommRing R] (g n l l' : ℕ) (t t' J u a dl : Rˣ) (lam lam' be be' : ℕ → Rˣ), g * n < l → l < l' → kaForm g n l l' (t * u ^ (-2 * (l : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (t' * u ^ (-2 * (l' : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be' j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l - j * n) ^ (4 * g + 2))) (fun j => lam' j * be' j ^ (-8 * ((l' - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l' - j * n) ^ (4 * g + 2))) (J * u ^ (-((g * n : ℕ) : ℤ)) * dl ^ 2) * a ^ (8 * kaExp g n l l') = kaForm g n l l' t t' lam lam' J := by
  intro R _ g n l l' t t' J u a dl lam lam' be be' hl hl'
  have hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_right _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  have hd' : ∀ j ∈ range (g + 1), (l' - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_left _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  unfold kaForm
  rw [tComb_rescale g n l _ _ a lam be hl hd, tComb_rescale g n l' _ _ a lam' be' (hl.trans hl') hd',
    tComb_mul_left, tComb_mul_left, tComb_mul_left, tComb_mul_left]
  refine kaForm_monomial_eq_of_exponent_relations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  all_goals
    try unfold kaExp
    push_cast [Nat.cast_sub hl'.le]
    ring

end GlobalTheory
end

section

open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KosKer
open Matrix

theorem mulVec_congr_deg {R Ix : Type} [CommRing R] [Fintype Ix] {deg : Ix → ℕ} {D : Matrix Ix Ix R}
    (h : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (u u' : Ix → R) (p : Ix)
    (hu : ∀ q, deg q = deg p + 1 → u q = u' q) : (D *ᵥ u) p = (D *ᵥ u') p := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : deg q = deg p + 1
  · rw [hu q hq]
  · rw [h p q hq, zero_mul, zero_mul]

theorem clear_denom {O Ix : Type} [CommRing O] [IsDomain O] [Fintype Ix] (D : Matrix Ix Ix O)
    (h : ∀ v, (D.map (algebraMap O (FractionRing O))) *ᵥ v = 0 →
      ∃ w, (D.map (algebraMap O (FractionRing O))) *ᵥ w = v) (x : Ix → O) (hx : D *ᵥ x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ u, D *ᵥ u = c • x := by
  have hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) =
      algebraMap O (FractionRing O) ∘ (D *ᵥ y) := fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm
  obtain ⟨w, hw⟩ := h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩
  apply IsFractionRing.injective O (FractionRing O)
  have e : algebraMap O (FractionRing O) ∘ u = (b : O) • w := funext hu
  have e2 := congrFun (hm u) p
  rw [e, mulVec_smul, hw] at e2
  simp only [Function.comp, Pi.smul_apply] at e2 ⊢
  rw [← e2, smul_eq_mul, map_mul, Algebra.smul_def]

variable {g d : ℕ} {N : ℕ → ℕ}

theorem mulVec_empty {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin (N 0)) :
    (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩) = (∑ i, m i 0 1 *ᵥ (fun k => u (.inl ⟨{i}, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single {i}]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ⟨by simp, by simp⟩]
    simp
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hJ (by simpa using h.2)), zero_mul]
  · simp

theorem mulVec_inr {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ∅]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg hJ, zero_mul]
  · simp

theorem mulVec_inl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d' : ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (ev' : ∀ j, Matrix (Fin d') (Fin (N j)) S)
    (u : KIx g d N → R) (u' : KIx g d' N → S) (hu : ∀ q, u' (.inl q) = f (u (.inl q))) (p) :
    (kosD (fun i j j' => (m i j j').map f) ev' *ᵥ u') (.inl p) = f ((kosD m ev *ᵥ u) (.inl p)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]

theorem div_unif {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O)
    (hD : IsCx kdeg (kosD m ev))
    (hk : ∀ v : KIx g 0 N → IsLocalRing.ResidueField O,
      (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p))
    {π : O} (hπ : Irreducible π) (v : Fin (N 0) → O) (u : KIx g d N → O)
    (hu : ∀ a, π * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) :
    ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
  classical
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  let u' : KIx g d N → O := fun q => if kdeg q = 2 then u q else 0
  have h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a := fun a => by
    rw [hu a]
    exact mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq
  obtain ⟨wb, hwb⟩ := hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by
    ext p
    rcases p with ⟨I, a⟩ | a
    · rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]
      by_cases hI : I = ∅
      · subst hI
        rw [h1 a]
        exact (hres _).2 (dvd_mul_right _ _)
      · rw [mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]
        · simp
        · have : I.card ≠ 0 := by simpa using hI
          rw [hq]
          simp only [kdeg]
          omega
    · exact a.elim0)
  choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))
  let w : KIx g d N → O := Sum.elim w0 0
  have h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y := by
    rintro (p | a)
    · by_cases hp : p.1 = ∅
      · refine ⟨0, fun h => ?_⟩
        simp [kdeg, hp] at h
      · have e := hwb p hp
        rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)] at e
        obtain ⟨y, hy⟩ := (hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by
          rw [Pi.sub_apply, map_sub, ← e]; exact sub_self _)
        exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => by simp [kdeg] at h⟩
  choose y hy using h2
  refine ⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩
  have e := mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq
  rw [mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a] at e
  exact e

theorem ker_and_image : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by
  intro O _ _ _ g d N m ev hD hK hk
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) →
      ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      rintro v ⟨u, hu⟩
      exact ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)
  refine ⟨fun v hv => ?_, ?_⟩
  · let x : KIx g d N → O := Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0
    have hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a := fun a => by
      simp only [x, Sum.elim_inl, dif_pos]
      rfl
    have hx : kosD m ev *ᵥ x = 0 := by
      ext p
      rcases p with p | a
      · rw [mulVec_congr_deg hD.1 x 0 _ ?_]
        · simp
        · rintro (q | q) hq
          · refine dif_neg fun h => ?_
            simp [kdeg, h] at hq
          · rfl
      · rw [mulVec_inr, funext hx0, hv]
        rfl
    obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK x hx
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    obtain ⟨y, hy⟩ := hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by
      rw [mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩
    exact ⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩
  · have h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O) := by
      intro a
      obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by
        ext p
        rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])
      refine ⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩
      rw [← mulVec_inr m ev u b, hu]
      rfl
    choose c hc v hv using h1
    refine ⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩
    choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)
    refine ⟨∑ a, (t a * e a) • v a, ?_⟩
    rw [mulVec_sum]
    ext b
    simp only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [he b]
    ring

end GlobalTheory.KeyKa.KosKer
end
end

section

open GlobalTheory.KeyKa

namespace GlobalTheory.TorsExists

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]

theorem exists_mul_mul_eq {K : Type} [Field K] (D : Matrix Ix Ix K) : ∃ G : Matrix Ix Ix K, D * G * D = D := by
  set f := Matrix.toLin' D with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := LinearMap.exists_extend s
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ← hf]
  refine LinearMap.ext fun v => ?_
  have h1 : g (f v) = s (f.rangeRestrict v) := by rw [← hg]; rfl
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict v))
  simp only [LinearMap.comp_apply, h1]
  exact h2

theorem exists_isUnit_field {K : Type} [Field K] (D : Matrix Ix Ix K) (hD : D * D = 0)
    (hex : ∀ v : Ix → K, D.mulVec v = 0 → ∃ w, D.mulVec w = v) :
    ∃ G : Matrix Ix Ix K, IsUnit (D * G + G * D).det := by
  obtain ⟨G, hG⟩ := exists_mul_mul_eq D
  refine ⟨G, ?_⟩
  set N := 1 - (D * G + G * D) with hN
  have h1 : D * N = 0 := by
    rw [hN, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hD, hG]; simp
  have h2 : N * D = 0 := by
    rw [hN, sub_mul, add_mul, mul_assoc G, hD, hG]; simp
  have h3 : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, hw⟩ := hex (N.mulVec v) (by rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec])
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, h2,
      Matrix.zero_mulVec, Matrix.zero_mulVec]
  have h4 : (D * G + G * D) * (1 + N) = 1 := by
    have : D * G + G * D = 1 - N := by rw [hN]; abel
    rw [this, sub_mul, mul_add, mul_add, h3]; simp
  exact Matrix.isUnit_det_of_right_inverse h4

theorem exists_contraction {R : Type} [CommRing R] [IsLocalRing R] (D : Matrix Ix Ix R) (hD : D * D = 0)
    (hex : ∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 →
      ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) :
    ∃ h : Matrix Ix Ix R, D * h + h * D = 1 := by
  obtain ⟨G, hG⟩ := exists_isUnit_field (D.map (IsLocalRing.residue R))
    (by rw [← Matrix.map_mul, hD]; simp) hex
  choose H hH using fun p q => IsLocalRing.residue_surjective (R := R) (G p q)
  have hHG : (Matrix.of H).map (IsLocalRing.residue R) = G := by ext p q; exact hH p q
  set A := D * Matrix.of H + Matrix.of H * D with hA
  have hu : IsUnit A.det := by
    have : IsLocalRing.residue R A.det = (D.map (IsLocalRing.residue R) * G + G * D.map (IsLocalRing.residue R)).det := by
      rw [RingHom.map_det, ← hHG, hA]
      simp [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_add (f := _)]
    rw [← this] at hG
    exact (isUnit_map_iff _ _).1 hG
  have hc : A * D = D * A := by
    rw [hA, add_mul, mul_add, mul_assoc (Matrix.of H), hD, ← mul_assoc D D, hD]; simp [mul_assoc]
  have hc' : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, mul_one]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hc]; simp only [mul_assoc]
      _ = D * A⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
  refine ⟨Matrix.of H * A⁻¹, ?_⟩
  rw [mul_assoc, hc', ← mul_assoc, ← mul_assoc, ← add_mul, ← hA, Matrix.mul_nonsing_inv _ hu]

theorem exists_homogeneous {R : Type} [CommRing R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (hh : D * h + h * D = 1) :
    ∃ h' : Matrix Ix Ix R, (∀ p q, deg p ≠ deg q + 1 → h' p q = 0) ∧ D * h' + h' * D = 1 := by
  refine ⟨Matrix.of fun p q => if deg p = deg q + 1 then h p q else 0, fun p q hpq => by simp [hpq], ?_⟩
  ext a b
  by_cases hab : deg a = deg b
  · rw [← hh]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_
    · split_ifs with hp
      · rfl
      · rw [hD a p (by omega)]; simp
    · split_ifs with hp
      · rfl
      · rw [hD p b (by omega)]; simp
  · rw [Matrix.one_apply_ne (fun e => hab (by rw [e]))]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro p _
      split_ifs with hp
      · rw [hD p b (by omega)]; simp
      · simp
    · intro p _
      split_ifs with hp
      · rw [hD a p (by omega)]; simp
      · simp

theorem block_mul_block {R : Type} [CommRing R] (P Q : Ix → Prop) [DecidablePred P] [DecidablePred Q]
    (M : Matrix Ix Ix R) (hM : M * M = 1) (h0 : ∀ p r, P p → ¬ Q r → M p r = 0) :
    M.submatrix (fun p : {p // P p} => p.1) (fun r : {r // Q r} => r.1) *
      M.submatrix (fun r : {r // Q r} => r.1) (fun p : {p // P p} => p.1) = 1 := by
  ext a b
  have h1 : (M * M) a.1 b.1 = (1 : Matrix {p // P p} {p // P p} R) a b := by
    rw [hM]; simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q (fun r => M a.1 r * M r b.1)]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r})), add_zero]
  intro r _
  rw [h0 _ _ a.2 r.2, zero_mul]

theorem nonempty_equiv {R : Type} [CommRing R] [Nontrivial R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : IsCx deg D) (hdeg : ∀ p q, deg p ≠ deg q + 1 → h p q = 0) (hh : D * h + h * D = 1) :
    Nonempty ({p // Even (deg p)} ≃ {p // ¬ Even (deg p)}) := by
  obtain ⟨hD1, hD2⟩ := hD
  have e1 : D * h = 1 - h * D := eq_sub_of_add_eq hh
  have e2 : D * h * D = D := by rw [e1, sub_mul, mul_assoc, hD2]; simp
  have e3 : D * h * (h * D) = 0 := by
    have : D * h = 1 - h * D := e1
    have e4 : h * D * (h * D) = h * D := by
      rw [mul_assoc, ← mul_assoc D, e2]
    rw [e1, sub_mul, e4]; simp
  set M := D + h * D * h with hM
  have hMM : M * M = 1 := by
    have : M * M = D * D + (D * h * D) * h + h * (D * h * D) + h * (D * h * (h * D)) * h := by
      rw [hM]; noncomm_ring
    rw [this, hD2, e2, e3, ← hh]; simp
  have hpar : ∀ p q, (Even (deg p) ↔ Even (deg q)) → M p q = 0 := by
    intro p q hpq
    have n1 : deg q ≠ deg p + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    have n2 : deg p ≠ deg q + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    rw [hM, Matrix.add_apply, hD1 p q n1, zero_add, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases c1 : deg p = deg s + 1
    · by_cases c2 : deg r = deg s + 1
      · rw [hdeg r q (by omega)]; simp
      · rw [hD1 s r c2]; simp
    · rw [hdeg p s c1]; simp
  exact ⟨Matrix.indexEquivOfInv
    (block_mul_block (fun p => Even (deg p)) (fun p => ¬ Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))
    (block_mul_block (fun p => ¬ Even (deg p)) (fun p => Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))⟩

theorem exists_torsSq : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) [IsLocalRing R], IsCx deg D → (∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 → ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) → ∃ t, TorsSq deg D t := by
  intro R Ix _ _ _ deg D _ hD hex
  obtain ⟨h0, hh0⟩ := exists_contraction D hD.2 hex
  obtain ⟨h, hdeg, hh⟩ := exists_homogeneous deg D h0 hD.1 hh0
  obtain ⟨e⟩ := nonempty_equiv deg D h hD hdeg hh
  exact ⟨_, h, hdeg, hh, e, rfl⟩

end GlobalTheory.TorsExists
end
