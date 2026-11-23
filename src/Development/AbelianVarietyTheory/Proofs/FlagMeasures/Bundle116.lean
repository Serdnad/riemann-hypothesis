module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
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
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht

end GlobalTheory.DegCnt
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerFormula

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {N : ℕ} {M : Mt g N} (hM : IsUniUp M) : IsUnit M := by
  have htri : M.BlockTriangular id := fun i j hij => (hM i j).1 hij
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri]
  simp [(hM _ _).2 rfl]

theorem card_lt_pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hb : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

def ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : Mt g N :=
  fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem isUniUp_ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : IsUniUp (ofUpper f) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · simp only [ofUpper, dif_neg (not_lt.mpr hba.le), if_neg hba.ne']
  · subst hab
    simp [ofUpper]

theorem card_uniUp (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  rw [← Fintype.card_subtype]
  have e : {u : Gn g N // IsUniUp (u : Mt g N)} ≃ ({p : Fin N × Fin N // p.1 < p.2} → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(isUnit_of_isUniUp (isUniUp_ofUpper f)).unit, isUniUp_ofUpper f⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        apply Units.ext
        dsimp only
        rw [IsUnit.unit_spec]
        funext a b
        show ofUpper _ a b = (u : Mt g N) a b
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp only [ofUpper, dif_pos hab]
        · simp only [ofUpper, dif_neg (lt_irrefl a)]
          exact ((hu a a).2 rfl).symm
        · simp only [ofUpper, dif_neg (not_lt.mpr hab.le), if_neg hab.ne']
          exact ((hu a b).1 hab).symm
      right_inv := by
        intro f
        funext p
        dsimp only
        rw [IsUnit.unit_spec]
        show ofUpper f p.1.1 p.1.2 = f p
        simp only [ofUpper, dif_pos p.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, card_lt_pairs]

theorem eU_coeff (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (u : Gn g N) :
    (eU g N ψ).coeff u = if IsUniUp (u : Mt g N) then
      ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ * (ψ (∑ i ∈ Finset.range (N - 1), entN (u : Mt g N) i (i + 1)))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, card_uniUp, Nat.cast_pow, smul_eq_mul]
  split_ifs <;> simp

theorem sum_br (i n : ℕ) (M : Mt g n) :
    ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) = supFrom i M := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  have hbr : entN (br i (n - i) M) j (j + 1) = entN M (i + j) (i + (j + 1)) := by
    conv_lhs => unfold entN
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  rw [hbr, add_assoc]

end GlobalTheory.GLm.DerFormula

namespace GlobalTheory.GLm

open DerFormula

theorem der_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  intro g _ ψ i n F h _
  have key : ∀ x : Gn g n, (∑ v : Gn g (n - i),
      (if IsUniUp (v : Mt g (n - i)) then
        (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
      (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
          br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0)) =
      if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
        F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
    intro x
    unfold InR
    by_cases hx : (InPar i (x : Mt g n) ∧ IsUniUp (br i (n - i) (x : Mt g n))) ∧
        tl i (x : Mt g n) = (h : Mt g i)
    · obtain ⟨⟨hP, hU⟩, ht⟩ := hx
      have hv0 : ((isUnit_of_isUniUp hU).unit : Mt g (n - i)) = br i (n - i) (x : Mt g n) :=
        IsUnit.unit_spec _
      rw [Finset.sum_eq_single (isUnit_of_isUniUp hU).unit]
      · rw [if_pos (by rw [hv0]; exact hU), if_pos ⟨hP, ht, hv0.symm⟩, if_pos ⟨⟨hP, hU⟩, ht⟩, hv0, sum_br,
          mul_comm]
      · intro v _ hv
        refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨-, -, hb⟩
        exact hv (Units.ext (hb.symm.trans hv0.symm))
      · intro hv
        exact absurd (Finset.mem_univ _) hv
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : IsUniUp (v : Mt g (n - i))
      · refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨hP, ht, hb⟩
        exact hx ⟨⟨hP, by rw [hb]; exact hv⟩, ht⟩
      · rw [if_neg hv, zero_mul]
  simp only [der, wh, tr, res, eU_coeff]
  calc _ = ∑ v : Gn g (n - i), ((g : ℂ) ^ (i * (n - i)))⁻¹ * ((g : ℂ) ^ ((n - i) * (n - i - 1) / 2))⁻¹ *
        ∑ x : Gn g n, (if IsUniUp (v : Mt g (n - i)) then
          (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
          (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
            br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [key]
        rw [pow_add, mul_inv]

end GlobalTheory.GLm
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.Pattern

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.Pattern.inPat_mul {Φ : Fin N → Fin N → Prop}
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) {M M' : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) (h' : _root_.GlobalTheory.GLm.InPat Φ M') :
    _root_.GlobalTheory.GLm.InPat Φ (M * M') := by
  intro a b hab
  have hone : (1 : _root_.GlobalTheory.GLq.Mt g N) a b =
      ((1 : _root_.GlobalTheory.GLq.Mt g N) * 1) a b := by rw [one_mul]
  rw [hone, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hac : Φ a c
  · have hcb : ¬ Φ c b := fun hcb => hab (ht a c b hac hcb)
    rw [h' c b hcb]
    by_cases e : c = b
    · subst e; exact absurd hac hab
    · rw [Matrix.one_apply_ne e, mul_zero, mul_zero]
  · rw [h a c hac]
    by_cases e : a = c
    · subst e; rw [h' a b hab]
    · rw [Matrix.one_apply_ne e, zero_mul, zero_mul]

def patSub (g : ℕ) [Fact g.Prime] {N : ℕ} (Φ : Fin N → Fin N → Prop)
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) : Subgroup (Gn g N) where
  carrier := {x | InPat Φ (x : Mt g N)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => inPat_mul ht ha hb
  inv_mem' := by
    intro x hx
    have hp : ∀ k : ℕ, InPat Φ ((x ^ k : Gn g N) : Mt g N) := by
      intro k
      induction k with
      | zero => exact fun _ _ _ => rfl
      | succ k ih => rw [pow_succ]; exact inPat_mul ht ih hx
    have ho : 0 < orderOf x := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    show InPat Φ ((x⁻¹ : Gn g N) : Mt g N)
    rw [this]; exact hp _

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private theorem isUnit_of_inPat_irrefl_trans {Φ : Fin N → Fin N → Prop} (hirr : ∀ a, ¬ Φ a a)
    (htrans : ∀ a b c, Φ a b → Φ b c → Φ a c) {M : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) : IsUnit M := by
  let r : Fin N → ℕ := fun i => (Finset.univ.filter fun j => Φ j i).card
  have hr : ∀ i j, Φ i j → r i < r j := by
    intro i j hij
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp [hirr i]⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact htrans k i j hk hij
  have hbt : Matrix.BlockTriangular M r := by
    intro i j hji
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hji
    rw [h i j (fun hij => absurd (hr i j hij) (not_lt.mpr hji.le)), Matrix.one_apply_ne hne]
  have hblock : ∀ k, Matrix.toSquareBlock M r k = 1 := by
    intro k
    refine Matrix.ext fun i j => ?_
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    have hij : ¬ Φ i.1 j.1 := fun hij => (hr _ _ hij).ne (i.2.trans j.2.symm)
    rw [h _ _ hij]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun h => e (Subtype.ext h))]
  rw [Matrix.isUnit_iff_isUnit_det, hbt.det]
  simp [hblock]


open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.Pattern.pattern_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ)
    (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) →
    (∃ H : Subgroup (_root_.GlobalTheory.GLq.Gn g N),
      (∀ x, x ∈ H ↔ _root_.GlobalTheory.GLm.InPat Φ (x : _root_.GlobalTheory.GLq.Mt g N)) ∧
      Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧
    (∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M) ∧
    ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) →
      ∀ M M' : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M →
        _root_.GlobalTheory.GLm.InPat Φ M' →
        _root_.GlobalTheory.GLm.sumAt E (M * M') =
          _root_.GlobalTheory.GLm.sumAt E M + _root_.GlobalTheory.GLm.sumAt E M' := by
  intro g _ N Φ hirr htrans
  have hunit : ∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M :=
    fun M hM => isUnit_of_inPat_irrefl_trans hirr htrans hM
  refine ⟨⟨_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans, fun x => Iff.rfl, ?_⟩, hunit, ?_⟩
  · have e1 : Nat.card (_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans) =
        Nat.card {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x => ⟨(x.1 : _root_.GlobalTheory.GLq.Mt g N), x.2⟩) ⟨?_, ?_⟩)
      · intro x y hxy
        exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
      · intro M
        exact ⟨⟨(hunit M.1 M.2).unit, M.2⟩, rfl⟩
    let e2 : {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} ≃
        ({p : Fin N × Fin N // Φ p.1 p.2} → ZMod g) :=
      { toFun := fun M p => M.1 p.1.1 p.1.2
        invFun := fun f => ⟨fun a b => if h : Φ a b then f ⟨(a, b), h⟩
            else (1 : _root_.GlobalTheory.GLq.Mt g N) a b, fun a b h => by simp [h]⟩
        left_inv := fun M => by
          apply Subtype.ext
          refine Matrix.ext fun a b => ?_
          dsimp only
          split_ifs with h
          · rfl
          · exact (M.2 a b h).symm
        right_inv := fun f => by
          funext p
          simp [p.2] }
    rw [e1, Nat.card_congr e2, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  · intro E hE hEirr M M' hM hM'
    unfold _root_.GlobalTheory.GLm.sumAt
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · rw [Matrix.mul_apply]
      have hne : a ≠ c := by rintro rfl; exact hEirr a hac
      rw [Fintype.sum_eq_add a c hne]
      · rw [hM a a (hirr a), hM' c c (hirr c), Matrix.one_apply_eq, Matrix.one_apply_eq,
          one_mul, mul_one, add_comm]
      · rintro b ⟨hba, hbc⟩
        by_cases hab : Φ a b
        · rw [hM' b c (fun hbc' => hE a b c hab hbc' hac), Matrix.one_apply_ne hbc, mul_zero]
        · rw [hM a b hab, Matrix.one_apply_ne (Ne.symm hba), zero_mul]
    · simp

end GlobalTheory.GLm.Pattern
end

section

noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private lemma traceOnCharacter_averagedSingles_eq (g N : ℕ) [Fact g.Prime]
    (Φ : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (E : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (χ : GL (Fin N) (ZMod g) → ℂ) :
    _root_.GlobalTheory.GLq.tr (_root_.Formalism.MainNotions.ArithmeticCylinders.eDat g N Φ E ψ) χ =
      ((Finset.univ.filter
          (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g)))).card : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter
            (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g))),
          (ψ (E u))⁻¹ * χ u := by
  unfold _root_.GlobalTheory.GLq.tr _root_.Formalism.MainNotions.ArithmeticCylinders.eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring


open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.tr_ePat_renumber : ∀ (g : ℕ) [Fact g.Prime]
    (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (Φ E : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (χ : _root_.GlobalTheory.GLq.Gn g N → ℂ), _root_.GlobalTheory.GLq.IsClass χ →
    _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N (fun a b => Φ (σ a) (σ b))
      (fun a b => E (σ a) (σ b)) ψ) χ =
      _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N Φ E ψ) χ := by
  intro g _ ψ N Φ E σ χ hχ
  unfold _root_.GlobalTheory.GLm.ePat
  rw [traceOnCharacter_averagedSingles_eq, traceOnCharacter_averagedSingles_eq]
  set Q : GL (Fin N) (ZMod g) := (Matrix.permMatrixHom (R := ZMod g)).toHomUnits σ⁻¹ with hQdef
  have hQ : ∀ (u : GL (Fin N) (ZMod g)) (x y : Fin N),
      ((Q⁻¹ * u * Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) x y =
        (u : Matrix (Fin N) (Fin N) (ZMod g)) (σ.symm x) (σ.symm y) := by
    intro u x y
    have hinv : ((Q⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        (σ⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix := by
      rw [hQdef]
      show (((σ⁻¹)⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    have hval : ((Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        σ.toPEquiv.toMatrix := by
      rw [hQdef]
      show ((σ⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    rw [Units.val_mul, Units.val_mul, hinv, hval, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  let e : GL (Fin N) (ZMod g) ≃ GL (Fin N) (ZMod g) := (MulAut.conj Q⁻¹).toEquiv
  have he : ∀ u, e u = Q⁻¹ * u * Q := by
    intro u
    simp [e, MulAut.conj_apply]
  have hmem : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.InPat (fun a b => Φ (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) ↔
        _root_.GlobalTheory.GLm.InPat Φ (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.InPat
    simp only [he, hQ]
    constructor
    · intro h x y hxy
      have hxy' := h (σ.symm x) (σ.symm y) (by simpa using hxy)
      rw [hxy', Matrix.one_apply, Matrix.one_apply]
      simp
    · intro h a b hab
      have hab' := h (σ a) (σ b) hab
      simp only [Equiv.symm_apply_apply] at hab'
      rw [hab', Matrix.one_apply, Matrix.one_apply]
      simp
  have hsum : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.sumAt (fun a b => E (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) =
        _root_.GlobalTheory.GLm.sumAt E (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.sumAt
    simp only [he, hQ]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
  congr 1
  · congr 2
    exact Finset.card_equiv e (fun u => by simp [hmem])
  · refine Finset.sum_equiv e (fun u => by simp [hmem]) (fun u _ => ?_)
    rw [hsum, he]
    congr 1
    have hconj := hχ u Q⁻¹
    simpa using hconj.symm

end GlobalTheory.GLm
end
end
