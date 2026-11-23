module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountUp
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PartnersFactorsOfKernelSmith
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SmithPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

def WdimUpAt : Prop :=
  ∀ (r : ℕ) [NeZero r] (lam : Fin r → ℤ), Antitone lam → wdim lam ≤ ∏ l, (sdXi r (lam l).natAbs : ℚ)

theorem le_finsum_of_nonneg {α : Type*} (f : α → ℚ) (c : ℚ) (hc : 0 < c) (hs : ∑ᶠ x, f x = c) (hnn : ∀ x, 0 ≤ f x) (a : α) :
    f a ≤ c := by
  have hfin : (support f).Finite := by
    by_contra hinf
    rw [finsum_of_infinite_support hinf] at hs
    linarith
  rw [← hs]
  exact single_le_finsum a hfin hnn

theorem wu_single (hCD : ChainDimAt) {N r : ℕ} [NeZero r] (LL : ChainLetters (N + 1))
    (ka : Fin (N + 1 + 1) → Fin r → ℤ) (h : IsChain LL ka) :
    wdim (ka (Fin.last (N + 1))) ≤ ∏ i, (sdXi r (LL.deg i) : ℚ) := by
  have h1 := hCD (N + 1) r LL
  unfold chainSum at h1
  have hpos : (0 : ℚ) < ∏ i, (sdXi r (LL.deg i) : ℚ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast sdXi_pos _ _ (Nat.pos_of_ne_zero (NeZero.ne r))
  refine (le_of_eq ?_).trans (le_finsum_of_nonneg _ _ hpos h1 ?_ ka)
  · rw [if_pos ⟨h, fun k => k.elim0⟩]
  · intro x
    split_ifs with hx
    · exact (wdim_pos (IsChain.anti_last hx.1)).le
    · exact le_rfl

def wuLam {r : ℕ} (lam : Fin r → ℤ) (y : ℕ) : ℤ := if h : y < r then lam ⟨y, h⟩ else 0

theorem wuLam_val {r : ℕ} (lam : Fin r → ℤ) (l : Fin r) : wuLam lam l.val = lam l := by
  unfold wuLam
  rw [dite_eq_left l.2]

def wuDeg {r : ℕ} (lam : Fin r → ℤ) (a : ℕ) : ℕ :=
  if a < r then (wuLam lam a).toNat else if a < 2 * r then (-(wuLam lam (2 * r - 1 - a))).toNat else 0

def wuLL {r : ℕ} (lam : Fin r → ℤ) : ChainLetters (2 * r + 1) where
  vec := fun a => decide (a.val < r ∨ a.val = 2 * r)
  deg := fun a => wuDeg lam a.val

def wuSt {r : ℕ} (lam : Fin r → ℤ) (n : ℕ) (l : Fin r) : ℤ :=
  if n ≤ r then (if l.val < n then max (lam l) 0 else 0)
  else (if 2 * r ≤ l.val + n then lam l else max (lam l) 0)

theorem wu_sum {r : ℕ} (f g : Fin r → ℤ) (l0 : Fin r) (c : ℤ) (h0 : f l0 - g l0 = c) (h : ∀ l, l ≠ l0 → f l = g l) :
    ∑ l, f l - ∑ l, g l = c := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l0]
  · exact h0
  · intro b _ hb
    rw [h b hb, sub_self]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem wu_step {r : ℕ} (lam : Fin r → ℤ) (hlam : Antitone lam) (a : ℕ) (ha : a < 2 * r + 1) :
    if decide (a < r ∨ a = 2 * r) = true then Strip (wuSt lam (a + 1)) (wuSt lam a) (wuDeg lam a)
      else Strip (wuSt lam a) (wuSt lam (a + 1)) (wuDeg lam a) := by
  have hadj : ∀ i j : Fin r, i.val + 1 = j.val → lam j ≤ lam i := fun i j hij =>
    hlam (Fin.le_def.mpr (by omega))
  rcases lt_or_ge a r with h1 | h1
  · rw [if_pos (by rw [decide_eq_true_eq]; omega)]
    refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
    · unfold wuSt
      have := l.2
      split_ifs <;> omega
    · unfold wuSt
      have := hadj i j hij
      have := i.2
      have := j.2
      split_ifs <;> omega
    · have e : wuDeg lam a = (lam ⟨a, h1⟩).toNat := by
        unfold wuDeg wuLam
        rw [if_pos h1, dite_eq_left h1]
      rw [e]
      apply wu_sum _ _ ⟨a, h1⟩
      · unfold wuSt
        dsimp only
        split_ifs <;> omega
      · intro l hl
        have hl' : l.val ≠ a := fun h => hl (Fin.ext h)
        unfold wuSt
        split_ifs <;> omega
  · rcases lt_or_ge a (2 * r) with h2 | h2
    · rw [if_neg (by rw [decide_eq_true_eq]; omega)]
      have h3 : 2 * r - 1 - a < r := by omega
      refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
      · unfold wuSt
        have := l.2
        split_ifs <;> omega
      · unfold wuSt
        have := hadj i j hij
        have := i.2
        have := j.2
        split_ifs <;> omega
      · have e : wuDeg lam a = (-(lam ⟨2 * r - 1 - a, h3⟩)).toNat := by
          unfold wuDeg wuLam
          rw [if_neg (by omega), if_pos h2, dite_eq_left h3]
        rw [e]
        apply wu_sum _ _ ⟨2 * r - 1 - a, h3⟩
        · unfold wuSt
          dsimp only
          split_ifs <;> omega
        · intro l hl
          have hl' : l.val ≠ 2 * r - 1 - a := fun h => hl (Fin.ext h)
          have := l.2
          unfold wuSt
          split_ifs <;> omega
    · have h4 : a = 2 * r := by omega
      rw [if_pos (by rw [decide_eq_true_eq]; omega)]
      have e : wuDeg lam a = 0 := by
        unfold wuDeg
        rw [if_neg (by omega), if_neg (by omega)]
      rw [e]
      refine ⟨fun l => ?_, fun i j hij => ?_, ?_⟩
      · unfold wuSt
        have := l.2
        split_ifs <;> omega
      · unfold wuSt
        have := hadj i j hij
        have := i.2
        have := j.2
        split_ifs <;> omega
      · have : wuSt lam (a + 1) = wuSt lam a := by
          funext l
          have := l.2
          unfold wuSt
          split_ifs <;> omega
        rw [this]
        simp

theorem wu_chain {r : ℕ} (lam : Fin r → ℤ) (hlam : Antitone lam) :
    IsChain (wuLL lam) (fun n : Fin (2 * r + 1 + 1) => wuSt lam n.val) := by
  refine ⟨?_, fun i => ?_⟩
  · funext l
    show wuSt lam 0 l = 0
    unfold wuSt
    simp
  · exact wu_step lam hlam i.val i.2

theorem sdXi_zero (r : ℕ) : sdXi r 0 = 1 := by
  unfold sdXi
  simp

theorem wu_prod {r : ℕ} (lam : Fin r → ℤ) :
    ∏ i, (sdXi r ((wuLL lam).deg i) : ℚ) = ∏ l, (sdXi r (lam l).natAbs : ℚ) := by
  show ∏ i : Fin (2 * r + 1), (sdXi r (wuDeg lam i.val) : ℚ) = _
  rw [Fin.prod_univ_eq_prod_range (fun a => (sdXi r (wuDeg lam a) : ℚ)) (2 * r + 1), Finset.prod_range_succ, two_mul,
    Finset.prod_range_add]
  have e1 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam x) : ℚ) = (sdXi r (wuLam lam x).toNat : ℚ) := fun x hx => by
    have := Finset.mem_range.mp hx
    unfold wuDeg
    rw [if_pos this]
  have e2 : ∀ x ∈ Finset.range r, (sdXi r (wuDeg lam (r + x)) : ℚ) =
      (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) (r - 1 - x) := fun x hx => by
    have := Finset.mem_range.mp hx
    unfold wuDeg
    rw [if_neg (by omega), if_pos (by omega)]
    have e : 2 * r - 1 - (r + x) = r - 1 - x := by omega
    rw [e]
  have e3 : wuDeg lam (r + r) = 0 := by
    unfold wuDeg
    rw [if_neg (by omega), if_neg (by omega)]
  rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2,
    Finset.prod_range_reflect (fun y => (sdXi r (-(wuLam lam y)).toNat : ℚ)) r, e3, sdXi_zero, Nat.cast_one, mul_one,
    ← Finset.prod_mul_distrib, ← Fin.prod_univ_eq_prod_range
      (fun x => (sdXi r (wuLam lam x).toNat : ℚ) * (sdXi r (-(wuLam lam x)).toNat : ℚ)) r]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [wuLam_val]
  rcases le_total 0 (lam l) with h | h
  · have a1 : (-(lam l)).toNat = 0 := by omega
    have a2 : (lam l).toNat = (lam l).natAbs := by omega
    rw [a1, a2, sdXi_zero, Nat.cast_one, mul_one]
  · have a1 : (lam l).toNat = 0 := by omega
    have a2 : (-(lam l)).toNat = (lam l).natAbs := by omega
    rw [a1, a2, sdXi_zero, Nat.cast_one, one_mul]

theorem wdimUp_of (hCD : ChainDimAt) : WdimUpAt := by
  intro r _ lam hlam
  have h := wu_single hCD (wuLL lam) _ (wu_chain lam hlam)
  rw [wu_prod] at h
  have e : wuSt lam (Fin.last (2 * r + 1)).val = lam := by
    funext l
    have := l.2
    show wuSt lam (2 * r + 1) l = lam l
    unfold wuSt
    rw [if_neg (by omega), if_pos (by omega)]
  rwa [e] at h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_coe_basis {E : Type} [AddCommGroup E] [Module O E] (Λ : Submodule O E) {n : ℕ}
    (B : Module.Basis (Fin n) O Λ) : Submodule.span O (Set.range fun i => (B i : E)) = Λ := by
  have h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem fock_zero_right {σ : Type} (F : MvPolynomial σ (KK O)) : fock F (0 : MvPolynomial σ (KK O)) = 0 := by
  simp [fock]

theorem smith_block {σ : Type} (Λ : Submodule O (MvPolynomial σ (KK O))) (hfg : Module.Finite O Λ) :
    ∃ (n : ℕ) (al be : Fin n → MvPolynomial σ (KK O)), (∀ i, al i ∈ Λ ∧ be i ∈ Λ) ∧
      (∀ i l, i ≠ l → fock (al i) (be l) = 0) ∧ LinearIndependent O al ∧
      Submodule.span O (Set.range al) = Λ ∧ Submodule.span O (Set.range be) = Λ := by
  classical
  haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O Λ
  obtain ⟨P, Q, hP, hQ, hd⟩ := Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ)
    (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))
  have hPt : IsUnit P.transpose.det := by rw [Matrix.det_transpose]; exact hP
  let alB := e.map (Matrix.toLinearEquiv e P.transpose hPt)
  let beB := e.map (Matrix.toLinearEquiv e Q hQ)
  have hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O)) := fun i => by
    show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp [Matrix.transpose_apply]
  have hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O)) := fun l => by
    show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp
  refine ⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)),
    fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩
  · have h := hd i l hil
    show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0
    rw [hal, hbe, fock_bilin]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  · exact alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)

theorem span_single {β E : Type} [DecidableEq β] [AddCommGroup E] [Module O E] (M : β → Submodule O E) (T : Finset β)
    (hM : ∀ b, b ∉ T → M b = ⊥) (n : β → ℕ) (al : ∀ b, Fin (n b) → E)
    (hspan : ∀ b, Submodule.span O (Set.range (al b)) = M b) :
    Submodule.span O (Set.range fun x : (Σ b : {b // b ∈ T}, Fin (n b.1)) =>
      (Pi.single x.1.1 (al x.1.1 x.2) : β → E)) = Submodule.pi Set.univ M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    beta_reduce
    by_cases h : i = x.1.1
    · subst h
      rw [Pi.single_eq_same, ← hspan]
      exact Submodule.subset_span ⟨x.2, rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have hfT : f = ∑ b ∈ T, Pi.single b (f b) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_pi_single]
      split_ifs with hi
      · rfl
      · have h0 := hf i (Set.mem_univ i)
        rw [hM i hi, Submodule.mem_bot] at h0
        exact h0
    rw [hfT]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hfb : f b ∈ Submodule.span O (Set.range (al b)) := by
      rw [hspan]
      exact hf b (Set.mem_univ b)
    have e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b) := rfl
    rw [e]
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨⟨b, hb⟩, i⟩, rfl⟩

end Gen


open Classical in
theorem smithData_seg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] {s : ℕ}
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hFG : ∀ b, Module.Finite O (blockLat O p r S aTop aPlus m b)) :
    ∃ (n : ℕ) (al be : Fin n → SegVs O r s S.t) (β : Fin n → SegBlock s r),
      SmithData (segForm O p r S) (segLat O p r S aTop aPlus m) n al be β := by
  have hfin := kf_kept_finite p r S aTop
  set T := hfin.toFinset with hT
  have hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b := fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥
  have hMfg : ∀ b, Module.Finite O (M b) := fun b => by
    by_cases hb : Kept p r S aTop b
    · have e : M b = blockLat O p r S aTop aPlus m b := if_pos hb
      rw [e]; exact hFG b
    · have e : M b = ⊥ := if_neg hb
      rw [e]; infer_instance
  have hM0 : ∀ b, b ∉ T → M b = ⊥ := fun b hb => if_neg fun h => hb ((hmemT b).2 h)
  choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)
  let ι := Σ b : {b // b ∈ T}, Fin (n b.1)
  let ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AL : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (al x.1.1 x.2)
  let BE : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (be x.1.1 x.2)
  have hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M := rfl
  have hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M := span_single M T hM0 n al hsa
  have hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M := span_single M T hM0 n be hsb
  refine ⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hL, ← hALs]
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    rw [hALs, ← hBEs]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro i b hb
    exact ⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩
  · intro i l hil
    set x := ev.symm i with hx
    set y := ev.symm l with hy
    have hxy : x ≠ y := fun h => hil (ev.symm.injective h)
    show segForm O p r S (AL x) (BE y) = 0
    rw [segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _),
      Finset.sum_singleton]
    show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1)
      ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0
    rw [Pi.single_eq_same]
    by_cases hb : x.1.1 = y.1.1
    · obtain ⟨⟨xb, hxb⟩, xi⟩ := x
      obtain ⟨⟨yb, hyb⟩, yi⟩ := y
      simp only at hb
      subst hb
      rw [Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]
    · rw [Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]
  · have h1 := Pi.linearIndependent_single (R := O) al hli
    have hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b))) := by
      rintro ⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [eq_of_heq h2]
    exact (h1.comp _ hj).comp _ ev.symm.injective
  · rw [hL, ← hALs, EquivLike.range_comp]
  · rw [hL, ← hBEs, EquivLike.range_comp]

end Formalism.MainNotions.ColumnSystems.Pf
end
end
