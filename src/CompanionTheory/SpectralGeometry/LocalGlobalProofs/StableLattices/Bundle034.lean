module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle001
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit KStab)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x ∧ Deg d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsIn lev d S) := by
  let L : chainsIn lev d S →ₗ[ℂ] (Finset (Pos n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsIn lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem lF_apply (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    lF E p q x A = E p q (x A) + ∑ i : Pos n, ∑ k : Pos n, adC p q i k • cre k (ann i x) A := by
  simp [lF, adL, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]

theorem cre_ann_mem {S : Submodule ℂ V} {x : Cn n V} (hx : ∀ A, x A ∈ S) (i k : Pos n) (A : Finset (Pos n)) :
    cre k (ann i x) A ∈ S := by
  rw [CompanionTheory.D.LK.Car.cre_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [CompanionTheory.D.LK.Car.ann_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  by_cases c1 : q = i.1.1 ∧ k.1 = (p, i.1.2)
  · show lev k.1.1 < lev k.1.2
    rw [c1.2]
    show lev p < lev i.1.2
    rw [hpq, c1.1]
    exact hi
  by_cases c2 : i.1.2 = p ∧ k.1 = (i.1.1, q)
  · show lev k.1.1 < lev k.1.2
    rw [c2.2]
    show lev i.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hi
  · exact absurd (by simp [adC, c1, c2]) h

theorem lF_ne {E : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cn n V} {A : Finset (Pos n)}
    (h : lF E p q x A ≠ 0) : x A ≠ 0 ∨ ∃ i k, adC p q i k ≠ 0 ∧ cre k (ann i x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [lF_apply, hc.1, map_zero, zero_add]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases h0 : adC p q i k = 0
  · rw [h0, zero_smul]
  · rw [hc.2 i k h0, smul_zero]

theorem term_supp {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cn n V}
    (hx : SuppIn (inU lev) x) (hd : Deg d x) {A : Finset (Pos n)} {i k : Pos n} (h0 : adC p q i k ≠ 0)
    (h : cre k (ann i x) A ≠ 0) : (∀ j ∈ A, inU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := CompanionTheory.D.LK.cre_ne h
  obtain ⟨h2, h3⟩ := CompanionTheory.D.LK.ann_ne h1
  have hs := hx _ h3
  have hi : inU lev i := hs i (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inU_of_adC hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem lF_mem_chainsIn {ε : Fin n → Bool} {lev : Fin n → ℕ} {d : ℕ} {E : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : KStab ε E S) {p q : Fin n} (hε : ε p = ε q) (hpq : lev p = lev q) {x : Cn n V}
    (hx : x ∈ chainsIn lev d S) : lF E p q x ∈ chainsIn lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx1 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').1
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx2 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').2
  · rw [lF_apply]
    exact S.add_mem (hS p q hε _ (hx3 A)) (S.sum_mem fun i _ => S.sum_mem fun k _ =>
      S.smul_mem _ (cre_ann_mem hx3 i k A))

theorem exists_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cn n V), LocFin ε E → SuppIn (inU lev) y → Deg d y →
    ∃ T : Submodule ℂ (Cn n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppIn (inU lev) x ∧ Deg d x) ∧
      ∀ p q : Fin n, ε p = ε q → lev p = lev q → ∀ x ∈ T, lF E p q x ∈ T := by
  intro n ε lev V _ _ E d y hF hy hd
  choose Sf hfd hSt hmem using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  haveI : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : KStab ε E S := fun a b h v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b h z hz) : S ≤ S.comap (E a b)) hv
  refine ⟨chainsIn lev d S, finiteDimensional_chainsIn lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hε hpq x hx => lF_mem_chainsIn hSs hε hpq hx⟩

end GlobalTheory.CompanionTheory.RgExhStableChains
end
end

section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ClusterNum

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq abs_sig)
open PI.UpqRep

theorem numKG : NumKG := by
  intro n ε γ lev ν B C hG hB hBn hC _ hdom hn
  set X := xv ε γ with hX
  set κ := X - rhoC ε - wt B with hκ
  set μ := X - wt B - wt C with hμ
  obtain ⟨hXa, -, hgap⟩ := hG
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  have hκw := sorted_weight_eq_of_norm_eq ε κ μ ν C hC w hw hs (hdom w hw)
    (fun a => by simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring) hn
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => (hBn _ h2).1 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hcd' : c < d := hcd
  have hne : t c d = -1 := by
    have h1 : ¬ε c = ε d := (hBn _ hi).1
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have hgcd : Lc n ≤ X c - X d := hgap c d (hBn _ hi).2

  have p1 := pair_eq t ta X
  have p2 := pair_eq sig sig_anti X
  have hD : ∀ a b, 0 ≤ sig a b * (X a - X b) - t a b * (X a - X b) := fun a b => by
    rw [sig_mul hXa, sub_nonneg]
    exact (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (tb' a b))
  have hDcd : 2 * Lc n ≤ sig c d * (X c - X d) - t c d * (X c - X d) := by
    rw [hne, show sig c d = 1 by simp [sig, hcd']]
    linarith
  have hsum : ∑ a, ∑ b, t a b * (X a - X b) + 2 * Lc n ≤ ∑ a, ∑ b, sig a b * (X a - X b) := by
    have h1 : sig c d * (X c - X d) - t c d * (X c - X d) ≤
        ∑ a, ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)) :=
      (Finset.single_le_sum (f := fun b => sig c b * (X c - X b) - t c b * (X c - X b))
        (fun b _ => hD c b) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)))
        (fun a _ => Finset.sum_nonneg fun b _ => hD a b) (mem_univ c))
    simp only [Finset.sum_sub_distrib] at h1
    linarith
  have hy : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) := fun a => by
    have h1 := hκw (w.symm a)
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    have ts : ∑ b, t a b = ∑ b, sig a b - ∑ b, sc ε a b - 2 * ∑ b, (ind B a b - ind B b a) +
        ∑ b, sc ε (w.symm a) (w.symm b) := by
      simp only [t]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b),
        Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]
    simp only [hκ, Equiv.apply_symm_apply, Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ts]
    linarith
  have hY : ∀ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := fun a => by
    have e : (∑ b, t a b) / 2 - (∑ b, sig a b) / 2 = (∑ b, (t a b - sig a b)) / 2 := by
      rw [Finset.sum_sub_distrib]; ring
    have h2 : |∑ b, (t a b - sig a b)| ≤ 2 * (n : ℝ) := by
      calc _ ≤ ∑ b, |t a b - sig a b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin n, (2 : ℝ) := Finset.sum_le_sum fun b _ => by
            have := abs_sub (t a b) (sig a b)
            linarith [tb' a b, abs_sig a b]
        _ = 2 * (n : ℝ) := by simp [mul_comm]
    rw [e, div_pow]
    have h3 : (∑ b, (t a b - sig a b)) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  have g1 : vNormSq ε ν = ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 := by
    unfold vNormSq nsq dot
    rw [← Equiv.sum_comp w.symm]
    exact Finset.sum_congr rfl fun a _ => by rw [hy, sq]
  have g2 : vNormSq ε γ = ∑ a, X a ^ 2 := by
    unfold vNormSq nsq dot
    exact Finset.sum_congr rfl fun a _ => (sq _).symm
  have g3 : ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 = ∑ a, X a ^ 2 +
      (2 * ∑ a, X a * ((∑ b, t a b) / 2) - 2 * ∑ a, X a * ((∑ b, sig a b) / 2)) +
      ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have g4 : ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc _ ≤ ∑ _a : Fin n, (n : ℝ) ^ 2 := Finset.sum_le_sum fun a _ => hY a
      _ = (n : ℝ) ^ 3 := by simp; ring
  have g5 : (n : ℝ) ^ 3 < Lc n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Lc
    nlinarith [pow_le_pow_left₀ h0 (by linarith : (n : ℝ) ≤ n + 1) 3, pow_pos (by linarith : (0 : ℝ) < n + 1) 3]
  rw [g1, g2, g3]
  linarith

end GlobalTheory.CompanionTheory.ClusterNum
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgFarRen

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor Tm sgn)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

theorem glRel_renum {A : Type*} [Ring A] {E : Fin n → Fin n → A} (hE : GlRel E) (s : Equiv.Perm (Fin n)) :
    GlRel (fun a b => E (s a) (s b)) := by
  intro a b c d
  have h := hE (s a) (s b) (s c) (s d)
  simpa only [Equiv.apply_eq_iff_eq] using h

theorem tm_renum {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n)) (u : ℂ)
    (a b : Fin n) : Tm (fun a b => E (s a) (s b)) u a b = Tm E u (s a) (s b) := by
  simp only [Formalism.REAL.Tm, Equiv.apply_eq_iff_eq]

theorem qminor_renum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n))
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (s a) (s b)) a b u = qminor E (s ∘ a) (s ∘ b) u := by
  unfold Formalism.REAL.qminor
  simp only [tm_renum, Function.comp_apply]

theorem qdet_renum {A : Type} [Ring A] [Algebra ℂ A] {E : Fin n → Fin n → A} (hE : GlRel E)
    (s : Equiv.Perm (Fin n)) (u : ℂ) : qdet (fun a b => E (s a) (s b)) u = qdet E u := by
  have h1 : qdet (fun a b => E (s a) (s b)) u = qminor E (id ∘ ⇑s) (id ∘ ⇑s) u := by
    unfold Formalism.REAL.qdet
    rw [qminor_renum]
    rfl
  have hsq : ((Equiv.Perm.sign s : ℤ) : A) * ((Equiv.Perm.sign s : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [h1, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds A n n E hE, ← mul_assoc, hsq, one_mul]
  rfl

theorem symm_lt {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    s.symm a < s.symm b := by
  rcases lt_trichotomy (s.symm a) (s.symm b) with h | h | h
  · exact h
  · exact absurd (s.symm.injective h) (ne_of_lt hab)
  · have h' := hs (s.symm b) (s.symm a) h (by simp [he])
    simp only [Equiv.apply_symm_apply] at h'
    exact absurd h' (lt_asymm hab)

theorem kHighest_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) (u : V) :
    KHighest ε E γ u ↔ KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) u := by
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨fun a => hw (s a), fun a b hab he => hz (s a) (s b) (hs a b hab he) he⟩
  · rintro ⟨hw, hz⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · simpa using hw (s.symm a)
    · have h := hz (s.symm a) (s.symm b) (symm_lt hs hab he) (by simpa using he)
      simpa using h

theorem rhoC_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (Finset.univ.filter (fun b => a < b ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => s a < b ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs a b hb.1 hb.2.symm, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2.symm
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  have h2 : (Finset.univ.filter (fun b => b < a ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => b < s a ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs b a hb.1 hb.2, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  simp only [PI.UpqRep.rhoC, Function.comp_apply, h1, h2]

theorem vNormSq_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    vNormSq (ε ∘ s) (γ ∘ s) = vNormSq ε γ := by
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  rw [rhoC_renum hs]
  exact Fintype.sum_equiv s _ _ (fun a => by simp)

theorem isMinG_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    IsMinG ε E γ ↔ IsMinG (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) := by
  unfold CompanionTheory.RgExh.U.IsMinG
  constructor
  · intro h μ x hx hk
    have hμ : μ = (μ ∘ s.symm) ∘ s := by
      funext a
      simp
    rw [hμ] at hk ⊢
    rw [vNormSq_renum hs, vNormSq_renum hs]
    exact h _ x hx ((kHighest_iff E hs _ x).mpr hk)
  · intro h μ x hx hk
    have h' := h (μ ∘ s) x hx ((kHighest_iff E hs μ x).mp hk)
    rwa [vNormSq_renum hs, vNormSq_renum hs] at h'

theorem renumber : CompanionTheory.RgExh.U.Renumber := by
  intro n ε V _ _ E hE s hs
  refine ⟨glRel_renum hE s, fun hU a b x y => hU (s a) (s b) x y, ?_, ?_,
    fun γ u => kHighest_iff E hs γ u, fun γ => isMinG_iff E hs γ, rhoC_renum hs⟩
  · intro hL x
    obtain ⟨S, hS, hK, hx⟩ := hL x
    exact ⟨S, hS, fun a b hab v hv => hK (s a) (s b) hab v hv, hx⟩
  · intro χ hχ Y
    exact (qdet_renum hE s _).trans (hχ Y)

end GlobalTheory.CompanionTheory.RgFarRen
end
end
