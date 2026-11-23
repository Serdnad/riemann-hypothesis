module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
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

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {S E κ : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E)

private lemma act_inv_act (v : Sˣ) (m : E) : act ((v⁻¹ : Sˣ) : S) (act (v : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]

private lemma act_act_inv (v : Sˣ) (m : E) : act (v : S) (act ((v⁻¹ : Sˣ) : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

private lemma prod_inv_inv (u : κ → Sˣ) (L : Finset κ) : (∏ l ∈ L, (u⁻¹) l)⁻¹ = ∏ l ∈ L, u l := by
  simp [Finset.prod_inv_distrib]

private lemma unsc_inv_unsc (u : κ → Sˣ) (c : Finset κ → E) : unsc act u⁻¹ (unsc act u c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_act_inv act _ _

private lemma unsc_unsc_inv (u : κ → Sˣ) (c : Finset κ → E) : unsc act u (unsc act u⁻¹ c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_inv_act act _ _

private lemma unsc_inj (u : κ → Sˣ) {c c' : Finset κ → E} (h : unsc act u c = unsc act u c') : c = c' := by
  rw [← unsc_inv_unsc act u c, h, unsc_inv_unsc]

variable [LinearOrder κ]

private lemma mem_C_iff (M : Submodule ℂ E) (u : κ → Sˣ) (z r : κ → S) (n : ℤ) (c : Finset κ → E) :
    c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n := by
  simp only [kosT, kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n
  · simp only [h, if_true]
    constructor
    · rintro ⟨m, hm, hc⟩
      change act _ (c s) ∈ M
      rw [← hc, act_inv_act]
      exact hm
    · intro hm
      exact ⟨_, hm, act_act_inv act _ _⟩
  · simp only [h, if_false, Submodule.mem_bot]
    constructor
    · intro h0
      simp [unsc, h0]
    · intro h0
      have h1 : act ((∏ l ∈ s, u l : Sˣ) : S) (unsc act u c s) = 0 := by rw [h0, map_zero]
      simpa only [unsc, act_act_inv] using h1

private lemma unsc_wd (u : κ → Sˣ) (z r : κ → S) (hr : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ)) (c : Finset κ → E) :
    unsc act u (wd (fun l => act (z l)) c) = wd (fun l => act (r l)) (unsc act u c) := by
  funext t

  simp only [unsc, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
  LinearMap.proj_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have hp : (∏ l ∈ t, u l) = u i * ∏ l ∈ t.erase i, u l := (Finset.mul_prod_erase t u hi).symm
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hr, hp, mul_inv, Units.val_mul]
  congr 2
  ring

end

theorem UpperTheory.Gal.productCup_of_system.rS_of :
    RS := by
  intro S E _ _ _ _ act κ _ _ M u r z hr n c
  have hD : ∀ c, unsc act u ((kosT act M u z).D c) = (kos act M r).D (unsc act u c) :=
    fun c => unsc_wd act u z r hr c
  have hC : ∀ n c, c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n :=
    fun n c => mem_C_iff act M u z r n c
  refine ⟨hC n c, ?_, ?_, unsc_inv_unsc act u c, unsc_unsc_inv act u c⟩
  · simp only [Cx.Z, Submodule.mem_inf, LinearMap.mem_ker]
    refine and_congr (hC n c) ?_
    rw [← hD]
    constructor
    · intro h
      rw [h]
      funext L
      simp [unsc]
    · intro h
      refine unsc_inj act u (h.trans ?_)
      funext L
      simp [unsc]
  · simp only [Cx.B, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨unsc act u y, (hC _ y).1 hy, (hD y).symm⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨unsc act u⁻¹ y, (hC _ _).2 ?_, unsc_inj act u ?_⟩
      · rwa [unsc_unsc_inv]
      · rw [hD, unsc_unsc_inv, h]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices

private lemma mem_lft' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : ι) :
    a ∈ lft s ↔ toLex (Sum.inl a) ∈ s := by
  simp [lft, Finset.mem_toLeft]

private lemma mem_rgt' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : κ) :
    a ∈ rgt s ↔ toLex (Sum.inr a) ∈ s := by
  simp [rgt, Finset.mem_toRight]

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    lft s ⊆ lft s' := fun a ha => (mem_lft' _ _).2 (h ((mem_lft' _ _).1 ha))

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    rgt s ⊆ rgt s' := fun a ha => (mem_rgt' _ _).2 (h ((mem_rgt' _ _).1 ha))

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

private lemma u_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (l : κ) :
    ((T.u n a b l * (T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  have e : T.u n a b l * (T.u n a' b' l)⁻¹ =
      (T.X a * (T.X a')⁻¹) ^ (n l).1 * (T.Y b * (T.Y b')⁻¹) ^ (n l).2 := by
    simp only [Sys.u, mul_inv, mul_pow, inv_pow]
    ac_rfl
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact mul_mem (pow_mem (hT.memX I J hJ a' ha' a) _) (pow_mem (hT.memY I J hI b' hb' b) _)

private lemma prod_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
  exact Subalgebra.prod_mem _ (fun l _ => u_quot T hT n hI hJ ha' hb' l)

private lemma lat_le (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) ≤
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) := by
  rintro y ⟨m, hm, rfl⟩
  have hr := prod_quot T hT n hI hJ (a := a) (b := b) ha' hb' L
  refine ⟨T.act (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) m,
    hT.stab I J hI hJ _ hr m hm, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, mul_comm (∏ l ∈ L, T.u n a b l),
    mul_inv_cancel_left]

private lemma lat_eq (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha : a ∈ I) (ha' : a' ∈ I) (hb : b ∈ J) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) =
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) :=
  le_antisymm (lat_le T hT n hI hJ ha' hb' L) (lat_le T hT n hI hJ ha hb L)

private lemma lat_mono (hT : T.Good) (n : κ → ℕ × ℕ) {I I' J J' : Finset (Fin (d + 1))} (hI : I.Nonempty)
    (hJ : J.Nonempty) (hII : I ⊆ I') (hJJ : J ⊆ J') (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) ≤
      (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I') (pk J') l : Sˣ) : S)) := by
  have hI' := Finset.Nonempty.mono hII hI
  have hJ' := Finset.Nonempty.mono hJJ hJ
  calc (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))
      ≤ (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) :=
        Submodule.map_mono (hT.monoM I I' J J' hI hJ hII hJJ)
    _ = _ := lat_eq T hT n hI' hJ' (hII (pk_mem' hI)) (pk_mem' hI') (hJJ (pk_mem' hJ)) (pk_mem' hJ') L

private lemma r_mem (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (l : κ) : T.r n z i j l ∈ T.R I J :=
  hT.monoR {i} I {j} J (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
    (Finset.singleton_subset_iff.2 hi) (Finset.singleton_subset_iff.2 hj) (hA i j l)

private lemma col_eq (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    T.colCx n z I J = kosT T.act (T.M I J) (T.u n i j) z := by
  unfold Sys.colCx kosT
  congr 1
  funext L
  exact lat_eq T hT n ⟨i, hi⟩ ⟨j, hj⟩ (pk_mem' ⟨i, hi⟩) hi (pk_mem' ⟨j, hj⟩) hj L

private lemma mix_mono (hT : T.Good) (n : κ → ℕ × ℕ) (L : Finset κ) {s s' : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))}
    (hs : s ⊆ s') {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s' := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · have h' : (lft s').Nonempty ∧ (rgt s').Nonempty :=
      ⟨Finset.Nonempty.mono (lft_mono' hs) h.1, Finset.Nonempty.mono (rgt_mono' hs) h.2⟩
    rw [if_pos h] at hm
    rw [if_pos h']
    exact lat_mono T hT n h.1 h.2 (lft_mono' hs) (rgt_mono' hs) L hm
  · rw [if_neg h, Submodule.mem_bot] at hm
    subst hm
    exact zero_mem _

private lemma mix_step (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) (L : Finset κ) {l : κ} (hl : l ∉ L)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))) {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ insert l L, T.u n (pk I) (pk J) l : Sˣ) : S))) s := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · rw [if_pos h] at hm ⊢
    rw [Submodule.mem_map] at hm ⊢
    obtain ⟨m0, hm0, rfl⟩ := hm
    refine ⟨T.act (T.r n z (pk (lft s)) (pk (rgt s)) l) m0,
      hT.stab _ _ h.1 h.2 _ (r_mem T hT n z hA (pk_mem' h.1) (pk_mem' h.2) l) m0 hm0, ?_⟩
    have e : ((∏ k ∈ insert l L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) *
        T.r n z (pk (lft s)) (pk (rgt s)) l =
        z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) := by
      have hu := Units.mul_inv (T.u n (pk (lft s)) (pk (rgt s)) l)
      rw [Finset.prod_insert hl, Units.val_mul]
      simp only [Sys.r]
      linear_combination (z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S)) * hu
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  · rw [if_neg h, Submodule.mem_bot] at hm
    rw [if_neg h, hm, map_zero]
    exact zero_mem _

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.sysOk_of :
    WdUni → SysOk := by
  intro _
  unfold SysOk
  intro d S E _ _ _ _ T κ _ _ n z hT hA
  refine ⟨⟨?_, ?_⟩, fun I J i hi j hj => ⟨fun l => r_mem T hT n z hA hi hj l, col_eq T hT n z hi hj⟩, ?_⟩
  · intro i j
    unfold Sys.wt
    rcases ofLex i with a | a <;> rcases ofLex j with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact Commute.one_left _
    · exact Commute.one_left _
    · exact Commute.one_right _
    · exact (Commute.all (z a) (z b)).map T.act
  · intro s t ht m hm
    obtain ⟨x, rfl⟩ : ∃ x : Two d ⊕ κ, toLex x = t := ⟨ofLex t, rfl⟩
    beta_reduce at hm ⊢
    rcases x with a | l
    · have hw : T.wt z (toLex (Sum.inl a)) = 1 := rfl
      rw [hw, Module.End.one_apply]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s ⊆ lft s1 → rgt s1 = rgt s →
          m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h2]
        exact mix_mono T hT n (rgt s) h1 hm
      refine gen _ ?_ ?_
      · intro b hb
        rw [mem_lft'] at hb ⊢
        simp [hb]
      · ext b
        simp [mem_rgt']
    · have hl : l ∉ rgt s := fun h => ht ((mem_rgt' s l).1 h)
      have key := mix_step T hT n z hA (rgt s) hl (lft s) hm
      have hw : T.wt z (toLex (Sum.inr l)) = T.act (z l) := rfl
      rw [hw]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s1 = lft s → rgt s1 = insert l (rgt s) →
          T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h1, h2]
        exact key
      refine gen _ ?_ ?_
      · ext b
        simp [mem_lft']
      · ext b
        simp [mem_rgt']
  · intro I I' J J' hI hJ hII hJJ m x hx
    simp only [Cx.Z, Sys.colCx, kosT, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
      true_implies] at hx ⊢
    refine ⟨fun L => ?_, hx.2⟩
    have hxL := hx.1 L
    split_ifs at hxL ⊢
    · exact lat_mono T hT n hI hJ hII hJJ L hxL
    · exact hxL
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem cubeSign_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n) :
    GlobalTheory.cubeSign t (t.orderEmbOfFin h k) = (-1) ^ (k : ℕ) :=
  _root_.UpperTheory.Reformulated.B.Qh71.cubeSign_emb t h k

private theorem erase_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n + 1) (k : Fin (n + 1))
    (h' : (t.erase (t.orderEmbOfFin h k)).card = n) (a : Fin n) :
    (t.erase (t.orderEmbOfFin h k)).orderEmbOfFin h' a = t.orderEmbOfFin h (k.succAbove a) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a))
    (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this a).symm

private theorem detC_erase {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (t : Finset κ)
    (h : t.card = p + 1) (k : Fin (p + 1)) :
    detC ρ (t.erase (t.orderEmbOfFin h k)) =
      (Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b).det := by
  have h' : (t.erase (t.orderEmbOfFin h k)).card = p := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]; rfl
  unfold detC
  rw [dite_eq_left h']
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [erase_emb t h k h' a]

private theorem ring_core {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (f : Fin p → S)
    (t : Finset κ) (h : t.card = p + 1) :
    ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) = 0 := by
  set e := t.orderEmbOfFin h with he
  let A : Matrix (Fin (p + 1)) (Fin (p + 1)) S :=
    Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))
  have hA : A.det = 0 := by
    have h1 := Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)
    have h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A := by
      ext a b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]
      · simp [A, Matrix.updateCol_apply, Fin.succ_ne_zero]
    rw [h2] at h1
    simpa using h1
  have ht : t = Finset.univ.map e.toEmbedding := by
    rw [he, Finset.map_orderEmbOfFin_univ]
  have hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) =
      ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * detC ρ (t.erase (e k))) := by
    conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i))) =
      ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) by
        rw [← ht]]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RelEmbedding.coe_toEmbedding]
    rw [he, cubeSign_emb t h k]
  rw [hs, ← hA, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he, detC_erase ρ t h k]
  have : (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b := by
    ext a b
    simp [A, he]
  rw [this]
  simp [A, he, mul_assoc]

theorem UpperTheory.Gal.productCup_of_system.det_of :
    Det := by
  intro S E _ _ _ _ act κ _ p ρ f m
  funext t
  have key : wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) t =
      ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • act (∑ b, ρ i b * f b) (act (detC ρ (t.erase i)) m) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [key]
  by_cases h : t.card = p + 1
  · have h0 := congrArg (fun x => act x m) (ring_core ρ f t h)

    simp only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0
    rw [Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  · rw [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ p := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [detC, hc]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
end
