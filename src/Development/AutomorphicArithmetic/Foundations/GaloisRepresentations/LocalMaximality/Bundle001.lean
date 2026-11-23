module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]

    rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_zero' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (x : Finset ι → E) (t : Finset ι) : wd (fun _ : ι => (0 : Module.End ℂ E)) x t = 0 := by
  simp [wd]

private theorem uni_inter_map_inrE {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ]
    (b : Finset β) (L : Finset κ) :
    uni b L ∩ Finset.map (inrE (β := β)).toEmbedding Finset.univ = L.map (inrE (β := β)).toEmbedding := by
  ext x
  simp [GlobalTheory.WH.uni, inrE]
  constructor
  · rintro ⟨h, a, rfl⟩
    exact ⟨a, by simpa using h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, a, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.colQEx_of :
    WdUni → ColQEx := by
  intro hU β κ E _ _ _ _ _ _ A w d hK n m hm c hc hlev hcz
  set Q := Finset.map (inrE (β := β) (κ := κ)).toEmbedding Finset.univ with hQ
  have hQc : ∀ (b : Finset β) (L : Finset κ), (uni b L ∩ Q).card = L.card := by
    intro b L
    rw [hQ, uni_inter_map_inrE]
    simp
  have hl : (fun i : β => wOn Q w (inlE i)) = fun _ => 0 := by
    funext i
    have : inlE (κ := κ) i ∉ Q := by
      simp [hQ, inlE, inrE]
    simp [wOn, this]
  have hr : (fun l : κ => wOn Q w (inrE l)) = fun l => w (inrE l) := by
    funext l
    have : inrE (β := β) l ∈ Q := by
      simp [hQ]
    simp [wOn, this]
  have hdec : ∀ (x : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ),
      wd (wOn Q w) x (uni b L) =
        (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => x (uni b L')) L := by
    intro x b L
    rw [(hU β κ E (wOn Q w) x b L).1, hl, hr, wd_zero', zero_add]
  have hmem : ∀ s, c s ∈ (if ((s.card : ℕ) : ℤ) = n then A s else ⊥) := by
    intro s
    have := hc
    simp only [acx, Submodule.mem_pi, Set.mem_univ, true_implies] at this
    exact this s
  have hY : ∀ b : Finset β, ∃ Y ∈ (colA A w b).C (m - 1),
      wd (fun l => w (inrE l)) Y = fun L => c (uni b L) := by
    intro b
    have hz : (fun L => c (uni b L)) ∈ (colA A w b).Z m := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [colA, acx, Submodule.mem_pi]
        intro L _
        show c (uni b L) ∈ (if ((L.card : ℕ) : ℤ) = m then A (uni b L) else ⊥)
        by_cases hL : ((L.card : ℕ) : ℤ) = m
        · rw [if_pos hL]
          have h1 := hmem (uni b L)
          split_ifs at h1 with h2
          · exact h1
          · rw [Submodule.mem_bot] at h1
            rw [h1]
            exact Submodule.zero_mem _
        · rw [if_neg hL, Submodule.mem_bot]
          apply hlev
          show ¬ (((uni b L ∩ Q).card : ℕ) : ℤ) = m
          rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
      · rw [LinearMap.mem_ker]
        change wd (fun l => w (inrE l)) (fun L => c (uni b L)) = 0
        funext L
        have h1 : (wd (wOn Q w)) c (uni b L) = 0 := by
          exact congrFun hcz (uni b L)
        rw [hdec] at h1
        simp only [Pi.zero_apply]
        have h2 := congrArg (fun v => (-1 : ℤ) ^ b.card • v) h1
        simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h2
        exact h2
    obtain ⟨Y, hY1, hY2⟩ := hK b m hm hz
    exact ⟨Y, hY1, hY2⟩
  choose Y hYC hYD using hY
  have hYmem : ∀ b L, Y b L ∈ (if ((L.card : ℕ) : ℤ) = m - 1 then A (uni b L) else ⊥) := by
    intro b L
    have := hYC b
    rw [colA, acx, Submodule.mem_pi] at this
    exact this L (Set.mem_univ _)
  have hU2 := fun s => (hU β κ E w c (lft s) (rgt s)).2.2.2.2 s
  have hQs : ∀ s, (s ∩ Q).card = (rgt s).card := by
    intro s
    have := hQc (lft s) (rgt s)
    rw [hU2 s] at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y : Finset (β ⊕ₗ κ) → E, ∀ s, y s = if (((lft s).card : ℕ) : ℤ) = n - m then
      (-1 : ℤ) ^ (lft s).card • Y (lft s) (rgt s) else 0 := ⟨_, fun s => rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [acx, Submodule.mem_pi]
    intro s _
    show y s ∈ (if ((s.card : ℕ) : ℤ) = n - 1 then A s else ⊥)
    rw [hy]
    have hs := hYmem (lft s) (rgt s)
    rw [hU2 s] at hs
    have hcard := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rw [hU2 s] at hcard
    by_cases h1 : (((lft s).card : ℕ) : ℤ) = n - m
    · rw [if_pos h1]
      by_cases h2 : ((s.card : ℕ) : ℤ) = n - 1
      · rw [if_pos h2]
        by_cases h3 : (((rgt s).card : ℕ) : ℤ) = m - 1
        · rw [if_pos h3] at hs
          exact zsmul_mem hs _
        · rw [if_neg h3, Submodule.mem_bot] at hs
          rw [hs, smul_zero]
          exact Submodule.zero_mem _
      · rw [if_neg h2, Submodule.mem_bot]
        rw [if_neg, Submodule.mem_bot] at hs
        · rw [hs, smul_zero]
        · intro h3
          apply h2
          rw [hcard]
          push_cast
          omega
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · intro s hs
    rw [hy]
    split_ifs with h1
    · have hY0 := hYmem (lft s) (rgt s)
      rw [if_neg] at hY0
      · rw [Submodule.mem_bot] at hY0
        rw [hY0, smul_zero]
      · intro h3
        apply hs
        show (((s ∩ Q).card : ℕ) : ℤ) = m - 1
        rw [hQs s]
        exact h3
    · rfl
  · funext t
    obtain ⟨b, L, rfl⟩ : ∃ b L, t = uni b L := ⟨lft t, rgt t, (hU2 t).symm⟩
    refine Eq.trans (b := (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => y (uni b L')) L) ?_ ?_
    · convert hdec y b L
    have hb2 := hU β κ E w c b
    have hfun : (fun L' => y (uni b L')) =
        if (((b.card : ℕ) : ℤ) = n - m) then (-1 : ℤ) ^ b.card • Y b else 0 := by
      funext L'
      rw [hy, (hb2 L').2.1, (hb2 L').2.2.1]
      split_ifs <;> rfl
    rw [hfun]
    by_cases hb : (((b.card : ℕ) : ℤ) = n - m)
    · rw [if_pos hb, map_zsmul, Pi.smul_apply, hYD, smul_smul, ← mul_pow]
      simp
    · rw [if_neg hb, map_zero, Pi.zero_apply, smul_zero]
      symm
      by_cases hL : ((L.card : ℕ) : ℤ) = m
      · have h5 := hmem (uni b L)
        rw [if_neg] at h5
        · exact (Submodule.mem_bot _).1 h5
        · intro hn
          apply hb
          rw [(hb2 L).2.2.2.1] at hn
          push_cast at hn
          omega
      · apply hlev
        show ¬ ((((uni b L ∩ Q).card : ℕ) : ℤ) = m)
        rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma inter_inr_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (_i : DecidableEq (β ⊕ₗ κ))
    (b : Finset β) (L : Finset κ) :
    (uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = L.card := by
  have h : uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding =
      L.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with i | l <;> simp [uni, inrE]
  rw [h, Finset.card_map]

private lemma inl_not_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (i : β) :
    (inlE i : β ⊕ₗ κ) ∉ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp [inlE, inrE]

private lemma inr_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp

theorem UpperTheory.Gal.productCup_of_system.localOne_of_gl1 :
    FiltrationBoundaryCriterion → ColQEx → WdUni → L1 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c hc hd hB
  have e : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w c ∅ ∅).2.2.2.2
  have eL : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w c b L).2.1
  have eR : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w c b L).2.2.1
  have eC : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    have := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rwa [e s] at this
  have hS : ∀ (_i : DecidableEq (β ⊕ₗ κ)) (s : Finset (β ⊕ₗ κ)),
      (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := fun i s => by
    have := inter_inr_card i (lft s) (rgt s)
    rwa [e s] at this
  have hy : ∀ b : Finset β, (b.card : ℤ) = n - d →
      ∃ y ∈ (colA A w b).C (d - 1), (colA A w b).D y = col c b := fun b hb => by
    obtain ⟨y, hy, h⟩ := hB b hb
    exact ⟨y, hy, h⟩
  let yb : Finset β → Finset κ → E := fun b => if h : (b.card : ℤ) = n - d then (hy b h).choose else 0
  have hyb : ∀ b, (b.card : ℤ) = n - d → yb b ∈ (colA A w b).C (d - 1) ∧ (colA A w b).D (yb b) = col c b := by
    intro b hb
    simp only [yb, dif_pos hb]
    exact (hy b hb).choose_spec
  have hy0 : ∀ b, ¬ (b.card : ℤ) = n - d → yb b = 0 := by
    intro b hb
    simp only [yb, dif_neg hb]
  let y : Finset (β ⊕ₗ κ) → E := fun s => ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s)
  have hmem : ∀ b, (b.card : ℤ) = n - d → ∀ L, yb b L ∈ (if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := by
    intro b hb L
    have h : yb b ∈ Submodule.pi Set.univ
      (fun L : Finset κ => if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := (hyb b hb).1
    exact (Submodule.mem_pi.1 h) L (Set.mem_univ _)
  have hz : ∀ s, ¬ (((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1) → y s = 0 := by
    intro s hs
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have hL : ¬ ((rgt s).card : ℤ) = d - 1 := fun h => hs ⟨hb, h⟩
      have h1 := hmem _ hb (rgt s)
      rw [if_neg hL, Submodule.mem_bot] at h1
      simp only [y, h1, smul_zero]
    · simp only [y, hy0 _ hb, Pi.zero_apply, smul_zero]
  have hcC : ∀ s : Finset (β ⊕ₗ κ), ¬ (s.card : ℤ) = n → c s = 0 := by
    intro s hs
    have h : c ∈ Submodule.pi Set.univ
      (fun s : Finset (β ⊕ₗ κ) => if (s.card : ℤ) = n then A s else ⊥) := hc.1
    have h1 := (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    rwa [if_neg hs, Submodule.mem_bot] at h1
  refine hG (β ⊕ₗ κ) E A w (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) d n hW
    (hC β κ E A w d hK) c hc ?_ ⟨y, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : d < ((rgt s).card : ℤ) := by
      rw [hS _ s] at hs
      exact not_le.1 hs
    have := hd (lft s) (rgt s) hs'
    rwa [e s] at this
  · refine Submodule.mem_pi.2 fun s _ => ?_
    by_cases h : ((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1
    · have hcard : (s.card : ℤ) = n - 1 := by
        rw [eC s]; push_cast; omega
      have h1 := hmem _ h.1 (rgt s)
      rw [if_pos h.2, e s] at h1
      show y s ∈ (if (s.card : ℤ) = n - 1 then A s else ⊥)
      rw [if_pos hcard]
      exact zsmul_mem h1 _
    · rw [hz s h]
      exact zero_mem _
  · intro s hs
    rw [hS _ s] at hs
    exact hz s fun h => hs h.2
  · intro s hs
    rw [hS _ s] at hs
    conv_lhs => rw [← e s]
    rw [(hU β κ E _ y (lft s) (rgt s)).1]
    have h0 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun i : β => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inlE i)) = fun _ => 0 := by
      intro _i
      funext i
      simp only [wOn, if_neg (inl_not_mem i)]
    have h1 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun l : κ => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inrE l)) = fun l => w (inrE l) := by
      intro _i
      funext l
      simp only [wOn, if_pos (inr_mem l)]
    have h2 : (fun L' : Finset κ => y (uni (lft s) L')) = ((-1 : ℤ) ^ (lft s).card) • yb (lft s) := by
      funext L'
      simp only [y, eL, eR, Pi.smul_apply]
    have h3 : wd (fun _ : β => (0 : Module.End ℂ E)) (fun b' => y (uni b' (rgt s))) (lft s) = 0 := by
      simp [wd]
    rw [h0 _, h1 _, h3, zero_add, h2, map_zsmul, Pi.smul_apply, smul_smul, ← mul_pow]
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have h4 := congrFun (hyb _ hb).2 (rgt s)
      have h5 : wd (fun l : κ => w (inrE l)) (yb (lft s)) (rgt s) = c s := by
        have : col c (lft s) (rgt s) = c s := by
          show c (uni (lft s) (rgt s)) = c s
          rw [e s]
        rw [← this]
        exact h4
      rw [h5]
      simp
    · rw [hy0 _ hb, hcC s (by rw [eC s]; push_cast; omega)]
      simp
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_at {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_act {ι S E : Type} [LinearOrder ι] [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (u : ι → S) (f : Finset ι → S) (m : E) (t : Finset ι) :
    wd (fun i => act (u i)) (fun t => act (f t) m) t =
      act (wd (fun i => Algebra.lmul ℂ S (u i)) f t) m := by

  rw [wd_at, wd_at, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul, Module.End.mul_apply]

private lemma wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (g : E →ₗ[ℂ] E) (b : Finset ι → E) (t : Finset ι) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun t => g (b t)) t = g (deltaL ℂ ι E b t) := by
  rw [wd_at]
  change _ = g (∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i))

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul]

private lemma lft_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    lft (uni b L) = b := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

private lemma rgt_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    rgt (uni b L) = L := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

private lemma uni_lr (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (s : Finset (β ⊕ₗ κ)) :
    uni (lft s) (rgt s) = s := (h β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

private lemma mj_uni (h : WdUni) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S)
    (b : Finset (Fin (d + 1)) → E) (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    T.mj p θ b (uni (uni I J) L) = T.act (θ (uni I L)) (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
  simp only [Sys.mj, lft_uni' h, rgt_uni' h, map_zsmul]

theorem UpperTheory.Gal.productCup_of_system.mJ_of :
    WdUni → MJ := by
  intro h d S E _ _ _ _ T κ _ _ z p θ b hθ hb hJ
  funext s
  obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
    ⟨lft (lft s), rgt (lft s), rgt s, by rw [uni_lr h, uni_lr h]⟩
  have hw2 : ∀ l : κ, T.wt z (inrE l) = T.act (z l) := fun _ => rfl
  have hw3 : ∀ i : Fin (d + 1), T.wt z (inlE (inlE i)) = 1 := fun _ => rfl
  have hw4 : ∀ i : Fin (d + 1), T.wt z (inlE (inrE i)) = 1 := fun _ => rfl
  have e1 := (h (Two d) κ E (T.wt z) (T.mj p θ b) (uni I J) L).1
  have e2 := (h (Fin (d + 1)) (Fin (d + 1)) E (fun i => T.wt z (inlE i))
    (fun b' => T.mj p θ b (uni b' L)) I J).1
  have e3 := (h (Fin (d + 1)) κ S (fun t => Algebra.lmul ℂ S (app (fun _ => 1) z t)) θ I L).1
  rw [hθ] at e3
  have hcard : (uni I J).card = I.card + J.card := (h _ _ ℂ (fun _ => 0) (fun _ => 0) I J).2.2.2.1
  set P : S := wd (fun i => Algebra.lmul ℂ S (1 : S)) (fun b' => θ (uni b' L)) I with hP
  set Q : S := wd (fun l => Algebra.lmul ℂ S (z l)) (fun L' => θ (uni I L')) L with hQ
  have hPQ : P + ((-1 : ℤ) ^ I.card) • Q = 0 := e3.symm

  have tA : wd (fun i => T.wt z (inlE (inlE i))) (fun b' => T.mj p θ b (uni (uni b' J) L)) I =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
    rw [hP, ← wd_act]
    simp only [mj_uni h, hw3, map_one]

  have tB : wd (fun j => T.wt z (inlE (inrE j))) (fun J' => T.mj p θ b (uni (uni I J') L)) J = 0 := by
    have : (fun J' => T.mj p θ b (uni (uni I J') L)) = fun J' =>
        (((-1 : ℤ) ^ ((p + 1) * L.card)) • T.act (θ (uni I L))) (b J') := by
      funext J'
      simp only [mj_uni h, map_zsmul, LinearMap.smul_apply]
    simp only [this, hw4]
    rw [wd_one, hb]
    simp

  have tC : wd (fun l => T.wt z (inrE l)) (fun L' => T.mj p θ b (uni (uni I J) L')) L =
      T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [hQ, ← wd_act, wd_at, wd_at]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hc : (L.erase l).card + 1 = L.card := Finset.card_erase_add_one hl
    have hs : ((-1 : ℤ) ^ ((p + 1) * (L.erase l).card)) = (-1 : ℤ) ^ ((p + 1) * (L.card + 1)) := by
      rw [← hc, show (p + 1) * ((L.erase l).card + 1 + 1) = (p + 1) * (L.erase l).card + 2 * (p + 1) by ring,
        pow_add, pow_mul]
      simp
    rw [mj_uni h, hs, hw2]
  have main : wd (T.wt z) (T.mj p θ b) (uni (uni I J) L) =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) +
        ((-1 : ℤ) ^ (I.card + J.card)) • T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [e1, e2, hcard, tA, tB, tC]
    simp
  rw [main]
  change _ = (0 : E)
  by_cases hJc : J.card = p + 1
  · have hsgn : ((-1 : ℤ) ^ (I.card + J.card)) * ((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) =
        ((-1 : ℤ) ^ I.card) * ((-1 : ℤ) ^ ((p + 1) * L.card)) := by
      rw [hJc, pow_add, show (p + 1) * (L.card + 1) = (p + 1) * L.card + (p + 1) by ring, pow_add]
      have : ((-1 : ℤ) ^ (p + 1)) * ((-1 : ℤ) ^ (p + 1)) = 1 := by
        rw [← mul_pow]; simp
      linear_combination ((-1 : ℤ) ^ I.card * (-1 : ℤ) ^ ((p + 1) * L.card)) * this
    have hPQ' : T.act P + ((-1 : ℤ) ^ I.card) • T.act Q = 0 := by
      rw [← map_zsmul, ← map_add (f := _), hPQ, map_zero]
    have := congrArg (fun f : Module.End ℂ E => f (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J)) hPQ'
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at this
    simp only [map_zsmul, smul_smul] at this ⊢
    rw [hsgn]
    simpa [smul_smul, mul_comm] using this
  · rw [hJ J hJc]
    simp
end
