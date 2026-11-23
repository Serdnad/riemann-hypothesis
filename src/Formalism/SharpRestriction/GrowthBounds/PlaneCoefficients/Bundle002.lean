module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Block

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def BlockDeg (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : Prop :=
  ∀ x : TL J nL r, ∑ c, rho (x, c) + lowP Fr p x * (dPl x + dNo x) = dd (posOf n' (posTL Fr x))

theorem blockDeg_of (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (mo : TV n' (m + 1) →₀ ℕ) (h1 : InLow Fr p hk nL rho mo) (h2 : InBlock Fr p hk nL dPl dNo mo)
    (h3 : ∀ t, ∑ c, mo (t, c) = dd t) : BlockDeg Fr p nL dd rho dPl dNo := by
  intro x
  rw [← h3, ← h2.1 x, ← h2.2 x]
  have e : ∑ c : Fin (m + 1), mo (posOf n' (posTL Fr x), c) =
      ∑ c : Fin (r + K), mo (posOf n' (posTL Fr x), Fin.cast hk.symm c) :=
    (Fintype.sum_equiv (finCongr hk.symm) _ _ (fun c => rfl)).symm
  rw [e, Fin.sum_univ_add, Fin.sum_univ_add]
  simp_rw [← h1.1 x, ← h1.2 x]
  have hA : ∑ a, mo (plVar Fr hk nL x a) = ∑ a, mo (plVar Fr hk nL x a) % lowP Fr p x +
      ∑ a, lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  have hB : ∑ b, mo (noVar Fr hk nL x b) = ∑ b, mo (noVar Fr hk nL x b) % lowP Fr p x +
      ∑ b, lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  change _ = ∑ a, mo (plVar Fr hk nL x a) + ∑ b, mo (noVar Fr hk nL x b)
  rw [hA, hB, mul_add, Finset.mul_sum, Finset.mul_sum]
  ring

end Block

def MemAtB (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (dd : Fin n' → ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ), BlockDeg Fr p Dt.nL dd rho dPl dNo →
    ∀ (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

section MemLin

variable (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (dd : Fin n' → ℕ)

def memSubB : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O)) where
  carrier := {F | MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F}
  add_mem' := by
    intro F G hF hG J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_add, oneT_add, planeCoeff_add]
    exact XX_add Dt (hF J Dt dPl dNo ka hT rho hb e he nu) (hG J Dt dPl dNo ka hT rho hb e he nu)
  zero_mem' := by
    intro J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_zero, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt
  smul_mem' := by
    intro c F hF J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_smul, oneT_smul, planeCoeff_smul]
    exact XX_smul Dt c (hF J Dt dPl dNo ka hT rho hb e he nu)

theorem memAtG_of_B (F : MvPolynomial (TV n' (m + 1)) (KK O)) (hdeg : ∀ mo ∈ F.support, ∀ t, ∑ c, mo (t, c) = dd t)
    (h : MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  by_cases hb : BlockDeg Fr p Dt.nL dd rho dPl dNo
  · exact h J Dt dPl dNo ka hT rho hb e he nu
  · have h0 : levImg Fr p hk Dt.nL rho dPl dNo F = 0 := by
      unfold levImg
      apply Finset.sum_eq_zero
      intro mo hmo
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hmo
      exact absurd (blockDeg_of Fr p hk Dt.nL dd rho dPl dNo mo h2 h3 (hdeg mo h1)) hb
    rw [h0, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt

end MemLin

def topDeg {n' k : ℕ} (ga : TV n' k →₀ ℕ) (t : Fin n') : ℕ := ∑ c, ga (t, c)

theorem castV_inj {n' m r K : ℕ} (hk : m + 1 = r + K) : Function.Injective (castV (n' := n') hk) := by
  intro u v huv
  have h1 : (castV hk u).1 = (castV hk v).1 := congrArg Prod.fst huv
  have h2 : (castV hk u).2 = (castV hk v).2 := congrArg Prod.snd huv
  exact Prod.ext h1 (Fin.cast_injective hk.symm h2)

theorem topDeg_castV {n' m r K : ℕ} (hk : m + 1 = r + K) (b : Fin n' × Fin (r + K) →₀ ℕ) (t : Fin n') :
    topDeg (b.mapDomain (castV hk)) t = ∑ c, b (t, c) := by
  unfold topDeg
  have hinj := castV_inj (n' := n') hk
  rw [← Fintype.sum_equiv (finCongr hk.symm) (fun c => (b.mapDomain (castV hk)) (t, Fin.cast hk.symm c)) _
    (fun c => rfl)]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finsupp.mapDomain_apply_of_injective hinj b (t, c)

def PlanePairsOnBlocksAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ (E' : Fin n' → ℕ) (xs : ℤ → SegRing O r K),
      (∀ i : ℕ, i < F.J → xs i ∈ pairSet O r K F (i : ℤ)
        (g2mg p n' r K F (flatDeg lam0) (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x)
          (cPrime n' r TT.card c0 cpp cStar)) Y (i : ℤ)) (g2th p n' F (flatDeg lam0) (i : ℤ))) →
    ∀ l : Fin n' × Fin (r + K) →₀ ℕ, IsLabel p F l →
    ∀ ga ∈ (SPR O p F hrk (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)).support,
      MemAtB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
        (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t) (symG p O hk F l ga xs)

theorem rest5aMonoStep_of_B (C CLa : ℝ) (h : PlanePairsOnBlocksAt C CLa) : Lemma5aMonomialAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD b ga hga
  have hGen := hD.2.2.2.1.choose_spec.2 b
  set E' := hD.2.2.2.1.choose with hE'
  obtain ⟨xs, hxs, l, hl, hB, hdeg⟩ := hGen
  have e1 : MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (B b) * monomial ga 1) =
      symG p O hk F l ga xs := by rw [hB]; rfl
  apply memAtG_of_B 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)
  · intro mo hmo t
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ hmo
    obtain ⟨d, hd, g, hg, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ h1)
    have hg' := MvPolynomial.support_monomial_subset hg
    rw [Finset.mem_singleton] at hg'
    subst hg'
    have hd' := hd
    rw [MvPolynomial.support_rename_of_injective (castV_inj hk)] at hd'
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hd'
    have h2 : ∑ c, b' (t, c) = G2d F (flatDeg lam0) E' t :=
      ((MvPolynomial.mem_restrictSupport_iff O).1 hdeg) hb' t
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    rw [← h2, ← topDeg_castV hk b' t]
    rfl
  rw [e1]
  let mS : ℕ := mStar p F (r + K) (orbitWindowCount r de h' x) (p ^ goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar)
  let Sj : ℤ → Set (SegRing O r K) := fun jj =>
    pairSet O r K F jj (g2mg p n' r K F (flatDeg lam0) mS Y jj) (g2th p n' F (flatDeg lam0) jj)
  have hspan : ∀ i : ℕ, i < F.J → xs i ∈ Submodule.span O (Sj i) := fun i _ =>
    symbol_spaces_le_pair_span CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h' x) (2 * TT.card)) mS a Y (i : ℤ) (hxs i)
  exact symG_span p O hk F (memSubB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)) Sj l ga
    (fun xs' hxs' => h p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
      E' xs' hxs' l hl ga hga)
    xs hspan

def PlanePairsOnBlocks (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PlanePairsOnBlocksAt C CLa

theorem rest5aMono_of_B (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : PlanePairsOnBlocks D CLa Ck Crk Cdeg) :
    Lemma5aMonomial D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h2⟩ := h hA
  exact ⟨C₁, h1, fun C hC => rest5aMonoStep_of_B C CLa (h2 C hC)⟩

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem sum_ite_mem {α β : Type*} [DecidableEq α] (f : β → α) (T : Finset α) (l : List β) :
    (l.map fun z => if f z ∈ T then (2 : ℝ) else 0).sum =
      2 * ∑ s ∈ T, ((l.filter fun z => f z = s).length : ℝ) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have e : ∀ s, (((y :: l).filter fun z => f z = s).length : ℝ) =
        ((l.filter fun z => f z = s).length : ℝ) + if f y = s then 1 else 0 := by
      intro s
      by_cases h : f y = s
      · simp [h]
      · simp [h]
    simp only [List.map_cons, List.sum_cons, ih, e, Finset.sum_add_distrib, Finset.sum_ite_eq]
    split_ifs <;> ring

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

theorem llPos_mem (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hl)]
  exact (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem _)

theorem mem_LLset (j x : ℤ) : x ∈ Fr.LLset j ↔
    (Fr.fr (j - 1) (r - 1) < x ∧ x < Fr.fr j 0) ∧ posOf n' x ∈ Fr.TT := by
  unfold Frames.LLset
  simp only [Finset.mem_filter, Finset.mem_Ioo]

variable {Fr} {L₁ N₁ : ℕ}

theorem LL_sub_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j y : ℤ) (hy : y ∈ Fr.LLset j) :
    y ∈ Fr.letters j ∧ ¬ Fr.IsW j y := by
  have h := (mem_LLset Fr _ _).1 hy
  have h1 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
  have h2 := frame_row_monotone Fr L₁ N₁ hV j (r - 1) (by omega)
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, h.2⟩
  · unfold Frames.IsW
    omega

theorem posU_mem (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr (Fr.LLset j).card j u) := by
  unfold posU
  split_ifs with h
  · exact LL_sub_letters hV hr j _ (llPos_mem Fr j u h)
  · have hi : u - (Fr.LLset j).card < r := by omega
    have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    have h2 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
    have h3 := frame_row_monotone Fr L₁ N₁ hV j _ hi
    have h4 := frame_entry_le_last Fr L₁ N₁ hV j _ hi
    refine ⟨?_, ?_⟩
    · unfold Frames.letters
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, h4⟩, (hV.2.2.2.2.1 j _ hi).1⟩
    · unfold Frames.IsW
      omega

theorem Bo_ge (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (G : ℕ) (j x : ℤ) (hG : Fr.fr j (r - 1) - Fr.fr (j - 1) 0 ≤ G)
    (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) :
    a / (p : ℝ) ^ G ≤ Bo p Fr deg j x := by
  have hy := oldest_mem_segment_letters Fr L₁ N₁ hV hr j x hx hW
  unfold Frames.letters at hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hy
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  unfold Bo levDeg
  apply div_le_div₀ (Nat.cast_nonneg _) (hdeg _ hy.2) (by positivity)
  apply pow_le_pow_right₀ hp'
  unfold Frames.dist
  omega

theorem wordLoss_le {k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (c0 : ℕ)
    (hc : ∀ s, (l.filter fun z => z.1 = s).length ≤ c0) (jz : ℤ) (u : ℕ) :
    wordLoss Fr l jz u ≤ 2 * ((Fr.letters jz).card : ℝ) * c0 := by
  set T : Finset (Fin n') := (Fr.letters jz).image (posOf n') with hT
  have h1 : wordLoss Fr l jz u ≤ (l.map fun z => if z.1 ∈ T then (2 : ℝ) else 0).sum := by
    unfold wordLoss
    apply List.sum_le_sum
    intro z _
    unfold opCost
    by_cases ht : touchT Fr jz u z.1
    · obtain ⟨x, hx, hxs, _⟩ := ht
      have hm : z.1 ∈ T := by
        rw [hT]
        exact Finset.mem_image.2 ⟨x, hx, hxs⟩
      rw [if_pos ⟨x, hx, hxs, by assumption⟩, if_pos hm]
    · rw [if_neg ht]
      split_ifs <;> norm_num
  have h2 := sum_ite_mem (fun z : Fin n' × (Fin k × Fin k) => z.1) T l
  have h3 : ∑ s ∈ T, ((l.filter fun z => z.1 = s).length : ℝ) ≤ ∑ _s ∈ T, (c0 : ℝ) := by
    apply Finset.sum_le_sum
    intro s _
    exact_mod_cast hc s
  have h4 : (T.card : ℝ) ≤ ((Fr.letters jz).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h5 : (T.card : ℝ) * c0 ≤ ((Fr.letters jz).card : ℝ) * c0 :=
    mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
  rw [h2] at h1
  nlinarith

end Geo

theorem size_arith (C k r N Q cS c0 e Y N1 : ℝ) (hC : 16 ≤ C) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 0 ≤ cS) (hc0 : 0 ≤ c0) (he : 0 ≤ e) (hY : 0 ≤ Y) (hN1 : 0 ≤ N1) (hN1' : N1 ≤ r * N) :
    16 * N1 * c0 * (Y * k ^ 2) * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + e)) * Y := by
  have a1 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
  have a2 : Q ≤ Q ^ 5 := le_self_pow₀ hQ (by norm_num)
  have a3 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr
  have a4 : N1 * c0 ≤ cS + (r * N * c0 + e) := by
    have := mul_le_mul_of_nonneg_right hN1' hc0
    linarith
  have b1 : 16 * k ^ 2 ≤ C * k ^ 3 := mul_le_mul hC a1 (by positivity) (by linarith)
  have b2 : 16 * k ^ 2 ≤ C * k ^ 3 * r ^ 2 := le_trans b1 (le_mul_of_one_le_right (by positivity) a3)
  have b3 : 16 * k ^ 2 ≤ C * k ^ 3 * r ^ 2 * N := le_trans b2 (le_mul_of_one_le_right (by positivity) hN)
  have b4 : 16 * k ^ 2 * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := mul_le_mul b3 a2 (by linarith) (by positivity)
  have b5 : 16 * k ^ 2 * Q * (N1 * c0) ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + e)) :=
    mul_le_mul b4 a4 (by positivity) (by positivity)
  have b6 := mul_le_mul_of_nonneg_right b5 hY
  calc 16 * N1 * c0 * (Y * k ^ 2) * Q = 16 * k ^ 2 * Q * (N1 * c0) * Y := by ring
    _ ≤ _ := b6

theorem wordBoundStep (C CLa : ℝ) (hC : 16 ≤ C) : WordBoundStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD l _ hc jz u hu
  obtain ⟨_, H, hF, _⟩ := hD
  have hB := hyps_basic (by linarith : (1 : ℝ) ≤ C) H
  obtain ⟨h1, h2, _, h4, h5, h6, _, _, _, _, _, h12⟩ := H
  obtain ⟨hTT, hV, hG, _⟩ := hF
  have hr1 : 1 ≤ r := by omega
  have ha0 : (0 : ℝ) ≤ a := by linarith [hB.two_le_a]
  obtain ⟨hx, hW⟩ := posU_mem hV hr1 jz u hu
  set xx := posU F (F.LLset jz).card jz u with hxx

  have hw := wordLoss_le (Fr := F) l c0 hc jz u
  have hcard : ((F.letters jz).card : ℝ) ≤ (orbitWindowCount r de h x : ℝ) := by exact_mod_cast hV.2.2.2.2.2.2.2.1 jz
  have hw2 : wordLoss F l jz u ≤ 2 * (orbitWindowCount r de h x : ℝ) * c0 := by
    have := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg c0 : (0 : ℝ) ≤ c0)
    linarith

  have hdeg : ∀ s ∈ F.TT, a ≤ (flatDeg lam0 s : ℝ) := by
    intro s hs
    rw [hTT] at hs
    exact (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs).1
  have hBo := Bo_ge hV hr1 p (by omega) (flatDeg lam0) a hdeg (goodG' r de h x) jz xx (le_of_lt (hG jz)) hx hW

  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hNN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hY0 : (0 : ℝ) < Y := by linarith [hB.two_le_Y]
  have hN1 : ((orbitWindowCount r de h x : ℕ) : ℝ) ≤ (r : ℝ) * TT.card := by
    have : orbitWindowCount r de h x ≤ r * TT.card := le_trans (Nat.le_self_pow (by norm_num) _) h4
    exact_mod_cast this
  have hs := size_arith C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x) cStar c0 (2 * r * n' * cpp) Y
    (orbitWindowCount r de h x : ℝ) hC hk1 hrr hNN hQ1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hY0.le
    (Nat.cast_nonneg _) hN1
  have hsa := le_trans hs h12
  have hkk : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hden : 0 < Y * ((r + K : ℕ) : ℝ) ^ 2 := by rw [hkk]; positivity
  have hQ0 : 0 < (p : ℝ) ^ goodG' r de h x := by linarith
  have hfl : ((16 * orbitWindowCount r de h x * c0 : ℕ) : ℤ) ≤ sl p F (flatDeg lam0) Y (r + K) jz xx := by
    unfold sl
    rw [Int.le_floor, le_div_iff₀ hden]
    refine le_trans ?_ hBo
    rw [le_div_iff₀ hQ0, hkk]
    push_cast
    push_cast at hsa
    linarith
  have hfl' : ((16 * orbitWindowCount r de h x * c0 : ℕ) : ℝ) ≤ (sl p F (flatDeg lam0) Y (r + K) jz xx : ℝ) := by
    exact_mod_cast hfl
  push_cast at hfl'
  linarith

theorem restWordBound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestWordBound D CLa Ck Crk Cdeg :=
  fun _ => ⟨16, by norm_num, fun C hC => wordBoundStep C CLa hC⟩

end Formalism.MainNotions.PairMembershipBlocks
end
end
