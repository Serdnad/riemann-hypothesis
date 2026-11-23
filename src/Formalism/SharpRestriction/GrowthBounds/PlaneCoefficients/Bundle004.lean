module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundJoint
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TouchCOfMem
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle001
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

theorem geoTop : GeoTop := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL s hs
  have hr : 1 ≤ r := NeZero.pos r
  obtain ⟨x0, hx0⟩ := posTL_surj Fr hV hr hJ hnL s hs
  refine ⟨x0, hx0, fun x' hx' => ?_⟩
  exact posTL_inj Fr hV hr hJ hnL (hx'.trans hx0.symm)

theorem geoTouch : GeoTouch := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL x0 j u hu hx
  have hr : 1 ≤ r := NeZero.pos r
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL]; exact hu
  unfold touchT
  rcases hx with (⟨l, hl, hlt⟩ | ⟨m, hm, hlt⟩) | ⟨m, hm⟩
  · subst hl
    have hl' : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL]; exact l.isLt
    refine ⟨llPos Fr (segZ j) l.val, (LL_sub_letters hV hr _ _ (llPos_mem Fr (segZ j) l.val hl')).1, rfl, ?_⟩
    rw [← posU_ll (Fr := Fr) (segZ j) l.val hl']
    exact (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 (by omega)
  · subst hm
    have hm' := m.isLt
    refine ⟨Fr.fr (segZ j) (r - 1 - m.val), fr_mem_letters hV hr _ _ (by omega), rfl, ?_⟩
    rw [← posU_fr (Fr := Fr) (segZ j) (r - 1 - m.val)]
    refine (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 ?_
    rw [← hnL]
    omega
  · subst hm
    have hm' := m.isLt
    obtain ⟨s, hs, hsh⟩ := DdG.shift Fr hV.2.1 hJ (j - 1)
    rw [sub_add_cancel] at hsh
    refine ⟨Fr.fr (segZ j - 1) (r - 1 - m.val), w_mem_letters hV hr _ _ (by omega), ?_,
      (w_lt_posU hV hr _ _ _ (by omega) hu').le⟩
    show _ = posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - m.val))
    rw [(hsh (r - 1 - m.val)).1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · rw [DdG.posOf_add_n]

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  [NeZero r] (Dt : SignedChainData p O r J)

theorem twoPow_pos (j : ZMod J) (m : Fin r) : 0 < Dt.P j m := pow_pos (Nat.Prime.pos Fact.out) _

theorem XXg_zeroP (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) :
    XXg Dt d th thL 0 := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j mm _ => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]; exact geZ_top _
  · rw [valS_zero_eq_top]; exact geZ_top _

private theorem touchC_of_liftVar_mem_chainML (x0 : TL J Dt.nL r) (a : Fin r) (j : ZMod J) (i : Fin (Dt.nch j))
    (h : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i) : touchC Dt x0 j i := by
  obtain ⟨j', y⟩ := x0
  obtain ⟨z, hz, hzz⟩ := h
  rcases y with l | m <;> rcases z with l' | m'
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1
    cases h2
    exact Or.inl ⟨l', rfl, hz⟩
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1 h2
    exact Or.inr ⟨m', rfl⟩

theorem plDer' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d' x0 = d x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = true → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = true → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (pderiv (x0, a) H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_pderiv x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, c3, rho1, rho2, hc2, hF⟩ := Fdig_der_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho1 H)))) (th j i) := by
      by_cases hc : c2 = 0
      · rw [hc, zero_smul, valS_zero_eq_top]
        exact geZ_top _
      have hv : Dt.trueLet.vec x0 = true := hc2 hc
      refine geZ_mono (valS_smul_ge _ _ _ _) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) ?_)
      · intro _
        rw [modelLet_vec]
        exact hv
      by_cases hs : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho1 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hs) hv)
      · exact geZ_anti (t1 j i)
          (geZ_mono (valS_pderiv_of _ _ _ _ (fun h => absurd h hs)) (hC rho1 j i))
    have e3 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c3 • pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = true
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_pderiv_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min (geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)) e3)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = true
    · exact valuation_ge_of_le_add_one (valS_pderiv _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_pderiv_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

theorem plMul' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d x0 = d' x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = false → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = false → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (X (x0, a) * H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_X_mul x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, rho1, rho2, hF⟩ := Fdig_mul_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = false
      · exact valuation_ge_of_le_add_one (valS_X_mul _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = false
    · exact valuation_ge_of_le_add_one (valS_X_mul _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_X_mul_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

end Formalism.MainNotions.PairMembershipBlocks

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem plDer : PlDer := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  exact plDer' Dt x0 a d (Function.update d x0 (d x0 + 1)) (by simp)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plMul : PlMul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD hd H hH
  exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) (by simp; omega)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plEul : PlEul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  rcases Nat.eq_zero_or_pos (d x0) with hz | hpos
  · have hvars : (x0, a) ∉ H.vars := by
      intro hv
      obtain ⟨m, hm, hma⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hv
      have hdeg := (mem_Pol'.1 hH.1) m hm x0
      rw [hz] at hdeg
      have hle : m (x0, a) ≤ multideg m x0 :=
        Finset.single_le_sum (f := fun c => m (x0, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hdeg] at hle
      exact (Finsupp.mem_support_iff.1 hma) (by omega)
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hvars, mul_zero]
    exact XXg_zeroP Dt d th thL
  · have e0 : d x0 = Function.update d x0 (d x0 - 1) x0 + 1 := by simp; omega
    have e1 : ∀ i, i ≠ x0 → Function.update d x0 (d x0 - 1) i = d i :=
      fun i hi => by simp [Function.update_of_ne hi]
    have e1' : ∀ i, i ≠ x0 → d i = Function.update d x0 (d x0 - 1) i :=
      fun i hi => (e1 i hi).symm
    cases hv : Dt.trueLet.vec x0
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th' th' thL' thL'
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) _ hD1
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th thL thL
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) _ hD1

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem det_mem_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => h _ _) _

theorem X_mem_supp {R σ : Type*} [CommRing R] (s : Set σ) (i : σ) (hi : i ∈ s) :
    (X i : MvPolynomial σ R) ∈ supported R s := by
  rw [supported_eq_adjoin_X]
  exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hi)

theorem pmat_det_mem (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ)
    (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
  apply det_mem_sub
  intro l i
  unfold pmat
  rw [Matrix.of_apply]
  exact Subalgebra.pow_mem _ (X_mem_supp {v : TV n' k | v.2.val < r ∧ Even v.1.val} (A l, Fin.castLE hrk i)
    (show (Fin.castLE hrk i).val < r ∧ Even (A l).val from ⟨i.isLt, hA l⟩)) _

theorem restSP : RestSP := by
  intro p n' r k _ R _ F hrk c' Q L₁ N₁ hV hn hr ga hga v hv
  have hfr : ∀ (j : ℤ) (l : Fin r), Even (posOf n' (F.fr j l.val)).val := fun j l =>
    (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have hAr : ∀ (s : ℤ) (l : Fin r), Even (posOf n' (Arow F s l.val)).val := fun s l =>
    (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  have hmem : SPR R p F hrk c' Q ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
    unfold SPR
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _)
      (Subalgebra.prod_mem _ fun j _ => ?_)) (Subalgebra.prod_mem _ fun s _ => ?_)
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hAr _)) _
  have hvars : v ∈ (SPR R p F hrk c' Q).vars :=
    (mem_vars_iff_mem_support v).2 ⟨ga, hga, Finsupp.mem_support_iff.2 hv⟩
  exact (mem_supported.1 hmem) (Finset.mem_coe.2 hvars)

end Formalism.MainNotions.PairMembershipBlocks
end
end
