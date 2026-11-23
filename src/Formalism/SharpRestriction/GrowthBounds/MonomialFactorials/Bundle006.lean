module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001
public import Lemmata.GeneralBFactLeftTerForm.Imports
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

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Map

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (ι : ℚ_[p] →+* KK O)

theorem map_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (map ι F) =
      map ι (Formalism.GM.M.glAct p (gmL LL) j c d F) := by

  simp only [glAct, Formalism.GM.M.glAct, gmL, LinearMap.sum_apply, map_sum, Set.mem_setOf_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j <;> by_cases h2 : LL.vec i = true <;> simp [h1, h2, pderiv_map]

theorem gm_ycond_stable {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt, Formalism.GM.M.glAct p LL j c d x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt := by
  intro x hx
  have key : Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      (Formalism.GM.M.YCond p (r := r) LL j Mt).comap (Formalism.GM.M.glAct p LL j c d) := by
    conv_lhs => unfold Formalism.GM.M.YCond
    refine sSup_le fun S hS y hy => ?_
    rw [Submodule.mem_comap]
    unfold Formalism.GM.M.YCond
    exact le_sSup hS (hS.2 c d y hy)
  exact key hx

theorem gm_ycond_supp {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((Formalism.GM.M.wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem map_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (F : MvPolynomial σ ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] s) : map ι F ∈ restrictSupport (KK O) s := by
  rw [mem_restrictSupport_iff] at hF ⊢
  exact (Finset.coe_subset.2 (support_map_subset ι F)).trans hF

theorem map_ycond {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt) :
    map ι y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  have hsupp : Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_restrictSupport ι z (gm_ycond_supp (gmL LL) j Mt hz)
  have hstab : chStable (KK O) (r := r) LL j
      (Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))) := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨_, gm_ycond_stable (gmL LL) j Mt c d z hz, (map_glAct ι LL j c d z).symm⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | smul k a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ k ha
  have hy' : map ι y ∈ Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  unfold Formalism.MainNotions.G.YCond
  exact le_sSup (show _ ∈ {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} from ⟨hsupp, hstab⟩) hy'

theorem map_Y {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.Y p (r := r) (gmL LL) J M) :
    map ι y ∈ Yjt (KK O) (r := r) LL J M := by
  rw [Formalism.GM.M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun k => map_ycond ι LL (J k) (M k) y (hy.2 k)⟩
  exact map_mem_restrictSupport ι y hy.1

variable {ι}

theorem map_int {σ : Type} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ) : map ι F ∈ IntPol O σ := by
  obtain ⟨G, rfl⟩ := hF
  induction G using MvPolynomial.induction_on' with
  | monomial m a =>
    obtain ⟨y, hy⟩ := hint a
    refine ⟨monomial m y, ?_⟩
    simp [hy]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem ha hb

theorem map_YZ {N r : ℕ} [NeZero r] (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YZ p (r := r) (gmL LL) J M) :
    map ι y ∈ YjtZ O (r := r) LL J M := by
  rw [Formalism.GM.M.YZ, Submodule.mem_inf] at hy
  have h2 : y ∈ Submodule.restrictScalars ℤ_[p] (Formalism.GM.M.Pol p r (gmL LL)) ⊓ Formalism.GM.M.IntPol p (Fin N × Fin r) := hy.2
  exact Submodule.mem_inf.2 ⟨map_Y ι LL J M y hy.1, map_int hint y (Submodule.mem_inf.1 h2).2⟩

theorem map_XiPolZ {N r t b : ℕ} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (g : MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]) (hg : g ∈ Formalism.GM.M.XiPolZ p N r t b) :
    map ι g ∈ XiPolZ O N r t b := by
  have hg' := Submodule.mem_inf.1 hg
  exact Submodule.mem_inf.2 ⟨map_mem_restrictSupport ι g hg'.1, map_int hint g hg'.2⟩

end Map

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem rank_le {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) (dl : DCl X)
    (hc : Compat C0 CE1 CE2 X dl aTop) :
    clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl ≤ mCl C0 CE1 CE2 X dl aTop := by
  have hIn := realise hH aTop aPlus hT hP
  have hm0 : 0 ≤ X.m := hH.2.2.2.2.2.2.2.2.1
  have hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) := hH.2.2.2.2.2.2.2.2.2
  have h := h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2
  rw [rankOnDigits_eq, realW_top, realW_plus] at h
  exact (h hc).2

theorem mem_cbox {dl : DCl X} {aTop : Fin X.s → ℕ} :
    aTop ∈ cbox C0 CE1 CE2 X dl ↔
      aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem clSum_levels (dl : DCl X) (aTop : Fin X.s → ℕ) (f : SegBlock X.s X.r → Lv C0 CE1 CE2 X → ℕ) :
    ((clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, f b x) aTop dl : ℕ) : ℝ) =
      ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (f z.1 z.2 : ℝ) := by
  rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
  unfold idx keptSet
  rw [Finset.sum_sigma]
  push_cast
  rfl

theorem claim2 {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hDir : RestDir C0 CE1 CE2 X) (hW : X.winA.Nonempty)
    (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) ≤ (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
  obtain ⟨aPlus, hP⟩ := hW
  obtain ⟨hT, hc⟩ := mem_cbox.1 ha
  rw [← clSum_levels dl aTop (fun b x => rL C0 CE1 CE2 X aTop b x)]
  have h1 : clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x) aTop dl ≤
      clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl := by
    rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop), clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
    refine Finset.sum_le_sum fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b :=
      (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop).mem_toFinset.1 (Finset.mem_filter.1 hb).1
    exact hDir aTop hT aPlus hP b hk
  exact_mod_cast h1.trans (rank_le hH h11 aTop aPlus hT hP dl hc)

theorem digit_class_dimension_comparison_of_remaining_estimates {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (CM : ℝ) (hCM : 0 ≤ CM)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hPlus : RestPlus C0 CE1 CE2 X CM) (hTM : RestTM C0 CE1 CE2 X CM) (hDir : RestDir C0 CE1 CE2 X)
    (hFree : RestFree C0 CE1 CE2 X) (hRat : RestRatio C0 CE1 CE2 X) :
    DigitClassDimensionComparison C0 CE1 CE2 X (fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
      ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) := by
  classical
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  intro dl hdl
  have hbox : (CountingStatementReduction.box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1) = cbox C0 CE1 CE2 X dl ×ˢ X.winA := by
    ext a
    simp only [CountingStatementReduction.box, Finset.mem_filter, Finset.mem_product, mem_cbox]
    tauto
  rw [hbox, Finset.sum_product, Finset.sum_product]
  have hR : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ _aPlus ∈ X.winA, (mCl C0 CE1 CE2 X dl aTop : ℝ) =
      (X.winA.card : ℝ) * ∑ aTop ∈ cbox C0 CE1 CE2 X dl, (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hR]
  by_cases hW : X.winA.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hW
    simp [hW]
  by_cases hA : (cbox C0 CE1 CE2 X dl).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [hA]
  obtain ⟨a0, ha0⟩ := hA
  have hL : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA,
        ((clSum C0 CE1 CE2 X (fun b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋) aTop dl : ℕ) : ℝ) =
      ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ∑ z ∈ idx C0 CE1 CE2 X dl a0,
        (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    refine Finset.sum_congr rfl fun aTop ha => Finset.sum_congr rfl fun aPlus _ => ?_
    rw [← hFree dl hdl aTop ha a0 ha0]
    exact clSum_levels dl aTop (fun b x => bLvl C0 CE1 CE2 X aTop aPlus b x ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
  rw [hL]
  have key := assemble (cbox C0 CE1 CE2 X dl) X.winA (idx C0 CE1 CE2 X dl a0)
    (Finset.univ : Finset (Fin (X.S C0 CE1 CE2).t))
    (fun aTop aPlus z => (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun aTop z => (bY C0 CE1 CE2 X aTop z.1 z.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun z => (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ))
    (fun aTop z => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ))
    (fun aTop i => upd C0 CE1 CE2 X dl aTop i)
    (fun aTop => (mCl C0 CE1 CE2 X dl aTop : ℝ))
    ((30 + CM) / X.L.Y) (5 / X.L.Y) (Real.exp 3) (by positivity) (by positivity) (fun z => Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fin] at key
    exact key
  · intro aTop ha z hz
    have h := hPlus dl hdl aTop ha z (by rw [hFree dl hdl aTop ha a0 ha0]; exact hz)
    have e : (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) =
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ) *
          (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ) := by
      unfold rL
      push_cast
      rfl
    rw [e] at h
    exact h
  · intro z hz
    exact hTM dl hdl a0 ha0 z hz
  · intro aTop ha
    have h := claim2 hH h11 hDir hW dl aTop ha
    rw [hFree dl hdl aTop ha a0 ha0] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold rL
    push_cast
    rfl
  · intro aTop ha i _
    exact hRat dl hdl aTop ha i

def RestAll (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X ∧
      RestFree C0 CE1 CE2 X ∧ RestRatio C0 CE1 CE2 X ∧ RestDepth C0 CE1 CE2 X CM C

theorem segment_weighted_counting_bound_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) (hCM : 0 ≤ CM)
    (hC : 2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hR : RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X) : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH _
  obtain ⟨hBlk, hPlus, hTM, hDir, hFree, hRat, hD0, hDep⟩ := hR hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  refine ⟨fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋,
    (30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y, by positivity, ?_, ?_,
    digit_class_dimension_comparison_of_remaining_estimates CM hCM hH h11 hPlus hTM hDir hFree hRat⟩
  · have e1 : 2 * ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) * Real.exp 3 =
        2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3 / X.L.Y := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_right _ hY0.le
    have h1 : (30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 ≤
        ((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by
      have : 0 ≤ (30 + CM) * Real.exp 3 := by positivity
      nlinarith
    have h2 : 0 ≤ (30 + CM) * Real.exp 3 + 5 := by positivity
    calc 2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3
        ≤ 2 * (((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1)) * Real.exp 3 := by
          apply mul_le_mul_of_nonneg_right _ he.le
          linarith
      _ = (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by ring
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := mul_le_mul_of_nonneg_right hC (by linarith)
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by
          have : 0 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) :=
            mul_nonneg (le_trans (by positivity) hC) (by linarith)
          nlinarith
  · intro aTop hT aPlus hP b hk
    have h0 : (0 : ℤ) ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.2 (mul_nonneg hY0.le hD0)
    obtain ⟨L₂, hg, hr⟩ := hBlk aTop hT aPlus hP b hk _ h0
    refine ⟨L₂, GoodSub_mono ?_ hg, hr⟩
    have := Int.floor_le (X.L.Y * D1r C0 CE1 CE2 X CM)
    linarith

def RestAllE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM C : ℝ, 0 ≤ CM ∧ 1 ≤ C ∧
    2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X

theorem rest1DAE_of (D : Formalism.BasicNotions.D7) (h : RestAllE D) : DigitClassRemainingUniform D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 Ckap Cs => by
    obtain ⟨CM, C, hCM, hC1, hC, h2⟩ := h1 Ckap Cs
    exact ⟨C, hC1, fun X hA =>
      segment_weighted_counting_bound_of_all_remaining_bounds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X hCM hC hA.2.2.2.2.2.2 (h2 X hA)⟩) h

theorem theorem_A_closed_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (h : RestAllE D) : IntegralityFromMetricForLargeConstants D :=
  counting_statement_uniform_of_digit_class D (rest1DAE_of D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section RankSpanGen

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem span_den_gen (M : Submodule R V) (y : V) (hy : y ∈ Submodule.span K (M : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ M := by
  first | exact Bl.general_b_fact_left_ter_form.goal1 .. | (apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y hy | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V | exact @Bl.general_b_fact_left_ter_form.goal1 R K | exact @Bl.general_b_fact_left_ter_form.goal1 R

def toSpanG (M : Submodule R V) : M →ₗ[R] (Submodule.span K (M : Set V)) where
  toFun x := ⟨x.1, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance toSpanG_loc (M : Submodule R V) : IsLocalizedModule (nonZeroDivisors R) (toSpanG (K := K) M) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro x
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hxK : algebraMap R K x ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hx0
    rw [Module.End.isUnit_iff]
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul K (x : R) y, ← algebraMap_smul K (x : R) z] at hyz
      exact smul_right_injective _ hxK hyz
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hxK, one_smul]
  · intro y
    obtain ⟨s, hs, hsy⟩ := span_den_gen (K := K) M y.1 y.2
    exact ⟨(⟨s • y.1, hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), rfl⟩
  · intro x₁ x₂ h
    refine ⟨1, ?_⟩
    have : x₁ = x₂ := Subtype.ext (congrArg (fun z : Submodule.span K (M : Set V) => (z : V)) h)
    rw [this]

theorem finrank_eq_span_gen (M : Submodule R V) :
    Module.finrank R M = Module.finrank K (Submodule.span K (M : Set V)) := by
  unfold Module.finrank
  rw [IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl]
  rw [(IsLocalizedModule.rank_eq (nonZeroDivisors R) le_rfl (toSpanG (K := K) M)).symm]

end RankSpanGen

def RestYbc : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ),
    ∀ y ∈ YjtZ O (r := r) LL J M,
      y ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.YZ p (r := r) (gmL LL) J M : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
