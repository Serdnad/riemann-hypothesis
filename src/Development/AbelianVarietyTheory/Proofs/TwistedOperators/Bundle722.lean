module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle697
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle699
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle719
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle701
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle717
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inBasis_congr {D : D7} {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    {x y : GL (Fin n) (Lev.EAf D)} (e : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y) : inBasis h β w x = inBasis h β w y := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, e]

theorem mem_jacGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (hσ : D.R.m - 1 - j = 2 * σ),
    1 ≤ σ → ∀ (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ jacGrp (rowJac ch.G j hj' σ hσ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j σ hi hj hj' hσ h1 r g hr hg
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, hc⟩, hsupp, hloc⟩ := hr
  obtain ⟨h, hh1, hh2, hr⟩ := GlobalTheory.T.exists_prod_single_place_pieces_of_suppAt _ _ es hes hc r hsupp
  rw [hr]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨q, hqe, -, hqpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w.1 (es w.1) (hes w.1 w.2) s.hF
  have hF := ch.S.row t (Set.mem_univ t) w.1 w.2 j hj'
  have e1 : GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) (h w)) =
      GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) r) := Units.ext (hh2 w)
  have hm : toFrame one_le_sLen hj' (g w) ∈ symR (Kw w.1) _ _ := hg w
  rw [← hloc w] at hm
  refine GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric (ch.G.rowDec j hj') hσ h1 w.1 _ _ _ hF (fun p => frameScal_ne w.1 _ _ p) (topRank_eq ch.G t w.1 hj)
    (rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩)
    (by have := topRank_add (G := locGrid ch.G t w.1) one_le_sLen j; have hm' : (locGrid ch.G t w.1).m = D.R.m := rfl; rw [hm'] at this; omega)
    q (fun x => (hqpr x).trans rfl) (h w) (hqe ▸ hh1 w) ?_
  rw [inBasis_congr _ _ _ e1]
  exact hm

end GlobalTheory.RowLift
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CellVanishing

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]

def extPt (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) : ∀ i, H i :=
  fun i => if hp : p i then g ⟨i, hp⟩ else h₀ i

lemma extPt_update (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p)
    (x : H j.1) : extPt p h₀ (Function.update g j x) = Function.update (extPt p h₀ g) j.1 x := by
  funext i
  by_cases hi : i = j.1
  · subst hi
    simp [extPt, j.2]
  · have hne : ∀ hp : p i, (⟨i, hp⟩ : Subtype p) ≠ j := fun hp h => hi (by rw [← h])
    rw [Function.update_of_ne hi]
    unfold extPt
    split_ifs with hp
    · rw [Function.update_of_ne (hne hp)]
    · rfl

lemma extPt_at (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p) :
    extPt p h₀ g j.1 = g j := by
  simp [extPt, j.2]

lemma niter_sub (p : ι → Prop) [DecidablePred p] {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i))
    (μ : ∀ i, Measure (H i)) (f : (∀ i, H i) → ℂ) (h₀ : ∀ i, H i) :
    ∀ (l : List (Subtype p)) (g : ∀ j : Subtype p, H j.1) (z : ℂ),
      NIter (R := fun j : Subtype p => R j.1) (fun j => ρ j.1) (fun j => μ j.1) (fun g => f (extPt p h₀ g)) l g z →
      NIter ρ μ f (l.map Subtype.val) (extPt p h₀ g) z := by
  intro l
  induction l with
  | nil =>
    intro g z hz
    simpa [NIter] using hz
  | cons j l ih =>
    intro g z hz
    simp only [List.map_cons, NIter.eq_2] at hz ⊢
    obtain ⟨F, hF, hF'⟩ := hz
    refine ⟨F, hF, fun x => ?_⟩
    rw [← extPt_update]
    exact ih _ _ (hF' x)

end GlobalTheory.CellVanishing

namespace GlobalTheory.RowVal


open GlobalTheory.CellVanishing in
theorem cellVan_holds : CellVan := by
  intro ι _ H _ _ _ _ _ _ _ _ A B R K l hl hS ρ μ ρ' μ' hM X S b w q z α hw hdist hinv hsupp hz hrel
  haveI := Classical.decEq (∀ i, H i)
  have hQ := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι H R ρ μ l 1).1 (Fin 2) Finset.univ α z q (fun n _ => hz n)
  refine GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish ι H A B R K l hl hS ρ μ ρ' μ' hM
    ((S 0).image (b 0) ∪ (S 1).image (b 1)) (fun g => ∑ n ∈ Finset.univ, α n * q n g) _ ?_ ?_ ?_ hQ ?_
  · intro c hc i
    rcases Finset.mem_union.1 hc with hc | hc <;>
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨_, hb, _⟩ := hw _ β hβ
      exact hb i
  · intro i hi h
    constructor
    · intro r hr
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).1 r hr]
    · intro k hk
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).2 k hk]
  · intro h h1 hne
    obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨β, hβ, hc⟩ := hsupp n h h1 (right_ne_zero_of_mul hn)
    refine ⟨b n β, ?_, hc⟩
    fin_cases n
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hβ)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hβ)
  · intro a ha ha1
    let p : ι → Prop := fun i => i ∈ l
    haveI : ∀ j : Subtype p, LocallyCompactSpace (B j.1) := fun j =>
      (hS j.1 j.2).clB.isClosedEmbedding_subtypeVal.locallyCompactSpace

    haveI : ∀ n (β : X n) i, Decidable (b n β i ∈ B i) := fun _ _ _ => Classical.dec _
    let bb : ∀ n, X n → ∀ i, B i := fun n β i => if h : b n β i ∈ B i then ⟨b n β i, h⟩ else 1
    have hbb : ∀ n β (hβ : β ∈ S n), bb n β = fun i => ⟨b n β i, (hw n β hβ).2.1 i⟩ := by
      intro n β hβ
      funext i
      exact dif_pos _
    let qn : Fin 2 → (∀ j : Subtype p, B j.1) → ℂ := fun n g => q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1
    have hg1 : ∀ (g : ∀ j : Subtype p, B j.1) i, i ∉ l → a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1 = 1 := by
      intro g i hi
      simp [extPt, p, hi, ha1 i hi]
    have hmeas : ∀ j ∈ l.attach, IsClosed (((R j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsCompact (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsOpen (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧ (ρ' j.1).IsHaarMeasure ∧
        (ρ' j.1).IsInvInvariant ∧ (μ' j.1).IsHaarMeasure ∧ (μ' j.1).IsMulRightInvariant := by
      intro j _
      have hs := hS j.1 j.2
      obtain ⟨-, -, h3, h4⟩ := hM j.1 j.2
      exact ⟨hs.clR.preimage continuous_subtype_val, hs.clB.isClosedEmbedding_subtypeVal.isCompact_preimage hs.cpt,
        hs.opn, h3, hs.uniRB _ h3, h4, hs.uniB _ h4⟩
    have hcell : ∀ n, NIter (R := fun j : Subtype p => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1) (fun j => μ' j.1)
        (qn n) l.attach 1 (∑ β ∈ S n, w n β * q n (a * b n β)) := by
      intro n
      have hv : ∀ β (hβ : β ∈ S n) i, ((bb n β i : B i) : H i) = b n β i := fun β hβ i => by rw [hbb n β hβ]
      have key := GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1))
        (fun j => (K j.1).subgroupOf (B j.1)) l.attach (List.nodup_attach.2 hl) (fun j => ρ' j.1) (fun j => μ' j.1) hmeas
        (X n) (S n) (fun β j => bb n β j.1) (qn n) (fun β _ j hj => absurd (List.mem_attach l j) hj) ?_ ?_ ?_
      · convert key using 1
        refine Finset.sum_congr rfl fun β hβ => ?_
        obtain ⟨h1, hb, hwβ⟩ := hw n β hβ
        rw [hwβ, hbb n β hβ]
        congr 1
        · exact congrArg List.prod (List.attach_map_val (f := fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩)).symm
        · show q n (a * b n β) = q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (fun j => (⟨b n β j.1, hb j.1⟩ : B j.1)) i).1
          congr 1
          funext i
          by_cases hi : i ∈ l
          · simp [extPt, p, hi]
          · simp [extPt, p, hi, ha1 i hi, h1 i hi]
      · intro β hβ β' hβ' hc
        apply hdist n β hβ β' hβ'
        intro i hi
        obtain ⟨r, hr, a0, ha0, k, hk, e⟩ := hc ⟨i, hi⟩ (List.mem_attach _ _)
        rw [Subgroup.mem_bot] at ha0
        subst ha0
        refine ⟨r.1, Subgroup.mem_subgroupOf.1 hr, 1, (A i).one_mem, k.1, Subgroup.mem_subgroupOf.1 hk, ?_⟩
        have e' := congrArg Subtype.val e
        dsimp only at e'
        simp only [Subgroup.coe_mul, OneMemClass.coe_one, mul_one] at e'
        rw [hv β' hβ', hv β hβ] at e'
        rw [mul_one]
        exact e'
      · intro j _ g
        have hgj : ∀ x : B j.1, (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (Function.update g j x) i).1) =
            Function.update (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1) j.1 (a j.1 * x.1) := by
          intro x
          rw [extPt_update]
          funext i
          by_cases hi : i = j.1
          · subst hi; simp
          · simp [Function.update_of_ne hi]
        have hj1 : (extPt (H := fun i => ↥(B i)) p 1 g j.1) = g j := extPt_at _ _ _ _
        constructor
        · intro r hr
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).1 r.1
            (Subgroup.mem_subgroupOf.1 hr)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (r * g j).1 = r.1 * (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) := by
            rw [hj1, Subgroup.coe_mul, ← mul_assoc, ← mul_assoc, (hS j.1 j.2).comm _ (ha j.1) _ r.2]
          rw [hx]
          exact this
        · intro k hk
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).2 k.1
            (Subgroup.mem_subgroupOf.1 hk)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (g j * k).1 = (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) * k.1 := by
            rw [hj1, Subgroup.coe_mul, mul_assoc]
          rw [hx]
          exact this
      · intro g _ hne
        obtain ⟨β, hβ, hc⟩ := hsupp n _ (hg1 g) hne
        refine ⟨β, hβ, fun j _ => ?_⟩
        obtain ⟨r, hr, a', ha', k, hk, e⟩ := hc j.1 j.2
        have hs := hS j.1 j.2
        have hbB : b n β j.1 ∈ B j.1 := (hw n β hβ).2.1 j.1
        have hkB : k ∈ B j.1 := hs.le hk
        have hgB : (g j).1 ∈ B j.1 := (g j).2
        dsimp only at e
        rw [extPt_at] at e
        obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = (g j).1 * k⁻¹ * (b n β j.1)⁻¹ := ⟨_, rfl⟩
        have hr₀B : r₀ ∈ B j.1 := hr₀ ▸ mul_mem (mul_mem hgB (inv_mem hkB)) (inv_mem hbB)
        have hrr : r = (a j.1 * a'⁻¹) * r₀ := by
          have hc' : a'⁻¹ * r₀ = r₀ * a'⁻¹ := hs.comm _ (inv_mem ha') _ hr₀B
          calc r = (r * a' * b n β j.1 * k) * k⁻¹ * (b n β j.1)⁻¹ * a'⁻¹ := by group
            _ = a j.1 * r₀ * a'⁻¹ := by rw [← e, hr₀]; group
            _ = a j.1 * (a'⁻¹ * r₀) := by rw [hc']; group
            _ = (a j.1 * a'⁻¹) * r₀ := by group
        have hr₀R : r₀ ∈ R j.1 := (hs.split _ (mul_mem (ha j.1) (inv_mem ha')) _ hr₀B (by rw [← hrr]; exact hr)).2
        refine ⟨⟨r₀, hr₀B⟩, Subgroup.mem_subgroupOf.2 hr₀R, 1, Subgroup.one_mem _, ⟨k, hkB⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
        apply Subtype.ext
        show (g j).1 = r₀ * 1 * (bb n β j.1).1 * k
        rw [hv β hβ, hr₀]
        group
    have hlin := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1)
      (fun j => μ' j.1) l.attach 1).1 (Fin 2) Finset.univ α (fun n => ∑ β ∈ S n, w n β * q n (a * b n β)) qn
      (fun n _ => hcell n)
    rw [hrel a ha ha1] at hlin
    have ht := niter_sub p ρ' μ' (fun bb : ∀ i, B i => ∑ n ∈ Finset.univ, α n * q n fun i => a i * (bb i).1) 1 l.attach 1 0 hlin
    have e1 : extPt p (1 : ∀ i, B i) (1 : ∀ j : Subtype p, B j.1) = 1 := by
      funext i; simp [extPt]
    rw [e1, List.attach_map_subtype_val] at ht
    exact ht

end GlobalTheory.RowVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.latticeVacuumCombination_localModel : Big fun ch => LatP ch → CombP ch := by
  first | exact @GlobalTheory.FlatPlace.eventually_combination_of_lattice | exact GlobalTheory.FlatPlace.eventually_combination_of_lattice | (intros; apply GlobalTheory.FlatPlace.eventually_combination_of_lattice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.arrowLocalModel_movedFrames : Big fun ch => LatP ch → ChrP ch → ArrP ch := by
  first | exact @GlobalTheory.ArrowModel.arrow_model | exact GlobalTheory.ArrowModel.arrow_model | (intros; apply GlobalTheory.ArrowModel.arrow_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  first | exact @GlobalTheory.LastStepOne.first_step_flat | exact GlobalTheory.LastStepOne.first_step_flat | (intros; apply GlobalTheory.LastStepOne.first_step_flat <;> assumption)
end
