module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle150
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle148
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BadEx2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle001
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

namespace PositivityTheory.Rg.BcN.F2.Final

open PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem hkAlg : HkAlg F ι := GlobalTheory.T.hecke_algebra_structure F ι
theorem prodFinLen : ProdFinLen F ι := GlobalTheory.T.finite_length_of_products F ι
theorem subOfNonNil' : SubOfNonNil' F ι :=
  GlobalTheory.T.subquotient_of_non_nilpotent_variant F ι

end PositivityTheory.Rg.BcN.F2.Final
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Loc0 (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n) : Prop where
  hSec : IsSection Sec
  inert : ∀ w, ¬ IsSplitAt w → w ∈ Sec
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  S_le : ∀ w ∈ S, IsSplitAt w → w ∈ d₀.S₀
  bad : ∀ w ∈ d₀.Bad, w ∈ Sec ∧ (¬ IsSplitAt w → ¬ IsUnramU π w)
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → IsUnramU π w ∧ μ.UnrAt w
  levFam : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) d₀.KU
  level : ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ d₀.KU w) → HasLevel Sec π K'
  fix : ∀ a ≤ n, ∀ w ∈ d₀.Bad, Match n a (n - a) w (μ.loc w) (U.lone (d₀.KB w)) (d₀.fix a w)
  mok₀ : MLM.MOk d₀
  off : ∀ w, w ∉ d₀.Bad → d₀.KB w = KL n w ∧ ∀ a, d₀.fix a w = 0

theorem isLevel_KL (w : Pl E) {K : Subgroup (UL n w)} (h : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) K) :
    GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨Subgroup.isOpen_mono h.2.1 h.1, le_rfl, fun _ hk => hk⟩

theorem local_existence_of_unramified (hSec : SecEx) (hU : UnifEx) (hLev : LevelEx) (hS : SplitEx) (hB : BadEx2) (hE : GlobalTheory.BCT.Unr E)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hun : ∀ᶠ w : Pl E in cofinite, IsUnramU π w) (S : Finset (Pl E))
    (hS1 : S.card ≤ 1) (μ : HChar E) (hin : ∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) (hae : ∀ᶠ w : Pl E in cofinite, μ.UnrAt w)
    (hop : ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)) : ∃ Sec d₀, Loc0 π S μ Sec d₀ := by
  set S₀ := S.filter IsSplitAt with hS₀
  obtain ⟨Sec, hsec, hS₀S, hinS⟩ := hSec E S₀ ((Finset.card_filter_le _ _).trans hS1)
  have hfin : {w : Pl E | ¬ (IsUnramU π w ∧ μ.UnrAt w)}.Finite := Filter.eventually_cofinite.1 (hun.and hae)
  set Bad := (hfin.toFinset.filter (· ∈ Sec)) \ S₀ with hBad
  have memBad : ∀ w, w ∈ Bad ↔ (¬ (IsUnramU π w ∧ μ.UnrAt w) ∧ w ∈ Sec) ∧ w ∉ S₀ := fun w => by
    simp only [hBad, Finset.mem_sdiff, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  obtain ⟨K₀, m, -, hm, hfam, hgood, hcong, hlev⟩ := hLev E n π hπ Sec hsec (S₀ ∪ Bad) 1
  choose ϖ hϖ using hU E hE
  have h1 : ∀ w : Pl E, ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ)
      (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)), w ∈ S₀ →
      K'.subgroupOf (UL n w) = K₀ w ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w (n := n) ∧
      (∀ k ∈ KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w (n := n)) ∧ (∀ k ∈ KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ.loc w (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1 := fun w => by
    by_cases hw : w ∈ S₀
    · obtain ⟨K', X, e, L, h⟩ := hS E n w (Finset.mem_filter.1 hw).2 (μ.loc w) (hop w) m hm (K₀ w)
        (hcong w (Or.inr (Finset.mem_union_left _ hw)))
      exact ⟨K', X, e, L, fun _ => h⟩
    · exact ⟨⊥, ∅, 0, fun _ => ⊥, fun h => absurd h hw⟩
  choose K' X e LS hSp using h1
  let fx : ∀ (a : ℕ) (w : Pl E), LF a (n - a) w := fun a w => fixFn n a w (μ.loc w) m (K₀ w)
  have h2 : ∀ (a : ℕ) (w : Pl E), ∃ L : Subgroup (GLw a w × GLw (n - a) w), a ≤ n → w ∈ Bad →
      IsPairLevel L ∧ IsHecke L (fx a w) ∧ Match n a (n - a) w (μ.loc w) (U.lone (K₀ w)) (fx a w) := fun a w => by
    by_cases hw : a ≤ n ∧ w ∈ Bad
    · obtain ⟨L, h⟩ := hB E hE n a hw.1 w (μ.loc w) (hop w) m hm (K₀ w) (hcong w (Or.inr (Finset.mem_union_right _ hw.2)))
      exact ⟨L, fun _ _ => h⟩
    · exact ⟨⊥, fun h h' => absurd ⟨h, h'⟩ hw⟩
  choose LB hBd using h2
  let d : LocData E n := ⟨∅, S₀, Bad, fun w => μ.loc w, ϖ, 0, K', X, e, fun a w => if w ∈ S₀ then LS w a else LB a w,
    fun a w => if w ∈ Bad then fx a w else 0, fun _ => 1, fun w => if w ∈ Bad then K₀ w else KL n w⟩
  have dK : ∀ w ∈ Bad, d.KB w = K₀ w := fun w hw => if_pos hw
  have dF : ∀ a, ∀ w ∈ Bad, d.fix a w = fx a w := fun a w hw => if_pos hw
  have hKU : ∀ w, d.KU w = if w ∈ S₀ ∪ Bad then K₀ w else KL n w := fun w => by
    show (if w ∈ (∅ : Finset (Pl E)) then _ else if w ∈ S₀ then (K' w).subgroupOf (UL n w) else if w ∈ Bad then (if w ∈ Bad then K₀ w else KL n w) else KL n w) = _
    by_cases a1 : w ∈ S₀
    · simp [a1, (hSp w a1).1]
    · by_cases a2 : w ∈ Bad <;> simp [a1, a2]
  have hgd : ∀ w ∈ Sec, w ∉ S₀ → w ∉ Bad → IsUnramU π w ∧ μ.UnrAt w := fun w a1 a2 a3 => by
    by_contra h
    exact a3 ((memBad w).2 ⟨⟨h, a1⟩, a2⟩)
  refine ⟨Sec, d, hsec, hinS, ⟨⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Finset.disjoint_sdiff⟩,
    fun w => (hϖ w).1.1, fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun a ha w hw => ?_,
    fun a ha w hw y hy => ?_, fun a ha w hw => ?_⟩, rfl, fun _ => rfl, hϖ,
    fun w hw => ⟨hS₀S w hw, (Finset.mem_filter.1 hw).2⟩, fun w hw hs => Finset.mem_filter.2 ⟨hw, hs⟩,
    fun w hw => ⟨((memBad w).1 hw).1.2, fun hs hu => ((memBad w).1 hw).1.1 ⟨hu, hin w hs⟩⟩, hgd, ⟨fun w => ?_, ?_⟩,
    fun K'' hK'' => ?_, fun a ha w hw => by rw [dK w hw, dF a w hw]; exact (hBd a w ha hw).2.2,
    ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun w hw hs => ⟨by rw [dK w hw]; exact hfam.1 w, fun a ha => ?_⟩,
      fun w hw hs => ⟨m, hm, by rw [dK w hw]; exact hfam.1 w, fun γ => ?_, fun a ha => ?_⟩⟩,
    fun w hw => ⟨if_neg hw, fun a => if_neg hw⟩⟩
  · obtain ⟨-, b1, b2, b3, b4, b5, b6, -⟩ := hSp w hw
    exact ⟨b1, b2, b3, b4, b5, b6⟩
  · show IsPairLevel (if w ∈ S₀ then LS w a else LB a w)
    by_cases a1 : w ∈ S₀
    · rw [if_pos a1]; exact ((hSp w a1).2.2.2.2.2.2.2 a ha).1
    · rw [if_neg a1]; exact (hBd a w ha ((Finset.mem_union.1 hw).resolve_left a1)).1
  · have hy' : y ∈ (if w ∈ S₀ then LS w a else LB a w) := hy
    rw [if_pos (show w ∈ S₀ from hw)] at hy'
    exact ((hSp w hw).2.2.2.2.2.2.2 a ha).2 y hy'
  · rw [dF a w hw]
    show IsHecke (if w ∈ S₀ then LS w a else LB a w) (fx a w)
    rw [if_neg ((memBad w).1 hw).2]
    exact (hBd a w ha hw).2.1
  · rw [hKU]
    split_ifs
    · exact hfam.1 w
    · exact isLevel_KL w (hfam.1 w)
  · filter_upwards [(S₀ ∪ Bad).eventually_cofinite_notMem] with w hw
    rw [hKU, if_neg hw]
  · obtain ⟨φ, a1, a2, a3⟩ := hlev (fun w => if w ∈ Sec then K'' w else K₀ w) fun w => by
      split_ifs with hw
      · refine (hK'' w).trans ?_
        rw [hKU]
        split_ifs with hR
        · exact le_rfl
        · rw [Finset.mem_union, not_or] at hR
          rw [hgood w (hgd w hw hR.1 hR.2).1 (by rw [Finset.mem_union, not_or]; exact hR)]
      · exact le_rfl
    exact ⟨φ, a1, a2, fun w hw x hx hk => a3 w hw x hx (by simpa only [if_pos hw] using hk)⟩
  · have hs : IsSplitAt w := (Finset.mem_filter.1 hw).2
    refine ⟨hs, fun g => by simp [UL, hs], ?_⟩
    show GlobalTheory.BCT.IsLevel _ _ ((K' w).subgroupOf (UL n w))
    rw [(hSp w hw).1]
    exact hfam.1 w
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_pos hs]
  · rw [dK w hw]
    exact hcong w (Or.inr (Finset.mem_union_right _ hw)) γ
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_neg hs]

end PositivityTheory.Rg.BcB.F.Ex0

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)

def MatchBadIOf2 : Prop := M2 → LponeIdem → MatchBadI

theorem matchBadIOf2 : MatchBadIOf2 := by
  intro h2 hI E _ _ _ hU w hw n a b k hab hk K' hK hmem m
  rw [hI E n w K' hK m]
  have hM := h2 E hU w hw n a b k hab hk
  have hf : lone K' = fun γ => ((K'.relIndex (KL n w) : ℕ) : ℂ) *
      (({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)).indicator 1 γ) := by
    funext γ
    rw [mb_lone_apply]
    by_cases h : γ ∈ K'
    · have h' : γ ∈ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := (hmem γ).1 h
      rw [if_pos h, Set.indicator_of_mem h', Pi.one_apply, mul_one]
    · have h' : γ ∉ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := fun h' => h ((hmem γ).2 h')
      simp [h, h']
  rw [hf]
  have hM' : Match n a b w 1 ({γ : UL n w | γ.1 ∈ congK n w k}.indicator 1) (pairIndicatorMatch n a b w k) := by
    convert hM using 2
    · rfl
    · unfold pairIndicatorMatch congK
      congr 1
      split_ifs <;> rfl
  exact mb_match_smul _ hM'

end PositivityTheory.Rg.BcB.F.MB

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

def LevIdem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (d : LocData E n) (a : ℕ),
  a ≤ n → IsSection S → d.Ok → (↑d.P : Set (Pl E)) ⊆ S →
  (IsOpen (lev₁ S d a : Set (GL (Fin a) (Af E))) ∧ IsCompact (lev₁ S d a : Set (GL (Fin a) (Af E)))) ∧
  (IsOpen (lev₂ S d a : Set (GL (Fin (n - a)) (Af E))) ∧ IsCompact (lev₂ S d a : Set (GL (Fin (n - a)) (Af E)))) ∧
  (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = levSet S d a ∧
  ∀ (ν : Measure (Hf E a (n - a))), ν.IsHaarMeasure → ∃ cK : ℂ,
    cK * (ν.real (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) : ℂ) = 1 ∧
    ∀ (x y : ∀ w : d.P, d.kap w) (h : Hf E a (n - a)),
      ((ν.real ((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : ℝ) : ℂ)⁻¹ *
          finFn S ((d.eL a).ent d.P x y) (d.eL a).t h =
        if x = y ∧ h ∈ ((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) then cK else 0

end PositivityTheory.Rg.BcB.F

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem cand_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} {F₀ : Frame0 hR π S} {d} {i} {s₁ s₂ Pa Pb D} (c : F₀.Cand d i s₁ s₂ Pa Pb D) :
    (∀ τ, ∑ j, Pa.m j τ = mOf (F₀.A i).χa τ) ∧ (∀ τ, ∑ j, Pb.m j τ = mOf (F₀.A i).χb τ) := by
  obtain ⟨G, hG, h0, -⟩ := c.vec
  have h := PairNe_holds _ _ _ _ _ G hG h0
  exact ⟨fun τ => lemD _ _ s₁ Pa τ _ c.ctx.g₁ c.ctx.u₁ c.ctx.t₁ (c.inf₁ τ) h.1,
    fun τ => lemD _ _ s₂ Pb τ _ c.ctx.g₂ c.ctx.u₂ c.ctx.t₂ (c.inf₂ τ) h.2⟩

end PositivityTheory.Rg.BcB.F.LemDd

end
end
