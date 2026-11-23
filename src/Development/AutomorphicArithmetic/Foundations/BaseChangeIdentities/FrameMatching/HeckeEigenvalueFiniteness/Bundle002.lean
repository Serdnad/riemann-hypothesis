module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle527
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.Bundle001
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hk_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (c : ℂ) (e : GL ι F → ℂ) (v : V) :
    PositivityTheory.Rg.BcN.F2.hk ρ K (fun g => c * e g) v = c • PositivityTheory.Rg.BcN.F2.hk ρ K e v := by
  unfold PositivityTheory.Rg.BcN.F2.hk
  rw [smul_finsum]
  exact finsum_congr fun q => mul_smul _ _ _

theorem UpperTheory.HeckeLevelFrameExistence.locE :
    UpperTheory.HeckeLevelFrameExistence.LocE := by
  intro E _ _ _ n w hw K' hKo hKle hlev σ hσ k D
  have hUL : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hKc : IsCompact (K' : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K' hKo) hKle
  obtain ⟨P, T, hT, hcomp, hdict⟩ := GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ
  have hd := hdict (K'.subgroupOf (UL n w)) hlev
  rw [hmap] at hd
  obtain ⟨y₀, hy₀, hy₀0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ) :=
    ⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩
  have hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0 :=
    ⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩
  have hchoice : PositivityTheory.Rg.BcB.F.Choice.ChoiceS :=
    PositivityTheory.Rg.BcB.F.Choice.choiceS_of
      (fun E _ _ _ n w => GlobalTheory.T.isolate_representation_at_character (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_subquotients (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n))
  obtain ⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩ :=
    hchoice E n w K' hKo hKc P hP0 k D
  set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr
  have hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g) :=
    ⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by
      simp only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩
  have hH := (hd _ hIk').1
  refine ⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩
  · have hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w)) := by
      rintro ⟨x, hx⟩
      apply T.injective
      have h1 := hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      rw [map_smul, hT, T.apply_symm_apply]
      simpa using h1
    refine ⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩
    · have h0 : T.symm v₀ = 0 := congrArg Subtype.val h
      have h1 : v₀ = 0 := T.symm.map_eq_zero_iff.1 h0
      rw [h1, map_zero] at hl1
      exact zero_ne_one hl1
    · apply Subtype.ext
      rw [(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]
      apply T.injective
      have h2 := ((hd e₀ hIk).2 _ hy).2
      rw [T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul] at h2
      rw [h2, T.apply_symm_apply]
  · intro j τ hs hne v hv
    rw [hk_const_mul, hkill j τ hs hne v hv, smul_zero]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem mok0 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) : MLM.MOk F₀.d₀ := by
  have h0 : ∀ w, w ∉ F₀.d₀.T := fun w => by rw [F₀.T₀]; exact Finset.notMem_empty w
  have hlev : ∀ w ∈ F₀.d₀.Bad, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (F₀.d₀.KB w) := fun w hw => by
    have h := F₀.levFam.1 w
    have e : F₀.d₀.KU w = F₀.d₀.KB w :=
      (if_neg (h0 w)).trans ((if_neg fun h' => Finset.disjoint_left.1 F₀.ok₀.disj.2.2 h' hw).trans (if_pos hw))
    rwa [e] at h
  refine ⟨fun w hw => absurd hw (h0 w), fun w hw => ⟨(F₀.S₀ w hw).2, fun g => ?_, F₀.K'_lev w hw⟩,
    fun w hw hs => ⟨hlev w hw, fun a ha => ?_⟩, fun w hw hs => ⟨F₀.kB w, F₀.kB_pos w hw hs, hlev w hw, fun γ => ?_, fun a ha => ?_⟩⟩
  · unfold UL
    rw [if_pos (F₀.S₀ w hw).2]
    exact Subgroup.mem_top g
  · rw [F₀.fix_def a ha w, if_pos hw, if_pos hs]
  · have e : {γ : UL n w | γ.1 ∈ MB.congK n w (F₀.kB w)} =
        (((GlobalTheory.PrincCong.congSub w n (F₀.kB w)).subgroupOf (UL n w) : Subgroup (UL n w)) : Set (UL n w)) :=
      Set.ext fun x => (GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) x.1).symm
    rw [F₀.KB_def w, if_pos hw, if_neg hs, e, Subgroup.closure_eq]
    exact GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) γ.1
  · rw [F₀.fix_def a ha w, if_pos hw, if_neg hs]

end UpperTheory.HeckeLevelFrameExistence

end
end
