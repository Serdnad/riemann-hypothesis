module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle345
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle298
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import GroundTheory.GlobalFields.KummerTheory.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.SplittingFromInequality.Galois
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqChar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gramAt_conjTranspose (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  have h : (HSpace.gram V)ᴴ = HSpace.gram V := by
    funext i j
    exact V.herm.eq (V.frame j) (V.frame i)
  rw [gramAt, ← Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ), h]

end GlobalTheory.SepPer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjGroup

theorem congr_red_mem_unipSym : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → K2cong (II D) g e0 z0 bw x → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  intro D g e0 f0 z0 bw bwd ew hF β PP w hβ hL x M hx hM hSt hc
  have hred := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  have hLf : ∀ v, v ∈ (II D).Lf → v ∈ Formalism.L2.Herm.hatL (F := ↥D.host.F) (E := D.host.E) (II D).L := by
    intro v hv
    have e := Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L
    exact (Set.ext_iff.mp e v).mp hv
  have hint : ∀ i : Fin D.R.k, ew ∈ IntAf (II D).F (II D).E ∧ sigA (II D) ew ∈ IntAf (II D).F (II D).E := by
    intro i
    obtain ⟨t, ht, he⟩ := hF.dual i i
    obtain ⟨t', ht', he'⟩ := Formalism.L2.SG.Pf.BunEx.Unip.Zsym (hF.dual i i)
    simp only [if_pos (Eq.refl i), ↓reduceIte] at he he'
    have h1 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).2 (hF.mem.2.2 i).1
    have h2 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).1 (hF.mem.2.2 i).2
    have hg : ((g : (II D).E ⊗[(II D).F] Af (II D).F)) ∈ IntAf (II D).F (II D).E := natCast_mem _ g
    constructor
    · have e1 : ew = hA (II D) (bwd i) (bw i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t := by
        rw [← he]; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h1 (mul_mem hg ht)
    · have e1 : sigA (II D) ew = hA (II D) (bw i) (bwd i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t' := by
        rw [← he']; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h2 (mul_mem hg ht')
  cases w
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 (fun i => bwd (Fin.rev i)) bw β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).1, ?_⟩
      have hi : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).1
      have hs := hred.2.1 ⟨ew, hi⟩ (bw i) (hLf _ (hF.mem.2.2 i).1)
      have h0 := hL.2.1 hi
      simp only [Bool.false_eq_true, if_false] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bw_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hb := GlobalTheory.T.unipotentLevel_moves_dualVector_upper (II D) g e0 f0 z0 bw bwd ew hF x hx hc (Fin.rev i)
      have hsub : Set.range e0 ∪ bwd '' {l | Fin.rev i < l} ⊆
          Set.range e0 ∪ Set.range bw ∪ (fun j => bwd (Fin.rev j)) '' {j | j.1 < i.1} := by
        rintro v (hv | ⟨l, hl, rfl⟩)
        · exact Or.inl (Or.inl hv)
        · refine Or.inr ⟨Fin.rev l, ?_, by simp⟩
          have hl' : (Fin.rev i).1 < l.1 := hl
          simp only [Fin.val_rev] at hl'
          show (Fin.rev l).1 < i.1
          simp only [Fin.val_rev]; omega
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hb
    · intro b
      rw [← hM]
      have hf := Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b
      have hsub : Set.range e0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ∪ f0 '' {c | b < c} ⊆
          Set.range e0 ∪ {z0} ∪ Set.range (fun j => bwd (Fin.rev j)) ∪ Set.range bw ∪ f0 '' {c | b < c} := by
        rintro v ((((hv | hv) | hv) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
        · exact Or.inl (Or.inr hv)
        · obtain ⟨j, rfl⟩ := hv
          exact Or.inl (Or.inl (Or.inr ⟨Fin.rev j, by simp⟩))
        · exact Or.inr hv
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hf
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 bw bwd β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).2, ?_⟩
      have hi : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).2
      have hs := hred.2.1 ⟨sigA (II D) ew, hi⟩ (bwd i) (hLf _ (hF.mem.2.2 i).2)
      have h0 := hL.2.2.1 hi
      simp only [if_true] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bwd_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hsub : Set.range e0 ∪ bw '' {j | j.1 < i.1} ⊆ Set.range e0 ∪ Set.range bwd ∪ bw '' {j | j.1 < i.1} :=
        Set.union_subset_union_left _ Set.subset_union_left
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub (hc.2.2 i)
    · intro b
      rw [← hM]
      exact Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b

end GlobalTheory.SeeConjGroup
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SplitAway

open GroundTheory.Global Filter

theorem splitsCompletely_of_tower {K E M : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
    {u : HeightOneSpectrum (𝓞 K)} (h : SplitsCompletely M u) : SplitsCompletely E u := by
  intro w hw
  obtain ⟨W⟩ := GroundTheory.Global.nonempty_placesOver M w
  have h1 : W.1.asIdeal.LiesOver w.asIdeal := W.2
  have h2 : W.1.asIdeal.LiesOver u.asIdeal := Ideal.LiesOver.trans W.1.asIdeal w.asIdeal u.asIdeal
  obtain ⟨he, hf⟩ := h W.1 h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).1, (mul_eq_one.1 hf).1⟩

theorem infinite_setOf_splitsCompletely (E : Type) [Field E] [NumberField E] :
    {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u}.Infinite := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.trans ℚ E (AlgebraicClosure E)
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := ⟨inferInstance, inferInstance⟩
  let M := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ (AlgebraicClosure E) := IsAlgClosure.isGalois ℚ _
  haveI : IsGalois ℚ M := IsGalois.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely ℚ M
  have hsub : {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely M u} ⊆
      {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u} := fun u hu => splitsCompletely_of_tower (M := M) hu
  intro hfin
  have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite (hfin.subset hsub)
  have e := hd.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq
  have hpos : (0 : ℝ) < 1 / (Module.finrank ℚ M : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := M)
    positivity
  exact hpos.ne' e

theorem primesOver_rat_eq (E : Type) [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 ℚ)) :
    u.asIdeal.primesOver (𝓞 E) = (u.asIdeal.under ℤ).primesOver (𝓞 E) := by
  have hs : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun x =>
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [eq_intCast, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨?_⟩
    rw [h.over, Ideal.under_under]
  · intro h
    refine ⟨Ideal.comap_injective_of_surjective _ hs ?_⟩
    change Ideal.under ℤ u.asIdeal = Ideal.under ℤ (Q.under (𝓞 ℚ))
    rw [Ideal.under_under, ← h.over]

end GlobalTheory.SplitAway

open GlobalTheory.SplitAway GroundTheory.Global in
theorem GlobalTheory.SplitAway.exists_splitsFully_notMem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (HeightOneSpectrum (𝓞 F))),
    ∃ v ∉ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ P
  classical
  obtain ⟨u, huS, huT⟩ := ((infinite_setOf_splitsCompletely E).diff
    (P.finite_toSet.image fun v : HeightOneSpectrum (𝓞 F) => v.under (𝓞 ℚ))).nonempty
  have hu : SplitsCompletely E u := huS
  obtain ⟨⟨v, hv⟩⟩ := GroundTheory.Global.nonempty_placesOver F u
  refine ⟨v, fun hP => huT ⟨v, hP, HeightOneSpectrum.ext hv.over.symm⟩, ?_, ?_⟩
  · show ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = Module.finrank ℚ E
    have e1 : v.asIdeal.under ℤ = u.asIdeal.under ℤ := by
      rw [hv.over, Ideal.under_under]
    rw [e1, ← primesOver_rat_eq]
    exact (splitsCompletely_iff_ncard_primesOver E u).1 hu
  · have hF : SplitsCompletely E v := hu.of_liesOver v
    haveI := (splitsCompletely_iff_isFiniteSplit (L := E) v).1 hF
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (v.adicCompletion F)
      (v.adicCompletion F ⊗[F] E)
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        haveI : Subsingleton (v.adicCompletion F ⊗[F] E) := e.toEquiv.subsingleton
        have h1 : Module.finrank (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) = Module.finrank F E :=
          Module.finrank_baseChange
        rw [Module.finrank_zero_of_subsingleton] at h1
        exact (Module.finrank_pos (R := F) (M := E)).ne h1
      · exact h
    exact ⟨(((Pi.evalAlgHom (v.adicCompletion F) (fun _ : Fin n => v.adicCompletion F) ⟨0, hn⟩).comp
      e.toAlgHom).restrictScalars F).comp Algebra.TensorProduct.includeRight⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.primitiveFrameDatum_blockSubstitution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  first | exact @GlobalTheory.FrameSubst.phiA_blockSubst | exact GlobalTheory.FrameSubst.phiA_blockSubst | (intros; apply GlobalTheory.FrameSubst.phiA_blockSubst <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | exact GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | (intros; apply GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO <;> assumption)
end
