module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle256
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrExtUnit

theorem exists_unit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    let S := sit D.loc HW l (D.locA l) K s LL h
    let E : S.Comparison₂ := ((F l).E K s LL h).tie
    ∀ (e : S.W.DD S.W.one) (t : ↥S.W.one.L.T),
      S.W.N S.W.one = Submodule.span (LetA S.O S.n) {e} → S.W.φD S.W.one e = e →
      Submodule.span S.O {(t : S.W.one.V)} = S.W.one.L.T →
      ∃ u : (S.O)ˣ, ∀ a : S.O,
        E.jD S.W.one (a • e) = (1 : S.RW) ⊗ₜ[S.O] (((u : S.O) * a) • t) := by
  intro S E e t hN hφ ht
  obtain ⟨u, hu'⟩ : ∃ u : (S.O)ˣ, E.jD S.W.one e = (algebraMap S.O S.RW (u : S.O)) ⊗ₜ[S.O] t :=
    GlobalTheory.Cyc.UnitGen.main D HW F l K s LL h e t hN hφ ht
  refine ⟨u, fun a => ?_⟩
  rw [map_smul, hu', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem smul_cocycle (S : Sit) {T Tp : LocLat S.G S.Qp S.LL S.O} (ι : LatHom T.L Tp.L) (x : T.V)
    (g : S.G) (et : Tp.V) (hx : ι.f x = Tp.ρ g et - et) (b : S.O) :
    ι.f (b • x) = Tp.ρ g (b • et) - b • et := by
  rw [← algebraMap_smul S.LL b x, ← algebraMap_smul S.LL b et, map_smul, map_smul, hx, smul_sub]

theorem smul_proj (S : Sit) {Tp Z : LocLat S.G S.Qp S.LL S.O} (π : LatHom Tp.L Z.L)
    (et : Tp.V) (b : S.O) : b • π.f et = π.f (b • et) := by
  rw [← algebraMap_smul S.LL b et, map_smul, algebraMap_smul]

theorem over_Ks (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExt (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.Cyc.dict_ext_Ks D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨_, resFun_Z1T T _ c hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem over_K (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExtΔ (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro _ hp T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hδ hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.ExtDict.dict_K D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    (fun h2 => absurd h2 hp) T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) hδ ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨c, hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F :=
  fun D HW F l _ K s LL h => ⟨over_Ks D HW F l K s LL h, over_K D HW F l K s LL h⟩

end GlobalTheory.HerrExtUnit
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.ExpansionsOdd



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm hN l _ K LL hA
  obtain ⟨p1, -, p3, p4, p5, -, -, -, p9, -⟩ := hN
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max LL
  have hLT := GlobalTheory.LevelClauseOdd.main D HW F Cm p4 p9 l K LL hA
  have C := ((Cm l).C K 1 LL hA.2.2).tie
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := p9 l K 1 LL hA.2.2
  refine ⟨fun hCA => ?_, Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of _ hLT.1 hG.1 hG.2, ?_⟩
  · have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=
      (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of _ hring hCA
  · have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
      rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
    have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL
    have hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hA.2.2) := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ h9
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)
      (p1 l K 1 LL hA.2.2) (p3 l K 1 LL hA.2.2) hLT.1 (p5 l K 1 LL hA.2.2) h9 hD hB C
      (p4 l K 1 LL hA.2.2) hLT.2

end GlobalTheory.ExpansionsOdd
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.rootOfUnity_padicComplex_mem_range_algClosure : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x := by
  first | exact @GlobalTheory.rootOfUnity_mem_range_Om | exact GlobalTheory.rootOfUnity_mem_range_Om | (intros; apply GlobalTheory.rootOfUnity_mem_range_Om; all_goals assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.HerrComplexH1

theorem herr_H1_description : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2a D HW F := by
  intro D HW F l _ K s LL h T _
  have H := GlobalTheory.HerrFull.herr_a_and_natural D HW F l K s LL h
  refine ⟨H.2.1 T, fun _ hp => ?_⟩
  have H1 := H.1 (fun e => absurd e hp) T
  exact ⟨H1.1, H1.2.1⟩

end GlobalTheory.NL.HerrComplexH1
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  first | exact @GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | exact GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | (intros; apply GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC chi1C)

namespace GlobalTheory.AmbWT

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def coef : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL

def grp (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Br.G D.nbr i w hw →* GE D.nd :=
  (decS D.nd w).comp (Br.iota D.nbr i w hw)

theorem locC_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    locC C M g = (M (grp hw g)).map (coef C) := rfl

theorem localizedCoefficientChar_apply (g : Br.G D.nbr i w hw) :
    chi1C C g = Units.map (coef C : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (grp hw g)) := rfl

theorem locC_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    locC C (rTwO D.nd i r x) = twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  rw [locC_apply]
  show coef C ((((chiU D.nd i 1)⁻¹ (grp hw g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (grp hw g) a b) =
    ((((chi1C C)⁻¹ g) : (↥C.LL.1)ˣ) : ↥C.LL.1) * (locC C (rO D.nd i r x) g) a b
  rw [map_mul, locC_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, localizedCoefficientChar_apply]
  rfl


open Classical in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hd
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  have hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : CoefExt D i w hw),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) ∧
        IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) := by
    intro w hw C
    have h1 := (hG w hw C).2 π
    rw [← locC_rTwO] at h1
    exact (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 h1
  refine ⟨fun _ w hw _ C => (hc w hw C).1, fun _ w hw _ C => ⟨(hc w hw C).2, ?_, ?_⟩⟩
  · exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) (D.nbr i w hw).Kw C.LL _ _ (hc w hw C).2).1
  · exact (hG w hw C).1.2.2.2.2.2.2

end GlobalTheory.AmbWT
end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.InvColim

theorem colim_equiv {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G]
    [CompactSpace G] {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M) (hmono : Monotone N)
    (hopen : ∀ n, IsOpen (N n : Set M)) (hcov : ∀ x, ∃ n, x ∈ N n) (hfg : ∀ n, IsFGTop O (N n)) :
    ∃ e : H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) ≃ₗ[O] M, ∀ n (z : H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n))),
      e (mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) (N n).subtype continuous_subtype_val
        (twist_map ε (N n).subtype) z) = Θ.θ (N n) (hfg n) z := by
  have hinj := GlobalTheory.T.map_H2_subtype_injective Θ N hmono hopen hcov hfg
  have hsurj := GlobalTheory.T.exists_H2_preimage_of_monotone_open_exhaustion ε N hmono hopen hcov
  let ι : ∀ n, H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n)) →ₗ[O] H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) := fun n =>
    mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)
  let ψ : ∀ n, N n →ₗ[O] H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) := fun n => ι n ∘ₗ (Θ.θ (N n) (hfg n)).symm.toLinearMap
  have hup : ∀ n m (h : n ≤ m) (y : N n), ψ m (Submodule.inclusion (hmono h) y) = ψ n y := by
    intro n m h y
    let inc := Submodule.inclusion (hmono h)
    have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
    have hι : ∀ w, ι m (mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N m)) inc hinc (twist_map ε inc) w) = ι n w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H w => rfl
    have hw : (Θ.θ (N m) (hfg m)).symm (inc y) = mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (N m)) inc hinc (twist_map ε inc)
        ((Θ.θ (N n) (hfg n)).symm y) := by
      rw [LinearEquiv.symm_apply_eq, Θ.nat _ _ (hfg n) (hfg m) inc hinc, LinearEquiv.apply_symm_apply]
    show ι m ((Θ.θ (N m) (hfg m)).symm (inc y)) = ι n ((Θ.θ (N n) (hfg n)).symm y)
    rw [hw, hι]
  have hind : ∀ n m (y : M) (hn : y ∈ N n) (hm : y ∈ N m), ψ n ⟨y, hn⟩ = ψ m ⟨y, hm⟩ := by
    intro n m y hn hm
    rw [← hup n (max n m) (le_max_left _ _), ← hup m (max n m) (le_max_right _ _)]
    rfl
  let nn : M → ℕ := fun y => (hcov y).choose
  have hnn : ∀ y, y ∈ N (nn y) := fun y => (hcov y).choose_spec
  let Ψ : M →ₗ[O] H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) :=
    { toFun := fun y => ψ (nn y) ⟨y, hnn y⟩
      map_add' := fun y y' => by
        have hy : y ∈ N (max (nn y) (nn y')) := hmono (le_max_left _ _) (hnn y)
        have hy' : y' ∈ N (max (nn y) (nn y')) := hmono (le_max_right _ _) (hnn y')
        refine (hind _ _ (y + y') (hnn _) (add_mem hy hy')).trans ?_
        rw [hind _ _ y (hnn y) hy, hind _ _ y' (hnn y') hy', ← map_add (f := _)]
        rfl
      map_smul' := fun c y => by
        refine (hind _ (nn y) (c • y) (hnn _) (Submodule.smul_mem _ c (hnn y))).trans ?_
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  have hΨ : ∀ n (y : N n), Ψ y = ψ n y := fun n y => hind _ n y (hnn _) y.2
  have hΨi : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, hn⟩ := hcov y
    have h1 : ψ n ⟨y, hn⟩ = 0 := (hΨ n ⟨y, hn⟩).symm.trans hy
    have h2 : (Θ.θ (N n) (hfg n)).symm ⟨y, hn⟩ = 0 := hinj n (by rw [map_zero]; exact h1)
    have h3 : (⟨y, hn⟩ : N n) = 0 := by simpa using h2
    exact congrArg Subtype.val h3
  have hΨs : Function.Surjective Ψ := by
    intro z
    obtain ⟨n, z', hz'⟩ := hsurj z
    refine ⟨(Θ.θ (N n) (hfg n) z' : M), ?_⟩
    rw [hΨ n]
    show ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z')) = z
    rw [LinearEquiv.symm_apply_apply]
    exact hz'
  refine ⟨(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).symm, fun n z => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  show _ = Ψ _
  rw [hΨ n]
  show _ = ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z))
  rw [LinearEquiv.symm_apply_apply]

section Lat
variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

theorem frac_isFGTop (hO : PadicCoeff p O) (hF : FracTop O) (n : ℕ) :
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := GlobalTheory.T.isFGTop_p_pow_inverse_lattice hO hF n

theorem frac_cover (hO : PadicCoeff p O) (y : FractionRing O) :
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing hO y

theorem ko_discrete (hF : FracTop O) : DiscreteTopology (KO O) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have h1 : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext y; simp [Submodule.mem_one]
  have h2 : ({0} : Set (KO O)) =
      (1 : Submodule O (FractionRing O)).mkQ '' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨0, zero_mem _, map_zero _⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 hy
  rw [h2]
  exact (Submodule.isOpenQuotientMap_mkQ _).isOpenMap _ (h1 ▸ hF.emb.isOpen_range)

end Lat

theorem inv_iso (hT : Formalism.GaloisCohomology.LocalTateDualityK) : InvIso := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hε
  obtain ⟨Θ⟩ := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT hK hO i hε
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI := ko_discrete hF
  let F : ℕ → Submodule O (FractionRing O) := fun n =>
    (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  let T : ℕ → Submodule O (KO O) := fun n => LinearMap.ker (LinearMap.lsmul O (KO O) ((p : O) ^ n))
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun n y hy => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hy
    refine Submodule.mem_one.2 ⟨(p : O) * a, ?_⟩
    simp only [LinearMap.lsmul_apply] at ha ⊢
    rw [map_mul, ha, pow_succ, mul_comm _ (p : O), mul_smul, Algebra.smul_def (p : O) (((p : O) ^ n) • y)]
  have hFo : ∀ n, IsOpen (F n : Set (FractionRing O)) := fun n => by
    have : (F n : Set (FractionRing O)) =
        (fun y : FractionRing O => ((p : O) ^ n) • y) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
      ext y; simp [F, Submodule.mem_one]
    rw [this]
    exact hF.emb.isOpen_range.preimage (continuous_const_smul _)
  have hFfg := frac_isFGTop hO hF
  have hred : ∀ n, ∀ y ∈ F n, toKO O y ∈ T n := fun n y hy => by
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply, F, Submodule.mem_comap] at hy ⊢
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy
  have hTm : Monotone T := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [pow_succ, mul_comm, mul_smul, hx, smul_zero]
  have hTo : ∀ n, IsOpen (T n : Set (KO O)) := fun n => isOpen_discrete _
  have hTc : ∀ x, ∃ n, x ∈ T n := fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := frac_cover hO y
    exact ⟨n, hred n y hn⟩
  have hTsurj : ∀ n, (F n).map (toKO O) = T n := fun n => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy => hred n y hy) fun x hx => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨y, ?_, rfl⟩
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hTfg : ∀ n, IsFGTop O (T n) := fun n => by
    refine ⟨?_, inferInstance, inferInstance⟩
    have := (hFfg n).fg
    rw [← hTsurj n, Module.Finite.iff_fg]
    exact Submodule.FG.map _ (Module.Finite.iff_fg.1 this)
  obtain ⟨eF, heF⟩ := colim_equiv Θ F hFm hFo (frac_cover hO) hFfg
  obtain ⟨eT, heT⟩ := colim_equiv Θ T hTm hTo hTc hTfg
  refine ⟨eT, eF, fun z => ?_⟩
  obtain ⟨n, hn⟩ := frac_cover hO (eF z)
  set z' := (Θ.θ (F n) (hFfg n)).symm ⟨eF z, hn⟩
  have hz : mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (F n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (FractionRing O)) (F n).subtype continuous_subtype_val
      (twist_map ε (F n).subtype) z' = z := eF.injective (by rw [heF, LinearEquiv.apply_symm_apply])
  let red : F n →ₗ[O] T n := ((toKO O).comp (F n).subtype).codRestrict (T n) fun y => hred n y y.2
  have hredc : Continuous red := (toKO_cont.comp continuous_subtype_val).subtype_mk _
  have e3 : mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (FractionRing O)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε)
      (mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (F n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε _) z') =
      mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (T n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (KO O)) (T n).subtype continuous_subtype_val (twist_map ε _)
        (mapH2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (F n)) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (T n)) red hredc (twist_map ε red) z') := by
    induction z' using Submodule.Quotient.induction_on with
    | H w => rfl
  rw [← hz, e3, heT, Θ.nat _ _ (hFfg n) (hTfg n) red hredc]
  refine Eq.trans ?_ (congrArg (toKO O) (heF n z')).symm
  rfl

end GlobalTheory.InvColim
end
end
