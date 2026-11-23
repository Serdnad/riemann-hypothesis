module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.BasesAt
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.cLoc_locU_bijective_open_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  intro E _ _ _ a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hf : ((cLoc w).comp (locU a w).subtype : locU a w → GL (Fin a) (w.adicCompletion E)) = (fun x => e x) := by
    funext x
    exact (he x).symm
  rw [hf]
  exact ⟨e.bijective, e.toHomeomorph.isOpenMap, e.continuous⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)), IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  first | exact @GlobalTheory.isOfFinOrder_of_conj_mem_ratU | exact GlobalTheory.isOfFinOrder_of_conj_mem_ratU | (intros; apply GlobalTheory.isOfFinOrder_of_conj_mem_ratU; all_goals assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.NormBelow.unrAt_under_of_compNorm | exact GlobalTheory.NormBelow.unrAt_under_of_compNorm | (intros; apply GlobalTheory.NormBelow.unrAt_under_of_compNorm <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) : ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u (n := a) → ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist


open GlobalTheory.ContraPair.SphTwist in
theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := GlobalTheory.ContraPair.SphTwist.conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2 (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem reindex_rename_point_det_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb : Submodule (𝓞 E) (Fin N → E)), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y ∧ Matrix.GeneralLinearGroup.det (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = Matrix.GeneralLinearGroup.det y ∧ HEq ((latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) (Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E)))).map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N n h J a y Lb
  subst h
  have hr : ∀ {A : Type} [CommRing A] (g : GL (Fin N) A), Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) g = g := by
    intro A _ g
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have hJ : J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
    ext i j
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hr]
  · rw [hr]
  · apply heq_of_eq
    rw [hJ, hr, map_reE_rfl, map_reE_rfl]

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.CrysFromGTwo

theorem matRep_twistM {K Γ : Type} [Field K] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) K)
    (χ : Γ →* Kˣ) (g : Γ) (v : Fin k → K) :
    matRep (twistM M χ) g v = ((χ g : Kˣ) : K) • matRep M g v := by
  change (((χ g : Kˣ) : K) • M g).mulVec v = ((χ g : Kˣ) : K) • (M g).mulVec v
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ h

theorem crys_chi (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π))))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  exact GlobalTheory.ChiOneEnl.chiOneE_of_isBlockSum hF D i r ρ π hs hc w hw C.LL C.le

theorem twist_mat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K LL : FinExt l)
    {k : ℕ} (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (χ : ↥(GK K) →* (↥LL.1)ˣ)
    (ht : IsTwistRep χ (matRep M) (matRep M')) (hχ : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : IsCrys (P.PD K) (matRep M)) : IsCrys (P.PD K) (matRep M') :=
  (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI T K LL _ _ _ _ χ ht hχ h).1

theorem crys_tw (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  have := D.nd.lPrime i
  have ht : IsTwistRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
    rw [locC_rTwO]
    exact matRep_twistM _ _ g v
  exact twist_mat (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL _ _ _ ht hχ h

end GlobalTheory.CrysFromGTwo
end
end
