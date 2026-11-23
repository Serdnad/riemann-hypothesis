module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle753
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.SetPtOff
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ
  have fa := hS.facts
  have hHub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by linarith [hS.big]) le_rfl (by exact_mod_cast (Real.exp_pos _).le) (fa.admJ L hS.par) hS.par67 fa.admA
    fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1 fa.large.2.2 fa.nct fa.trip fa.same fa.block
    fa.muUnr fa.depthG
  have hR : RestPt i (X.r i) (X.ρ i) π := hHub.2.2.2.2.2.2.2.1 i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L hS.par)
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π :=
    semisimple_decomposition_of D i (X.r i) (X.ρ i) π fa.admA.2.2.2.2.2.2 hR.good hR.rho hR.ss
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i (X.r i) fa.Conclusion1.1 hR.good,
    _root_.GlobalTheory.GTwoTheta.main_alt_alt hP.font D L fa.g2.1 hJ.1 hJ.2.2.1 i (X.r i) (X.ρ i) π hR.good hR.ng0 hR.ng1 hZ hdec,
    _root_.Formalism.MainNotions.N.galois_condition_three_of_alt_alt D i (X.r i) (X.ρ i) π fa.Conclusion1.1 hR.good hdec hR.cont hHG fa.rhoBar (litBurnside_all D) hR.g3,
    _root_.Formalism.MainNotions.N.admG4_of_goodR D i (X.r i) fa.Conclusion1.1 hR.good,
    galois_condition_five_of D i (X.r i) fa.Conclusion2.1 hHG hR.good,
    (GlobalTheory.TameDesign.main D i).2,
    galois_condition_six_of D i (X.r i) fa.Conclusion2.2.1 hHG hR.good,
    GlobalTheory.T.blochKato_localCondition_all_localizations hP.bk hP.tate hP.euler D i,
    continuous_family_of D i (X.r i) hR.good,
    semisimple_family_of D i (X.r i) hR.good,
    hdec, hR.eps, GlobalTheory.T.completion_comparison_admissible_every_place_over D i, hR.shape, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i,
    GlobalTheory.T.integral_tate_H2_top hP.tate D i, GlobalTheory.T.unramifiedClassFieldBound_of_artin hP.artin D i⟩
end GlobalTheory.SetPtOff
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLinkTameShape
theorem restPt_of_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) (i : D.nd.Loc)
    (hi : D.nd.l i ∉ TwistedPlaces.gset D) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) : RestPt i (X.r i) (X.ρ i) π := by
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]; unfold Scale.b; exact (Real.exp_pos _).le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have fa := hS.facts
  exact (_root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P hL le_rfl hb
    (fa.admJ L hS.par) hS.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG).2.2.2.2.2.2.2.1 i hi π hπ
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ _ S hG
  have R := _root_.GlobalTheory.NLinkTameShape.restPt_of_alt hP D L P nch HW F X C₂ hS i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have h32 := hS.facts.Conclusion2.1 i hHG (X.r i) R.good
  have hx := (GlobalTheory.TameDesign.main D i).2
  have hrb := isRhoBar_of_isRhoOf D i π (X.ρ i π) R.rho
  intro v hv
  have hl := D.nd.SQ_l i v hv
  obtain ⟨ha, hb, hc⟩ := h32 v hv hl
  refine ⟨(hx v hv).1, fun hq x => ?_, fun hk => ?_, fun hvS => ⟨?_, fun a => ?_⟩⟩
  · obtain ⟨hprod, Pm, hPm⟩ := ha hq x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) :=
      LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (Matrix.toLin' ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    refine ⟨ψ.trans (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl), fun γ hγ u => ?_⟩
    have hM := hPm γ hγ
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) *
        mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ =
        Matrix.diagonal (fun k : Fin D.R.nV => if (k : ℕ) < D.R.r then 1 else
          algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ)) *
          ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      rw [← hM]
      have e : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ =
          (Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ * Pm) * Pm⁻¹ := by group
      have e2 := congrArg (fun g : GL (Fin D.R.nV) (Kf D.nd i) => (g : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i))) e
      simp only [Units.val_mul] at e2
      exact e2
    show Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl
        (((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)).mulVec
          ((mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ).mulVec u)) = _
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
    exact splitL_diagonal D.R.r D.R.t D.R.nV rfl _ _
  · obtain ⟨k, hk⟩ := hk
    have hvS : v ∈ D.nd.S i := by
      refine (D.nd.S_def i v).2 ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    obtain ⟨Pp, hU, hPp⟩ := hb ⟨k, hk⟩ hvS
    exact ⟨Pp, fun x γ hγ => hPp x γ hγ, hU⟩
  · exact (hc hvS).1 (X.ρ i) π S (Formalism.MainNotions.SumRepresentations.At.inertia_props_of_idempotent_choice D.nd hG)
  · have H := (hc hvS).2 _ hrb a
    obtain ⟨H0z, H1z, H2z⟩ := H
    rw [rhoBarTw_eq]
    letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
    haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : H0 ((twistRep (glRep (redRep D.nd i (X.ρ i π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a)).comp (decS D.nd v)) = ⊥ := H0z
      rw [e]
      infer_instance
    · convert H1z using 2
    · convert H2z using 2
end GlobalTheory.NLinkTameShape
end
end
end

end

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.set_pt_of_setup_not_twisted : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  first | exact @_root_.GlobalTheory.SetPtOff.main_alt_alt | exact _root_.GlobalTheory.SetPtOff.main_alt_alt | (intros; apply _root_.GlobalTheory.SetPtOff.main_alt_alt <;> assumption)
end

end
end
