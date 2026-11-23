module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle331
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

end GlobalTheory.GalLift.BaseEquiv

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_action_preserves_integral_cusp_forms : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  first | exact @GlobalTheory.LevActInt.intAll_actLev | exact GlobalTheory.LevActInt.intAll_actLev | (intros; apply GlobalTheory.LevActInt.intAll_actLev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilParts

theorem integrableOn_theta_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ :=
  GlobalTheory.DefiniteQuotient.integrableOn_theta

end GlobalTheory.WeilParts
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ConjWeil

theorem hecke_mul_inv {D : D7} {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem exists_of_datum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (ho : IsWeilDatumO ψ S T χS χT om)
    (hS : IsHeckeChar D χS') (hT : IsHeckeChar D χT') (rS : ResEta D χS' S.rank) (rT : ResEta D χT' T.rank) :
    ∃ om', IsWeilDatumO ψ S T χS' χT' om' := by
  obtain ⟨o, h1, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (hecke_mul_inv hS ho.hecS) (hecke_mul_inv hT ho.hecT)
    (resEta_parity (resEta_mul rS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul rT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  exact ⟨o, h1⟩

theorem even_im_hermitian_sub (R : Ranks) : 0 % 2 = R.nV % 2 ∧ (0 + 1) % 2 = R.r % 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have h2 := R.two_le_m
  unfold Ranks.nV Ranks.r
  constructor <;> omega

end GlobalTheory.GalLift.ConjWeil
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_weilDatum_twist_heckeCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  first | exact @GlobalTheory.WeilChange.exists_weilDatum_twist | exact GlobalTheory.WeilChange.exists_weilDatum_twist | (intros; apply GlobalTheory.WeilChange.exists_weilDatum_twist <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add (f := _)]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

theorem rder_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  intro D θ V S M J χ T _ hT v τ
  have hs := smoothVec_of_mem M τ (v τ).2
  refine ⟨hs, fun X hX => ?_⟩
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hπ := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hπ _ hs
  refine ⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  have hd := GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX
  rw [← hℓT]
  have e : (fun t : ℝ => T v (x * oneP θ V τ X t)) =
      fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
    funext t
    have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
    let w : M.sm τ := ⟨_, Submodule.subset_span (h1 _ hg)⟩
    have h4 := congrFun (hT.equiv τ _ hg v w rfl) x
    exact ((hℓT w).trans h4).symm
  show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _
  rw [e]
  exact hd.deriv

end GlobalTheory.HolRead.MultDer
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.KappaPowMod

theorem algebraicModulusOneAll_one : StandardLatticesGL3.Mod1All 1 := by
  refine ⟨one_mem _, fun σ => ?_⟩
  have e : (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 := rfl
  rw [e, map_one, norm_one]

theorem algebraicModulusOneAll_mul {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem algebraicModulusOneAll_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem algebraicModulusOneAll_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero => simpa using algebraicModulusOneAll_one
  | succ n ih => rw [pow_succ]; exact algebraicModulusOneAll_mul ih ha

theorem algebraicModulusOneAll_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using algebraicModulusOneAll_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact algebraicModulusOneAll_inv (algebraicModulusOneAll_pow ha _)

def phiQ (D : D7) : D.host.E →+* TaylorLogMetric.Qbar :=
  D.host.φ₀.codRestrict TaylorLogMetric.Qbar fun x => Formalism.L2.KerInert.AlgP.phi_mem_Qbar x

theorem splitPrime_rootChoice_algebraicModulusOneAll {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) (hp : p.Prime) (hs : SplitK D p) :
    StandardLatticesGL3.Mod1All (k.rt p) := by
  set h := 2 * classNumber D.host.K with hh
  have h0 : h ≠ 0 := mul_ne_zero two_ne_zero (classNumber_ne D)
  set x : D.host.E := (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) with hx
  set_option synthInstance.maxHeartbeats 200000 in
  have hx0 : x ≠ 0 := by
    have h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0 := by simpa using k.pi_ne_zero p hp hs
    simpa [hx] using h1
  have hpow := k.rt_pow p hp hs
  have hmem : k.rt p ∈ TaylorLogMetric.Qbar := by
    have hq : k.rt p ^ h ∈ TaylorLogMetric.Qbar := by
      rw [hpow]
      exact div_mem (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _) (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _)
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := h) (Nat.pos_of_ne_zero h0)
      (mem_algebraicClosure_iff.1 hq))
  refine ⟨hmem, fun σ => ?_⟩
  let ψ : D.host.E →+* ℂ := σ.comp (phiQ D)
  have hc : ψ (D.host.conj x) = starRingEnd ℂ (ψ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  have hψ0 : ψ x ≠ 0 := (map_ne_zero ψ).2 hx0
  have e : (⟨k.rt p, hmem⟩ : TaylorLogMetric.Qbar) ^ h = phiQ D x / phiQ D (D.host.conj x) := by
    apply Subtype.ext
    simp only [IntermediateField.coe_pow, IntermediateField.coe_div]
    exact hpow
  have hn : ‖σ ⟨k.rt p, hmem⟩‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_div₀]
    change ‖ψ x / ψ (D.host.conj x)‖ = 1
    rw [hc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hψ0)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 hn

theorem kappa_pow_mod1All : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ),
    StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  intro D cc δ B m
  refine algebraicModulusOneAll_pow ?_ m
  show StandardLatticesGL3.Mod1All (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))
  exact finprod_induction StandardLatticesGL3.Mod1All algebraicModulusOneAll_one (fun _ _ => algebraicModulusOneAll_mul)
    fun p => algebraicModulusOneAll_zpow (splitPrime_rootChoice_algebraicModulusOneAll B.kc p p.2.1 p.2.2) _

end GlobalTheory.KappaPowMod
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.integralEigenBasis_transport_pullback_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  first | exact @GlobalTheory.IntEigTransport.transport | exact GlobalTheory.IntEigTransport.transport | (intros; apply GlobalTheory.IntEigTransport.transport <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem lastPos_wtA_of_kapIs : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → ∀ i : Fin D.R.m, LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) :=
  fun D T κ h hκ i =>
    GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins _ (inR i) (κ i) (GlobalTheory.HolDict.lastPos_of_kapIs D κ hκ i)

end GlobalTheory.HolRead
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincCore



theorem mem_group_of_congruent : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (γ : GL (Fin D.R.r) D.host.E), ReciprocityTheory.ChartRestriction.G.FD.IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ → (∀ v ∈ ((T.U j σ).X k).Λ, ∃ u ∈ ((T.U j σ).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v = v + T.Q.l.M • u) → γ ∈ ((T.U j σ).X k).Γ := by
  intro D T h j hj σ hσ k γ hγ hc0
  have hc : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hc0 x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧ (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  first | exact @GlobalTheory.QSA.exists_idem_pick_unit | exact GlobalTheory.QSA.exists_idem_pick_unit | (intros; apply GlobalTheory.QSA.exists_idem_pick_unit <;> assumption)
end
