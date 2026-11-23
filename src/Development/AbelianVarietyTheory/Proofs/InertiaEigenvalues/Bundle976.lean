module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle950
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle972
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeightOfPointwise
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle974
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_thetaLift_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  classical
  intro D X E Y i j b t hxi hQ y hy
  obtain ⟨u, hu⟩ := GlobalTheory.LiftClassSum.exists_low D X E Y j
  obtain ⟨m, h₀, c, z, hh₀, hz, hP⟩ := GlobalTheory.T.thetaLift_eq_multiple_principalLevel_classSum D X E Y i j b t hxi hQ y u
  have hB : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hq : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hc : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hgood : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → τ.Good := by
    rintro ⟨Q0, c0, r0⟩ hq0 hc0
    dsimp only at hq0 hc0
    subst hq0 hc0
    have h1 := Twist.triv_good (D := D) (A := Circle) (Q := ∅) splitSet_empty
    exact ⟨h1.isOpen, h1.rat, h1.real, h1.split, h1.unram, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := hgood _ hq hc
  have hA : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [hq]; exact Base.admissible_empty_of_good hB
  have hBase : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hc, mul_one], by rw [hQ, hq, Finset.union_empty]⟩
  have hW : (Y.Z.ρ.B i j b).IsWeil (Y.Z.ρ.tw i b 0 ∅ 1).chi (X.R.ωP j t) := hBase.isWeil X.char.thP.ωP htup
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum D _ _ (Y.Z.ρ.B i j b) hB (D.sp.V_sig _) _ hψ hA _ hW m h₀ hh₀ _
    (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) (Y.Z.good.classes i j b _ hψ hA)
  have hF := GlobalTheory.T.fockReading_translatedForm_mem_complexForms D X E Y i j b t hxi hQ y hy u hu z hz
  refine ⟨(c * κ) • (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))), Submodule.smul_mem _ _ hF, ?_⟩
  refine (congrArg (fun v => X.R.thF j t y v) hu.symm).trans (hP.trans ?_)
  exact (congrArg (c • ·) (hκ _ hF)).trans ((smul_smul c κ _).trans (LinearMap.map_smul _ _ _).symm)

end GlobalTheory.LiftClassSum

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ), ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ ∀ eT : AE D, IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ x : (AE D)ˣ, IsFlipDet V eT m x ∧ ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (flipScal χW V W T m x • F) = f := by
  first | exact @GlobalTheory.LevelSeries.exists_central_flip_step | exact GlobalTheory.LevelSeries.exists_central_flip_step | (intros; apply GlobalTheory.LevelSeries.exists_central_flip_step <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_basis_rationalForms_local_unit_ball : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧ ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1 := by
  first | exact @GlobalTheory.GeoTie.locBall_basis_exists | exact GlobalTheory.GeoTie.locBall_basis_exists | (intros; apply GlobalTheory.GeoTie.locBall_basis_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.definiteFormReading_injective_lattice_integralForms : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  first | exact @GlobalTheory.PlaceExp.rdE_injective_lattice | exact GlobalTheory.PlaceExp.rdE_injective_lattice | (intros; apply GlobalTheory.PlaceExp.rdE_injective_lattice <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.BpfUniform

theorem exists_weight_noCommonZero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 :=
  exists_weight_of_pointwise GlobalTheory.ScalarPoin.exists_cusp_ne

end GlobalTheory.BpfUniform
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.cuspForm_integral_arc_section_equalChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | exact GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | (intros; apply GlobalTheory.GoodTransfer.inV_of_arc_of_extIn <;> assumption)
end
