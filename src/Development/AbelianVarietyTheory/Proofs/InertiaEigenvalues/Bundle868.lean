module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle852
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle861
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle853
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle855
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle856
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuumVector_drop_auxiliary_places : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')] (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q → B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  first | exact @GlobalTheory.ExportSeries.vecAt_drop | exact GlobalTheory.ExportSeries.vecAt_drop | (intros; apply GlobalTheory.ExportSeries.vecAt_drop <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  first | exact @GlobalTheory.BaseLiftWeight.lam_eq | exact GlobalTheory.BaseLiftWeight.lam_eq | (intros; apply GlobalTheory.BaseLiftWeight.lam_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realisation_definite_realPoint_fockVector_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0) (B : Base (Vc D j) (Wc D j)), R.IsThP → B.Good → B.F.ψ = R.ψ → B.F.θ = R.θ → B.F.sT = cart (R.MW j (sg0 D A)) → (∀ τ, (B.F.BS τ).val = R.BV j τ) → B.F.BT = onb (R.MW j (sg0 D A)) → B.eta = R.eta → (∀ τ, HasInfExp D (R.toLevCh.mu t ((j : ℕ) + 1)) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2)) → ∀ u ∈ GinfC (Vc D j), ∀ P, R.ωP j t (u, 1) (R.ptP j t P) = R.ptP j t (B.act u P) := by
  first | exact @GlobalTheory.RealFockActionP.om_fock_vP | exact GlobalTheory.RealFockActionP.om_fock_vP | (intros; apply GlobalTheory.RealFockActionP.om_fock_vP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenReal



theorem downInt_lie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (τ : D.what₂.Tau)
    (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ →
    ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank),
    (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) →
    ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ), (∀ g, downInt R i t y (R.ptP i t P) l g = 0) →
    ∀ g, downInt R i t y (R.ptP i t P') l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y τ Y hY P P' hder l hvan g
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hom := (hP i t).datum
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ptP i t P) := hG.core.thP.pt_theta i t P
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hom hY
  have hf' := ht.theta hf

  have hid : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y (R.ptP i t P) = R.ptP i t P' := by
    funext z
    have h1 := hd _ hf 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact h1.unique (hder z)
  rw [← hid]
  set f := R.ptP i t P with hfdef
  set f' := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y f with hf'def

  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have hrat : ∀ γ ∈ GQ (Vc D i), ∀ (c : GA D (Vc D i)) (g' : GA D (Wc D i)),
      thetaKO (R.ωP i t) (γ * c) g' f' = thetaKO (R.ωP i t) c g' f' := by
    intro γ hγ c g'
    unfold thetaKO
    have e : ((γ * c, g') : GA D (Vc D i) × GA D (Wc D i)) = ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (c, g') := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf')
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩

  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact (Vc D i) hpos
  have hΨ : Continuous fun p : GA D (Vc D i) × ℝ =>
      thetaKO (R.ωP i t) p.1 (g * oneP R.θ (Wc D i) τ Y p.2) f' * l (R.extV i t y p.1) := by
    refine Continuous.mul ?_ (hcont.comp continuous_fst)
    exact (hom.om_cont f' hf' 0).comp (continuous_fst.prodMk
      (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)))
  obtain ⟨B, hB⟩ := (hC.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hΨ.continuousOn
  have hbd : ∀ (h : GA D (Vc D i)) (x : ℝ), x ∈ Metric.ball (0 : ℝ) 1 →
      ‖thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h)‖ ≤ B := by
    intro h x hxb
    obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    subst e
    rw [hrat γ hγ c, hinv γ hγ c]
    exact hB (c, x) (Set.mk_mem_prod hc (Metric.ball_subset_closedBall hxb))

  have hfin : R.νV i t (R.fdV i t) < ⊤ := by
    haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (Vc D i)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
    have h1 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D (Vc D i)) (GQ (Vc D i)) C hC
      (fun h => by
        obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
        exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩)
      (R.νV i t) (hm.νV i t).1.1 (R.fdV i t) (hm.νV i t).2 (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h2 | h2
    · simp at h2
    · exact h2

  have hmeas : ∀ (φ : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ x : ℝ,
      AEStronglyMeasurable (fun h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) φ * l (R.extV i t y h))
        ((R.νV i t).restrict (R.fdV i t)) := fun φ hφ x =>
    (((hom.om_cont φ hφ 0).comp (continuous_id.prodMk continuous_const)).mul hcont).measurable.aestronglyMeasurable
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (R.νV i t).restrict (R.fdV i t))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (F := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f * l (R.extV i t y h))
    (F' := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h))
    (bound := fun _ => B) (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun x => hmeas f hf x)
    (GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y f l _ hf)
    (hmeas f' hf' 0) (.of_forall fun h x hxb => hbd h x hxb) (integrableOn_const hfin.ne)
    (.of_forall fun h x _ => ?_)).2
  · have e : (fun x : ℝ => ∫ h in R.fdV i t, thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f *
        l (R.extV i t y h) ∂(R.νV i t)) = fun _ => 0 := funext fun x => hvan _
    rw [e] at key
    have h0 := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at h0
    exact h0
  · refine (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g' => thetaKO (R.ωP i t) h g' f)
      (φ' := fun g' => thetaKO (R.ωP i t) h g' f') (fun g' => ?_) g x).mul_const _
    simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (h, g') 0

end GlobalTheory.DownLift.GenReal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.IndefR.NX

theorem goodE_of_eigOcc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → EigOcc D S θ hL Sb eig → ∀ i (s : D.ntw.Sig i), Formalism.MainNotions.BlochKatoReduction.Gen.goodE D.nexp i s := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc i s
  classical
  obtain ⟨h1, h2⟩ := D.ntw.jS_range i s
  obtain ⟨hiso, hgood, -⟩ := Bs.rhoS i s
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc _ h1 h2 _ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i (D.ntw.side i s) x hx0
  set e := Bs.eF i (D.ntw.jS i s) (D.ntw.side i s) h1 h2 with he
  refine ⟨e.symm (Φ x), by simpa using hΦ0, ?_, ?_⟩
  · letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective

    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
    map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]

    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A (D.ntw.jS i s)).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  · intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply,
      Bs.rowS_eig i s k P hk1 hk2 hsp hP]
    have h3 := hΦT (hL (D.ntw.jS i s) k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm

end GlobalTheory.TwInputs

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  first | exact @GlobalTheory.EmbExt.exists_side_embeddings | exact GlobalTheory.EmbExt.exists_side_embeddings | (intros; apply GlobalTheory.EmbExt.exists_side_embeddings <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



theorem _root_.GlobalTheory.T.twisting_char_values_mem_coeff_field_range : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ), ∃ a : FractionRing (X.O i), ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  first | exact @GlobalTheory.DeltaRange.delta_value_mem_range | exact GlobalTheory.DeltaRange.delta_value_mem_range | (intros; apply GlobalTheory.DeltaRange.delta_value_mem_range <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



theorem _root_.GlobalTheory.T.split_off_outside_S0 : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  first | exact @GlobalTheory.SplitOffS0.main | exact GlobalTheory.SplitOffS0.main | (intros; apply GlobalTheory.SplitOffS0.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chosenPlaces_admissible_goodSetup : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  first | exact @GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | exact GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | (intros; apply GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.ExportSeries

namespace GlobalTheory.OnePlaceCong

def locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) : Rˣ where
  val := 1 - g + g * x
  inv := 1 - g + g * (x⁻¹ : Rˣ)
  val_inv := by
    have h := x.mul_inv
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h
  inv_val := by
    have h := x.inv_mul
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h

theorem coe_locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    ((locU g hg x : Rˣ) : R) = 1 - g + g * x := rfl

theorem locU_inv {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    (locU g hg x)⁻¹ = locU g hg x⁻¹ := rfl

variable {D : D7}

theorem finPart_locU_mem {g : AE D} (hg : g * g = g) {z : (AE D)ˣ} (hz : finPart D (z : AE D) ∈ intAE D) :
    finPart D ((locU g hg z : (AE D)ˣ) : AE D) ∈ intAE D := by
  have h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)
  have hfg : finPart D g ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])
  rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul]
  exact add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)

theorem res_locU_eq_one {A : Type} [CommGroup A] {PP : Pl D.host.E} {χ : (AE D)ˣ →* A} {c : (kP PP)ˣ →* A}
    (hχ : IsResAt χ PP c) (hI : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (N : ℕ)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (x : (AE D)ˣ) (hx : finPart D (x : AE D) ∈ intAE D)
    (y : Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ intAE D) (hxy : finPart D (x : AE D) - 1 = N • y) :
    χ (locU (idemAt PP) hI.1.1 x) = 1 := by
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have hfa := finPart_locU_mem he hx
  have hxa := GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa
  obtain ⟨hE, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI
  obtain ⟨w, rfl⟩ := GlobalTheory.SplitDualLat.finPart_surjective (D := D) y
  have hX := GlobalTheory.IdemRes.toEAf_mem_of_finPart hx
  have hW := GlobalTheory.IdemRes.toEAf_mem_of_finPart hy
  have key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0 := by
    change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]
  have key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul] at key0
    linear_combination key0
  have ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩) := by
    apply Subtype.ext
    change Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) =
      1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) *
        (1 + N • Formalism.IndefR.Datum.toEAf D w)
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]
  have hN0 : ((N : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hN
  refine (hχ _ ?_ hxa 1 ?_).trans (map_one c)
  · change (1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP
    linear_combination (-((x : AE D) - 1)) * he
  · rw [ha, map_add (f := _), map_sub, map_one, map_mul, hres, map_add (f := _), map_one, map_nsmul, nsmul_eq_mul, hN0]
    simp

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  intro D A _ PP χ κ ht N hN x hx hxy
  obtain ⟨y, hy, hxy⟩ := hxy
  have hPP : PP ∈ ({PP} : Finset (Pl D.host.E)) := Finset.mem_singleton_self PP
  have hsp : SplitSet ({PP} : Finset (Pl D.host.E)) := ht.split
  have hI := hsp.isIdemAt hPP
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have h0 : idemAt PP * cA D (idemAt PP) = 0 := hsp.mul_conj hPP hPP
  have hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, he]
  have hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) =
      1 - idemAt PP - cA D (idemAt PP) := by
    linear_combination he + hc + 2 * h0
  have hres := ht.res PP hPP

  have hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x *
      locU (1 - idemAt PP - cA D (idemAt PP)) hg x := by
    apply Units.ext
    simp only [Units.val_mul, coe_locU]
    linear_combination ((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc +
      (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0

  have hA : χ (locU (idemAt PP) he x) = 1 := res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy

  have hB : χ (locU (cA D (idemAt PP)) hc x) = 1 := by
    have hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) =
        locU (idemAt PP) he (Units.map (cA D).toMonoidHom x) := by
      apply Units.ext
      change cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)
      rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    have h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1 := by
      refine res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y)
        (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_
      · change finPart D (cA D (x : AE D)) ∈ intAE D
        rw [GlobalTheory.SplitDualLat.finPart_cA]
        exact GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1
      · change finPart D (cA D (x : AE D)) - 1 = _
        rw [GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy,
          map_nsmul]
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    set b := locU (cA D (idemAt PP)) hc x with hb
    have hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) =
        ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) := by
      change cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)
      rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]
    obtain ⟨a, ha⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz
    have hr : χ (idF D a) = 1 := ht.real a
    have ha' : idF D a = b * Units.map (cA D).toMonoidHom b := ha
    rw [ha', map_mul, hcb, h1, mul_one] at hr
    exact hr

  have hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1 := by
    have hi0 : infPart D (idemAt PP) = 0 := SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI
    have hi1 : infPart D (cA D (idemAt PP)) = 0 := by
      rw [GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]
    have hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP := Finset.sum_singleton _ _
    refine ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_
    · rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub,
        RingHom.map_one, hi0, hi1, hx.1]
      ring
    · rw [locU_inv]
      exact finPart_locU_mem hg hx.2.2
    · change (idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) *
        (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _
      rw [hidem]
      linear_combination (-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0
  rw [hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]

end GlobalTheory.OnePlaceCong
end
end
