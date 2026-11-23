module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ), EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  first | exact @GlobalTheory.PolDeg.rescale_psiEven | exact GlobalTheory.PolDeg.rescale_psiEven | (intros; apply GlobalTheory.PolDeg.rescale_psiEven <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.refinesPolarisedData_rescale_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  first | exact @GlobalTheory.PolDeg.half_rescale | exact GlobalTheory.PolDeg.half_rescale | (intros; apply GlobalTheory.PolDeg.half_rescale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  first | exact @GlobalTheory.DefectHom.exists_evenDefect_hom | exact GlobalTheory.DefectHom.exists_evenDefect_hom | (intros; apply GlobalTheory.DefectHom.exists_evenDefect_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  first | exact @GlobalTheory.PolDeg.half_symm_cocycle | exact GlobalTheory.PolDeg.half_symm_cocycle | (intros; apply GlobalTheory.PolDeg.half_symm_cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  first | exact @GlobalTheory.FibreDense.mem_closure_fibre | exact GlobalTheory.FibreDense.mem_closure_fibre | (intros; apply GlobalTheory.FibreDense.mem_closure_fibre <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem exists_fracSpec {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem tauBimult_of_half : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R)
    (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) →
    D.TauBimult := by
  intro R _ _ R' _ _ Q ρ D e hρ h
  obtain ⟨κ, hκ⟩ := exists_fracSpec ρ hρ
  obtain ⟨β, β₂, w, hpb, hsq, hgen, hnorm, hc, hper⟩ := h
  have per : ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J := by
    intro a b z J J' hJ hJ'
    have := hper κ hκ a b z J J' hJ hJ'
    rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this
  let k : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  have hQ : ∀ a a' b : Q.X, ∀ z J, Good Q.M.L z J →
      val (Q.tau (a + a') b) κ z J * @id ((TK R').left.presheaf.stalk z)ˣ
        (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub z J
        (k ≫ toUnit (TK R) ≫ Q.c a) (k ≫ toUnit (TK R) ≫ Q.c a') (k ≫ toUnit (TK R) ≫ Q.c b)) =
      val (Q.tau a b) κ z J * val (Q.tau a' b) κ z J := by
    intro a a' b z J hJ
    have hcorr : LB.Gen.Corr Q.M.L _ _ _ _ (LB.mulGen Q.M.L _ _ _ _ (Q.tau (a + a') b)
        (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
          (lift (toUnit (TK R) ≫ Q.c a) (lift (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau a b) (Q.tau a' b)) := by
      refine corr_of_val Q.M.isLB fun y J hJ => ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)).trans ?_
      rw [Category.id_comp]
      exact Q.tau_add a a' b y J hJ
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ hcorr κ).trans (val_mul hJ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_cub Q.cub k hJ _ _ _).symm
  intro a a' b
  refine corr_of_val D.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB y (K := PEmpty) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans ?_
  rw [Category.id_comp]
  have hx : toUnit (TK R') ≫ D.c (a + a') = (toUnit (TK R') ≫ D.c a) * (toUnit (TK R') ≫ D.c a') := by
    rw [D.c_add, padd, comp_lift_assoc, Hom.mul_def]
  have hu : ∀ χ : D.X, (k ≫ toUnit (TK R) ≫ Q.c (e χ)).left = (toUnit (TK R') ≫ D.c χ).left ≫ β := by
    intro χ
    simp only [Over.comp_left, Over.homMk_left, toUnit_left, Category.assoc, hc, k]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Over.Hom.left (Q.c (e χ))) hκ
  obtain ⟨-, hw⟩ := GlobalTheory.T.mumfordBundleIso_normalised_respects_laws _ _ Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub (spMap ρ) β β₂ w
    hpb D.P.isAb hsq hgen hnorm (TK R') (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)
    y J J' hJ hJ'
  have hw' := hw _ _ _ (hu a) (hu a') (hu b)
  rw [← hx] at hw'
  have hq := hQ (e a) (e a') (e b) y J hJ
  rw [← map_add (f := _)] at hq
  change val (D.tau (a + a') b) (𝟙 _) y J' * cubV D.cub y J' _ _ _ = _
  rw [per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ']
  calc _ = (lamVal w (lift (toUnit (TK R') ≫ D.c (a + a')) (toUnit (TK R') ≫ D.c b)).left y J J' *
        cubV D.cub y J' (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)) *
        val (Q.tau (e (a + a')) (e b)) κ y J := by ac_rfl
    _ = _ := by
      rw [hw']
      calc _ = lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left y J J' *
            lamVal w (lift (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)).left y J J' *
            (val (Q.tau (e (a + a')) (e b)) κ y J * @id ((TK R').left.presheaf.stalk y)ˣ
              (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub y J
              (k ≫ toUnit (TK R) ≫ Q.c (e a)) (k ≫ toUnit (TK R) ≫ Q.c (e a')) (k ≫ toUnit (TK R) ≫ Q.c (e b)))) := by
            ac_rfl
        _ = _ := by rw [hq]; ac_rfl

end GlobalTheory.PolDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleForm

open GlobalTheory.TauTwist (unitAt unitAt_injective IsScalarForm)

theorem scalar_of_laws {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R)
    [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ) (hB : D.TauBimult) (hW : TraceFormTwistIso D oa w0)
    (hB' : (GlobalTheory.PolDeg.rescale D g).TauBimult)
    (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst)
    (ho : @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB)
    (hW' : @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0) :
    IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧
      ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ := by
  letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst
  have hG := GlobalTheory.globalFns_holds
  let y : (TK R).left := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨I, hJ⟩ := GlobalTheory.DegPull.exists_good' D.P.isLB y
  have vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I =
      unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I := fun a b => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact GlobalTheory.PolDeg.rescale_tau_val D g a b hJ
  have sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹ := fun a b => by
    rw [add_comm, mul_right_comm]
  have al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ =
      (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹) := fun a a' b => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e'' := (congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))
    rw [_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  obtain ⟨onB', cl', tb'⟩ := oa'
  obtain rfl : onB' = oa.onB := ho
  refine ⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩
  · rw [sy, sy a b, sy a b']
    exact al b b' a
  · have hr := GlobalTheory.TorusExt.exists_isRos hG oa (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := hr
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))
    have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))
    have e'' := (congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))
    rw [← e, _root_.mul_assoc] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  · obtain ⟨u, hu, u₀, h⟩ := hW
    obtain ⟨u', hu', u₀', h'⟩ := hW'
    have k := gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu'
      (fun z J hz => by
        have a := val_corr hz u₀ (𝟙 _)
        have b := val_corr hz u₀' (𝟙 _)
        rw [val_pull hz, val_one, Category.id_comp] at a
        have b' := ((val_pull hz _ _ _).symm.trans b).trans (val_one _)
        rw [Category.id_comp] at b'
        exact a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [val_pull hJ] at e
    have e'' := (congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))
    rw [_root_.mul_assoc, e] at e''
    exact (unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm

theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R) [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ), D.TauBimult → TraceFormTwistIso D oa w0 → (GlobalTheory.PolDeg.rescale D g).TauBimult → ∀ (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst), @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB → @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0 → GlobalTheory.TauTwist.IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧ ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ :=
  fun D _ oa w0 g a b c oa' d e => scalar_of_laws D oa w0 g a b c oa' d e

end GlobalTheory.RescaleForm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.ChartTraitForm


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

theorem isMonomial_pull {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] {κ : R →+* W}
    {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg κ D D') {m : ℕ} {r : Fin m → R}
    {B : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D r B) {ϖ : W} {a : Fin m → ℕ}
    (ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k)) (β : LinearMap.BilinForm ℤ D'.X)
    (hβ : ∀ y, β y y = ∑ k, (a k : ℤ) * B k (hD.xe y) (hD.xe y)) : IsMonomial D' ![ϖ] ![β] := by
  intro y
  obtain ⟨u, n, hn, hc⟩ := h (hD.xe y)
  obtain ⟨u', hc'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
  have h₁ : Associated (ϖ ^ ∑ k, a k * n k) (u' * κ (u * ∏ i, r i ^ n i)) := by
    refine Associated.symm ((associated_unit_mul_left _ _ u'.isUnit).trans ?_)
    rw [map_mul, map_prod, ← Finset.prod_pow_eq_pow_sum]
    refine (associated_unit_mul_left _ _ (u.isUnit.map κ)).trans (Associated.prod _ _ _ fun i _ => ?_)
    rw [map_pow, pow_mul]
    exact (ha i).pow_pow
  obtain ⟨v, hv⟩ := h₁
  refine ⟨v, ![∑ k, a k * n k], fun i => ?_, ?_⟩
  · fin_cases i
    simp only [Fin.zero_eta, Matrix.cons_val_zero, hβ, hn]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, mul_comm, hv]
    exact hc'

theorem exists_trait : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  intro o _ ζ g n F S j V _ _ _ Q ξ hUO m t δ R' _ _ _ ρ r D e hR' hρ hρf _ hr ht hδ hRef hmon W _ _ _ hW κ hκ hκl
  obtain ⟨G', _, _, A, U, y', α, α₂, hG, hy, hα, hsq, hL⟩ := hUO.2 R' ρ hR' hρ hρf D e hRef
  have h0 : CharZero R' := hR'.2.2.2
  have hW0 : CharZero W := charZero_of_injective_ringHom hκ
  obtain ⟨D', hD, A', U', gA, gpA, tA⟩ := exists_pull (I := maximalIdeal R') (I' := maximalIdeal W)
    ⟨hR'.1, inferInstance, hR'.2.1, hR'.2.2.1⟩ ⟨inferInstance, inferInstance, inferInstance, hW⟩ κ hκ
    (Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit κ a ha) hG U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A A'.A gA gpA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hr0 : ∀ k, κ (r k) ≠ 0 := fun k h => ht k (hρ (hκ (by rw [← hr, map_pow, h]; simp)))
  choose a u hu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hr0 k) hϖ
  have ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k) := fun k => by
    rw [hu]; exact associated_unit_mul_left _ _ (u k).isUnit
  let e' : D'.toPre.X ≃+ Q.X := hD.xe.trans e
  let β : LinearMap.BilinForm ℤ D'.toPre.X := ∑ k, ((2 * a k : ℕ) : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ k)
  have hβ : ∀ x y, β x y = ∑ k, ((2 * a k : ℕ) : ℤ) * δ k (e' x) (e' y) := fun x y => by
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ jK R' = jK W ≫ spMap κ :=
    (GlobalTheory.ArcPull.fracMap_sq hκ).symm.trans (Category.id_comp _)
  let T : Trait F :=
    { V := W, complete := hW, ϖ := ϖ, irr := hϖ, y := spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y'
      G := (Over.pullback (spMap κ)).obj G', semi := IsSemiAbelian.pullback _ G' hG, D := D', A := A', U := U'
      α := gA ≫ α, α₂ := β₂ ≫ α₂, cart := gpA.comp hα
      sq := ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hβ₂.1, Category.assoc],
        by rw [Category.assoc, hsq.2, ← Category.assoc, hβ₂.2, Category.assoc]⟩
      lb := hΛ A.L A'.L _ F.univ.P α₂ A.isLB A'.isLB F.univ.isLB tA hL
      β := β
      symm := fun x y => by
        rw [hβ, hβ]
        exact Finset.sum_congr rfl fun k _ => by rw [hδ]
      mono := isMonomial_pull hD hmon ha β fun y => by
        rw [hβ]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : ((2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) (hD.xe y) (hD.xe y) = 2 * δ k (e' y) (e' y) := rfl
        rw [this]
        push_cast
        ring }
  refine ⟨T, RingHom.id W, fun k => 2 * a k, e', Function.bijective_id, ?_, fun k => ?_, hβ⟩
  · show jK W ≫ spMap (RingHom.id W) ≫ spMap κ ≫ spMap ρ ≫ ξ = (spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y') ≫ j
    have : spMap (RingHom.id W) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, Category.assoc, hy, ← Category.assoc (spMap (GlobalTheory.ArcPull.fracMap hκ)), sq, Category.assoc]
  · show Associated (κ (ρ (t k))) (ϖ ^ (2 * a k))
    rw [← hr, map_pow, mul_comm, pow_mul]
    exact (ha k).pow_pow

end GlobalTheory.Poinc.ChartTraitForm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  first | exact @GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | exact GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | (intros; apply GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_endChar_pull : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : FinalForm.G ⟶ FinalForm.G), IsMonHom f → ∃ (fR : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR m := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm x R _ _ _ j hR G _ _ gm hpb D A U f hf
  have hG : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ FinalForm.G G gm hpb FinalForm.semi
  let fR : G ⟶ G :=
    Over.homMk (hpb.1.lift (gm ≫ f.left) G.hom (by rw [Category.assoc, Over.w f, hpb.1.w])) (hpb.1.lift_snd _ _ _)
  have e : fR.left ≫ gm = gm ≫ f.left := hpb.1.lift_fst _ _ _
  have hfR : IsMonHom fR := Out.PullGtPf.isMonHom_of_grpPullback hpb hpb f fR e
  obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hR G hG D A U fR hfR
  exact ⟨fR, m, hfR, e, hm⟩

end GlobalTheory.UPoinc
end
