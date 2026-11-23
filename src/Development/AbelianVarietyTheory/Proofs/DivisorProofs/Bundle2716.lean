module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SecConst


open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in
theorem exists_secB_isUnit_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ Y n' v' dd _ D q _ h _ _ _ ρ hρ B' _ π₁ π₂ c' _ _ _ _
  refine ⟨6, fun e he mu al => ?_⟩
  have hpt : ∀ zz, (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz =
      (P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d)) := by
    intro zz
    rw [Scheme.Hom.comp_apply]
    congr 1
    have key : ∀ r : ChartRing k m d,
        (constHom ρ) r = algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r) := by
      intro r
      simp [constHom, hρ r]
    apply PrimeSpectrum.ext
    ext r
    show (constHom ρ) r ∈ PrimeSpectrum.asIdeal (R := DualNumber k) zz ↔
      r ∈ IsLocalRing.maximalIdeal (ChartRing k m d)
    rw [key, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
    by_cases h0 : MvPowerSeries.constantCoeff r = 0
    · simp [h0, Ideal.zero_mem]
    · refine iff_of_false (fun hm => ?_) h0
      have hu : IsUnit (algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r)) :=
        (isUnit_iff_ne_zero.2 h0).map _
      exact (PrimeSpectrum.isPrime (R := DualNumber k) zz).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hxc : P.D.toPre.P.A.hom ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) =
      IsLocalRing.closedPoint (ChartRing k m d) := by
    show ((P.D.toPre.c mu).left ≫ P.D.toPre.P.A.hom) _ = _
    rw [Over.w (P.D.toPre.c mu)]
    rfl
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre (ChartRing k m d) (GlobalTheory.MumfordChart.admissibleBase_chartRing k m d).2.2.2 P.D.toPre al _ hxc
  have hA := (GlobalTheory.abelianSchemeLaws_all).1.ample
  obtain ⟨N, s, hcov⟩ := (hA (Spec (CommRingCat.of (ChartRing k m d))) P.D.toPre.P (e - 2) (by omega)).1 ⊤
    (isAffineOpen_top _)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : P.D.toPre.P.A.left ⟶ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ' ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) ∈ ⨆ i, nonzeroLocus (s i) by
      rw [hcov]; trivial)
  have hF : FormEq (Sum.elim (DegPre.famφB P.D.toPre al)
      (fun _ : Fin (e - 2) => ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι))
      (Sum.elim (DegPre.famε 2) (fun _ => 1)) (DegPre.famφB P.D.toPre al) (DegPre.famε e) := by
    intro U _ hh
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hρ', Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zpow_one, Fin.prod_univ_four]
    have e0 : DegPre.famφB P.D.toPre al 0 = 𝟙 _ := rfl
    have x0 : DegPre.famε 2 0 = 1 := by simp [DegPre.famε]
    have y0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
    have x1 : DegPre.famε 2 1 = DegPre.famε e 1 := rfl
    have x2 : DegPre.famε 2 2 = DegPre.famε e 2 := rfl
    have x3 : DegPre.famε 2 3 = DegPre.famε e 3 := rfl
    rw [x0, y0, x1, x2, x3, e0, show (e : ℤ) - 1 = 1 + ((e - 2 : ℕ) : ℤ) by omega, zpow_add, zpow_natCast,
      zpow_one]
    ac_rfl
  obtain ⟨σ, hσ⟩ := exists_sec P.D.toPre.P.isLB hF (mulSec σ₂ (pullSec (s i) ρ'))
  refine ⟨σ, fun zz J hJ => ?_⟩
  rw [hσ _ _ zz J hJ, sval_mulSec _ _ _ zz hJ]
  erw [sval_pullSec (s i) ρ' _ zz hJ]
  refine IsUnit.mul ?_ ?_
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hσ₂
    exact isUnit_sval σ₂ _ zz hJ j (by rw [hpt]; exact hj)
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) _ zz hJ j (by rw [Scheme.Hom.comp_apply, hpt]; exact hj)

end GlobalTheory.SecConst
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtDec

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem cv_act (Y : Ray oa) {T : Over (Sp R)} (t : T ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : T ⟶ Y.H) (χ : Q.X)
    (y : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L y J) :
    (GlobalTheory.TorusModel.cv (Y.Φ T ((t ≫ Y.i) * x)) χ y J : T.left.presheaf.stalk y) =
      gs (𝟙 T.left) y ⊤ (t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) *
        GlobalTheory.TorusModel.cv (Y.Φ T x) χ y J := by
  have h := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x (t ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := T) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one] at h
  rw [mul_comm (t ≫ Y.i) x, h, Units.val_mul, (Y.Φ_i t).2 χ y J hJ, _root_.mul_comm]
  exact congrArg (fun s => gs (𝟙 T.left) y ⊤ s * _) (GlobalTheory.SplitTorusPoints.coord_single t χ)

theorem preimage_stable (Y : Ray oa) (W : Q.P.A.left.Opens) :
    (snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) ≤
      ((fst (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H ≫ Y.i) * snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ
        (Y.q.left ⁻¹ᵁ W) := by
  have := Y.q_linear.isMonHom
  exact fun p hp => GlobalTheory.LevelExpansion.act_mem Y.isKernel _ _ p hp

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec


open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv in
theorem isAffineHom_q : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa), IsAffineHom Y.q.left := by
  intro R _ _ D O _ _ _ oa Y
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem isWt_of_uu : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    GlobalTheory.UU.IsWt Y.i V u χ → IsWt Y χ V u := by
  intro R _ _ Q O _ _ _ oa Y V u χ h S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have w : (x' * x⁻¹) ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by
    rw [← Hom.one_def, MonObj.mul_comp, hq, ← MonObj.mul_comp, mul_inv_cancel, MonObj.one_comp]
  let t := Y.isKernel.lift (x' * x⁻¹) (toUnit _) w
  have ht : t ≫ Y.i = x' * x⁻¹ := Y.isKernel.lift_fst _ _ _
  have hx' : (t ≫ Y.i) * x = x' := by rw [ht, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  have key : t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c χ) := fn_ext fun y _ => by
    choose J hJ using fun ψ : Sp S ⟶ Q.P.A.left => exists_chart Q.P.isLB (ψ y)
    have e1 := cv_act Y t x χ y J hJ
    rw [hx'] at e1
    have e2 := congrArg Units.val (hc χ y J hJ)
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial] at e2
    exact (Units.mul_left_inj _).1 (e1.symm.trans e2)
  have h₁ : ⊤ ≤ ((t ≫ Y.i) * x).left ⁻¹ᵁ V := by rw [hx']; exact hV'
  rw [WtAlg.valR_eq' _ _ hV', WtAlg.valR_eq' _ _ hV, ← GlobalTheory.TorusGrading.val_congr hx' h₁ hV' u, h _ t x h₁ hV, map_mul,
    key, Iso.inv_hom_id_apply]

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem uu_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    IsWt Y χ V u → GlobalTheory.UU.IsWt Y.i V u χ := by
  intro R _ _ Q O _ _ _ oa Y V u χ h
  refine (GlobalTheory.CubCompare.isWt_iff_germ _ _ _ _).2 fun T z t x hx hx' => ?_
  obtain ⟨U, hU, hzU, hUle⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := x.left ⁻¹ᵁ V ⊓ ((t ≫ Y.i) * x).left ⁻¹ᵁ V) ⟨hx, hx'⟩
  let ρ : Sp Γ(T.left, U) ⟶ T.left := hU.fromSpec
  let φ : R →+* Γ(T.left, U) := (Spec.preimage (ρ ≫ T.hom)).hom
  have hφ : ρ ≫ T.hom = spMap φ := by simp [spMap, φ]
  let k : Over.mk (spMap φ) ⟶ T := Over.homMk ρ hφ
  have hr : ∀ p, ρ p ∈ U := fun p => by
    have : ρ p ∈ Set.range ρ := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨z', rfl⟩ : z ∈ Set.range ρ := by rw [hU.range_fromSpec]; exact hzU
  have hV₁ : ⊤ ≤ (k ≫ x).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).1
  have hV₂ : ⊤ ≤ (k ≫ ((t ≫ Y.i) * x)).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).2
  let c : Q.X → (Γ(T.left, U))ˣ := fun χ' => Units.map (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom.toMonoidHom
    (Units.map (k ≫ t).left.appTop.hom.toMonoidHom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ'))
  have hcv : ∀ χ', (unitOn (c χ')).val = (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val := fun χ' => by
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom
      ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val)) = _
    exact Iso.hom_inv_id_apply _ _
  have e : k ≫ ((t ≫ Y.i) * x) = ((k ≫ t) ≫ Y.i) * (k ≫ x) := by rw [MonObj.comp_mul, Category.assoc]
  have hc : ∀ χ' y J, Good Q.P.L y J → val ((Y.Φ _ (k ≫ ((t ≫ Y.i) * x))).s χ') (𝟙 _) y J =
      gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ')) * val ((Y.Φ _ (k ≫ x)).s χ') (𝟙 _) y J := by
    intro χ' y J hJ
    rw [e]
    apply Units.ext
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial, hcv]
    exact cv_act Y (k ≫ t) (k ≫ x) χ' y J hJ
  have hq : (k ≫ ((t ≫ Y.i) * x)) ≫ Y.q = (k ≫ x) ≫ Y.q := by
    have := Y.q_linear.isMonHom
    exact Over.OverMorphism.ext (by simp only [Over.comp_left, Category.assoc, GlobalTheory.LevelExpansion.act_q Y.isKernel t x])
  have E := h Γ(T.left, U) φ (k ≫ x) (k ≫ ((t ≫ Y.i) * x)) c _ _ rfl rfl hV₁ hV₂ hq hc
  rw [WtAlg.valR_eq' _ _ hV₂, WtAlg.valR_eq' _ _ hV₁] at E
  have E' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom E
  rw [Iso.hom_inv_id_apply, map_mul, Iso.hom_inv_id_apply] at E'
  have E'' := congrArg (gs (𝟙 _) z' ⊤) E'
  rw [GlobalTheory.CubCompare.gs_appLE, gs_mul _ z' ⊤ trivial, GlobalTheory.CubCompare.gs_appLE] at E''
  have hcv' : (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom (c χ : Γ(T.left, U)) =
      (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val := hcv χ
  have g1 : gs (𝟙 _) z' ⊤ ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) =
      gs (k ≫ t).left z' ⊤ (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val :=
    (gs_pull (𝟙 _) (k ≫ t).left z' ⊤ trivial _).trans (by rw [Category.id_comp])
  rw [hcv', g1] at E''
  apply (ConcreteCategory.bijective_of_isIso (ρ.stalkMap z')).1
  show (ρ.stalkMap z').hom _ = (ρ.stalkMap z').hom _
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv.charV
  rw [map_mul, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx' u, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx u,
    ← gs_unit _ _ ⊤ trivial, ← GlobalTheory.CubCompare.gs_comp ρ _ ⊤ z' trivial]
  exact E''

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem existsUnique_weights : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t) := by
  intro R _ _ Q O _ _ _ oa Y W hW f
  have hi : IsMonHom Y.i := Y.i_linear.isMonHom
  have := isAffineHom_q Y
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights (Sp R) Y.H (GlobalTheory.RayEv.Chr Q) Y.i hi _ (hW.preimage Y.q.left)
    (preimage_stable Y W)
  obtain ⟨a, ha, rfl⟩ := ex f
  refine ⟨a, ⟨fun χ => isWt_of_uu Y _ _ χ (ha χ), rfl⟩, fun F hF => ?_⟩
  let F' : GlobalTheory.RayEv.Chr Q →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) := F
  have e := un (F' - a) (fun χ => uu_of_isWt Y _ _ χ (WtAlg.isWt_sub (hF.1 χ) (isWt_of_uu Y _ _ χ (ha χ))))
    (by rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]; exact sub_eq_zero.2 hF.2.symm)
  exact sub_eq_zero.1 e

end GlobalTheory.Heat.WtDec
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat.GlueWt

theorem isWt_of_isInv : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (W : Y.H.left.Opens) (f : Γ(Y.H.left, W)), IsWt Y α W f → IsWt Y α W (dd W f) :=
  fun Y v dd h α W f hf => GlobalTheory.Heat.IsInv.isWt Y v dd h α W f hf

end GlobalTheory.Heat.GlueWt
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  first | exact @GlobalTheory.Heat.IsInv.isWt | exact GlobalTheory.Heat.IsInv.isWt | (intros; apply GlobalTheory.Heat.IsInv.isWt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtMul

open GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_add {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hq : x' ≫ Y.q = x ≫ Y.q)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J)
    (χ χ' : Q.X) : c (χ + χ') = c χ * c χ' := by
  have hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ') := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e₁ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'
    have e₂ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'
    rw [Ray.Φ_b] at e₁ e₂
    rw [hq] at e₂
    dsimp only [GlobalTheory.TorusModel.cv] at e₁ e₂
    rw [hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm] at e₂
    rw [map_mul]
    exact mul_right_cancel e₂
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this
  refine Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))
  exact congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)

theorem isWt_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  intro R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]
  ring

end GlobalTheory.Heat.WtMul
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtPres

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_div {α : Q.X} {V : Y.H.left.Opens} {f u u' : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hu : IsWt Y α V u)
    (h : u * u' = 1) : IsWt Y 0 V (f * u') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V u * valR b V u' = 1 := fun b hb => by
    rw [← WtAlg.valR_mul'' _ _ hb, h, WtAlg.valR_eq' _ _ hb, map_one, map_one]
  have e₁ := e a hV
  have e₂ := e a' hV'
  rw [hu S φ x x' c a a' ha ha' hV hV' hq hc] at e₂
  rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  linear_combination valR a V f * valR a V u' * e₂ - c α * valR a V f * valR a' V u' * e₁

end GlobalTheory.Heat.WtPres
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusInvariant_heatOperator_preserves_weight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  first | exact @GlobalTheory.Heat.WtAlg.op_isWt | exact GlobalTheory.Heat.WtAlg.op_isWt | (intros; apply GlobalTheory.Heat.WtAlg.op_isWt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  first | exact @GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | exact GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | (intros; apply GlobalTheory.Heat.WtLocal.isWt_of_basicOpen <;> assumption)
end
