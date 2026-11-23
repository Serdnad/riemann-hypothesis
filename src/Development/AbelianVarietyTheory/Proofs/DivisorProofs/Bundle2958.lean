module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegResc

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_le {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) {W : (Sp R₀).Opens}
    (hle : W ≤ (Sp R₀).basicOpen (fnSp R₀ f)) : IsUnit (fnOn W r) := by
  have e := appTop_fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) (RingHom.id R₀) ((Sp R₀).homOfLE hle) W.ι (by
    rw [Scheme.homOfLE_ι]
    exact (Category.comp_id _).symm.trans (congrArg (W.ι ≫ ·) (Spec.map_id _).symm)) r
  have := (isUnit_fnOn f r N hr).map ((Sp R₀).homOfLE hle).appTop.hom
  rw [e] at this
  exact this

theorem gm_mono {R₀ K : Type} [CommRing R₀] [Field K] (W : (Sp R₀).Opens) (α : R₀ →+* K) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp K) (h : t ≫ W.ι = s ≫ spMap α) {I : Type} [Fintype I] (a : I → R₀)
    (ha : ∀ k, IsUnit (fnOn W (a k))) (h0 : ∀ k, α (a k) ≠ 0) (n : I → ℤ) (v : Kˣ)
    (hv : (v : K) = ∏ k, α (a k) ^ n k) (z : Z) :
    gm t z ⊤ (∏ k, (ha k).unit ^ n k) = gm s z ⊤ (unitOn v) := by
  obtain rfl : v = ∏ k, Units.mk0 (α (a k)) (h0 k) ^ n k := Units.ext (by
    rw [hv]; simp)
  show _ = GlobalTheory.TauTwist.unitAt s z _
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ n k) (gm_fnOn W α t s h (a k) _ _ (ha k).unit_spec rfl z)

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ)
    (hu : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (s : Z ⟶ (TK R₀).left), t ≫ W'.ι = s ≫ jK R₀ → ∀ z,
      gm t z ⊤ (u y) = gm s z ⊤ (unitOn (κ₀ y))) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine hu y _ _ ?_ z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

theorem exists_rescale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀) (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  classical
  have hf : φ (∏ k, s k) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set f := ∏ k, s k with hfd
  set W' : (Sp R₀).Opens := h.W ⊓ (Sp R₀).basicOpen (fnSp R₀ f) with hW'
  have hsq : jK R ≫ specOf φ = 𝟙 (TK R).left ≫ spMap ((algebraMap R (FractionRing R)).comp φ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R (FractionRing R)))).symm
  have hpre : (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    rw [hsq]
    refine (congrArg IsUnit (appTop_comp_spMap ((algebraMap R (FractionRing R)).comp φ) (𝟙 _) f)).mpr ?_
    exact ((IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)).map (fnSp _)).map
      (Scheme.Hom.appTop (𝟙 (Sp (FractionRing R)))).hom
  obtain ⟨g, hg⟩ : ∃ g : (TK R).left ⟶ (TW W').left, g ≫ W'.ι = jK R ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W'.ι (jK R ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, (show y ∈ (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) from hpre.ge trivial)⟩
      rw [← h.g_comm]
      exact (h.g y).2), IsOpenImmersion.lift_fac _ _ _⟩
  have hle : W' ≤ h.W := inf_le_left
  have hU : ∀ k, IsUnit (fnOn W' (s k)) := fun k =>
    isUnit_fnOn_le f _ 1 (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) inf_le_right
  have s0 : ∀ k, algebraMap R₀ (FractionRing R₀) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R₀ _)).2 fun e => hs k (by rw [e, map_zero])
  obtain ⟨ψW, hψW⟩ := exists_psiOn_rescale D₁ κ₀ h.psiW hle (fun y => ∏ k, (hU k).unit ^ n y k)
    (fun y Z t r e z => gm_mono W' (algebraMap R₀ (FractionRing R₀)) t r e s hU s0 (n y) _ (h₀ y) z)
  have hgm : g ≫ (Sp R₀).homOfLE hle = h.g := by
    rw [← cancel_mono h.W.ι, Category.assoc, Scheme.homOfLE_ι, hg, h.g_comm]
  have hv : ∀ (x : D.X) (z : (TK R).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' :=
    fun x z J J' hJ hJ' => by
    rw [hψW _ g z J hJ, hgm]
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' =
        gm (𝟙 (TK R).left) z ⊤ (unitOn (κ x)) * val (D.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (κ x)) (D.psi x) (𝟙 _) hJ'
    have e3 := gm_mono W' ((algebraMap R (FractionRing R)).comp φ) g (𝟙 _) (by rw [hg, hsq]) s hU
      (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs k)) (n (h.xe x)) (κ x) (h₁ x) z
    rw [e3, e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap φ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap φ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : D.X, (D.c x).left ≫ proj h = spMap φ ≫ (D₁.c (h.xe x)).left := h.c_pr
  have hw : PGen h.w := (isGen_iff h.w).1 h.w_gen
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale D₁ κ₀)
    (GlobalTheory.PolDeg.rescale D κ) ψW g hg gp h.w hw hr h.xe hc hv
  exact ⟨hD, k₁, k₂⟩

theorem rescale_inv {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (x : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi x = D.psi x :=
  GlobalTheory.TorusExt.gen_ext_val D.P.isLB ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi_gen x)
    (D.psi_gen x) fun y J hJ => by
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (GlobalTheory.UU.val_scaleGen _ _ _ hJ)).trans ?_)
      show GlobalTheory.TauTwist.unitAt _ y (g x)⁻¹ * (GlobalTheory.TauTwist.unitAt _ y (g x) * _) = _
      rw [map_inv, inv_mul_cancel_left]

theorem exists_withPsi {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (ψ₁ : GlobalTheory.TauTwist.PsiFam D₁) (g₁ : ∀ χ, (ψ₁ χ).IsGen)
    (ψ : GlobalTheory.TauTwist.PsiFam D) (g : ∀ χ, (ψ χ).IsGen) (e₁ : D₁.psi = ψ₁) (e : D.psi = ψ) :
    ∃ h' : IsPullDeg φ (GlobalTheory.TauTwist.withPsi D₁ ψ₁ g₁) (GlobalTheory.TauTwist.withPsi D ψ g),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  subst e₁ e
  exact ⟨h, rfl, fun _ => rfl⟩

theorem exists_unscale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ)
    (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀)
    (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) =
      ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ D₁ D, proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  obtain ⟨h₂, a₁, a₂⟩ := exists_rescale h (fun y => (κ₀ y)⁻¹) (fun y => (κ y)⁻¹) s hs n h₀ h₁
  obtain ⟨h₃, b₁, b₂⟩ := exists_withPsi h₂ D₁.psi D₁.psi_gen D.psi D.psi_gen (funext (rescale_inv D₁ κ₀))
    (funext (rescale_inv D κ))
  exact ⟨h₃, b₁.trans a₁, fun x => (b₂ x).trans (a₂ x)⟩

theorem exists_rescale_inv {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ) :
    ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x :=
  exists_withPsi h D₁.psi D₁.psi_gen _ ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹).psi_gen) rfl
    (funext (rescale_inv D κ)).symm

theorem main : (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ D₁ D, h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ), ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) :=
  ⟨fun h κ₀ κ _ _ s hs n h₀ h₁ => exists_rescale h κ₀ κ s hs n h₀ h₁,
    fun κ₀ κ h _ _ s hs n h₀ h₁ => exists_unscale κ₀ κ h s hs n h₀ h₁, fun h κ => exists_rescale_inv h κ⟩

end GlobalTheory.PullDegResc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem exists_trait_point {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x : M.S)
    (hx : M.π x = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x := by
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have := M.proper
  have := M.integral
  have := M.dominant
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (M.S.fromSpecStalk x ≫ M.π)
  have hψp : ∀ q : Spec (M.S.presheaf.stalk x), Spec.map ψ q = M.π (M.S.fromSpecStalk x q) := fun q => by
    rw [hψ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom ψ.hom := by
    rw [isLocalHom_iff_comap_closedPoint]
    have := hψp (closedPoint _)
    rw [Scheme.fromSpecStalk_closedPoint, hx] at this
    exact this

  let t₀ : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : M.gp t₀ ⤳ x := by
    rw [specializes_iff_mem_closure]
    have h1 : Set.range M.gp ⊆ {M.gp t₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t t₀]; rfl
    exact closure_mono h1 ((IsDominant.denseRange (f := M.gp)).closure_eq ▸ Set.mem_univ x)
  have hr : M.gp t₀ ∈ Set.range (M.S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  obtain ⟨q, hq⟩ := hr
  have e1 : Spec.map ψ q = jK R t₀ := by
    rw [hψp, hq, ← Scheme.Hom.comp_apply, M.gp_π]
  have h2 : Ideal.comap ψ.hom q.asIdeal = ⊥ := by
    have := congrArg (fun p : Sp R => (p : PrimeSpectrum R).asIdeal) e1
    change Ideal.comap ψ.hom q.asIdeal = Ideal.comap (algebraMap R (FractionRing R)) t₀.asIdeal at this
    rw [this, @Ideal.eq_bot_of_prime _ _ t₀.asIdeal t₀.isPrime]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  have hinj : Function.Injective ψ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap ψ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact q.asIdeal.zero_mem
    rw [h2] at this
    exact this
  have : CharZero (M.S.presheaf.stalk x) := charZero_of_injective_ringHom hinj
  have key : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : M.S.presheaf.stalk x →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective χ ∧ IsLocalHom χ := by
    by_cases h : IsField (M.S.presheaf.stalk x)
    · letI := h.toField
      refine ⟨PowerSeries (M.S.presheaf.stalk x), inferInstance, inferInstance, inferInstance, PowerSeries.C,
        ⟨inferInstance, ?_, ?_⟩, PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := M.S.presheaf.stalk x)) (RingHom.injective _)
    · obtain ⟨O, _, _, _, _, χ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating _ h
      have : CharZero O := charZero_of_injective_ringHom h1
      exact ⟨O, inferInstance, inferInstance, inferInstance, χ, ⟨inferInstance, inferInstance, inferInstance⟩, h1, h2⟩
  obtain ⟨W, _, _, _, χ, hW, hχ, hχl⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, χ.comp ψ.hom, Spec.map (CommRingCat.ofHom χ) ≫ M.S.fromSpecStalk x,
    hW, hχ.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]; rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint χ)) Scheme.fromSpecStalk_closedPoint)

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem mem_embH_of_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s := by
  intro R _ _ _ hR M G _ _ B L _ _ N s θ Y _ _ j _ _ O hT g hg
  obtain ⟨W, _, _, _, φ, ξ, hW, hφ, hl, hξ, hξx⟩ := exists_trait_point hR M (G.hom g) hg
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hfin, hcart, -, -, hpts⟩ := hT W hW φ ξ hφ hl hξ
  have hiol : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hfin
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  have hc : (spMap io ≫ ξ) (closedPoint W') = G.hom g :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ (IsLocalRing.comap_closedPoint io)).trans hξx)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') hc.symm
  have hg1 : β (hcart.1.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (hcart.1.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_snd, hz2]
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (hcart.1.isoPullback.inv z) (closedPoint (ResidueField W'))
    (hg2.trans (IsLocalRing.comap_closedPoint (residue W')).symm)
  let F := ((Over.pullback (spMap (residue W'))).obj G').left
  let q' : F := q
  obtain ⟨⟨hs, -⟩, -⟩ := hpts (F.residueField q') (F.fromSpecResidueField q')
    (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W')))
    (F.fromSpecResidueField q' ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ)) rfl rfl
  have hm : closedPoint (F.residueField q') ∈
      ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)) := by
    rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  rw [GlobalTheory.nonzeroLocus_secPull] at hi
  have hpt : ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)
      (closedPoint (F.residueField q')) = g := by
    have h1 : (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) (closedPoint (F.residueField q')) =
        hcart.1.isoPullback.inv z :=
      (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (pullback.fst G'.hom (spMap (residue W'))) (Scheme.fromSpecResidueField_apply q' _)).trans hq1)
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg β h1).trans hg1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← hpt]
  exact hi

end GlobalTheory.Mum.SecEmb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem sec_eq_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W).hom)
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) : s = s' := by
  have e : ∀ j, s.f j = s'.f j := fun j => by
    refine hinj _ (fn_ext fun y hy => ?_)
    choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
    have m := hJ'.mem φ (𝟙 Y' ≫ h)
    refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
    exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)
  cases s
  cases s'
  congr
  exact funext e

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem traitRed_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    ∀ σ : Fin (Sc.N + 1) → SecK C.P.L.L β Sc.k, (∀ i, Agree C.P.L.L (σ i) (Sc.s i)) →
    ∀ θ₀ : SecK C.P.L.L β 1, Agree C.P.L.L θ₀ Sc.θ →
    ∃ θ : C'.P.L.L.Sec, GlobalTheory.Mum.SecEmb.TraitRed C'.toModif C'.G σ θ Sc.Y Sc.j Sc.O := by
  intro R _ _ _ _ D C C' Sc h β hπ hpb hiso σ hσ θ₀ hθ₀
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  obtain ⟨θ₁, hθ₁⟩ := exists_sec hL (φ := fun _ : Fin 1 => β) (ε := fun _ => ((1 : ℕ) : ℤ))
    (φ' := fun _ : PUnit => β) (ε' := fun _ => 1) (fun U _ g => by simp) θ₀
  obtain ⟨w, hw⟩ := hiso
  refine ⟨DVR.secOfIso (u := w) θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β), ?_⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, β'', σ'', θ'', κ, e, hW', hio, hfin, hG'', hκ, he, hσ'', hθ'', hfib⟩ :=
    Sc.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  obtain ⟨β', hβ'1, hβ'2⟩ : ∃ β' : G''.left ⟶ C'.G.left, β' ≫ β = β'' ∧ β' ≫ C'.G.hom = G''.hom ≫ spMap io ≫ ξ :=
    ⟨hpb.1.lift β'' (G''.hom ≫ spMap io ≫ ξ) (by rw [hG''.1.w]; simp), hpb.1.lift_fst _ _ _, hpb.1.lift_snd _ _ _⟩
  subst hβ'1

  have hρ : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' (FractionRing W')).comp (hio.comp hφ)
  obtain ⟨ga, -, hga⟩ := Modif.factor_gp R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ ≫ h) hρ (by
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)

  have : Smooth C.G.hom := C.semi.smooth
  have : Flat G''.hom := MorphismProperty.of_isPullback (P := @Flat) hG''.1 inferInstance

  have hgen : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G''.hom (jK W')), ∃ q : Z ⟶ C.A.A.left,
      q ≫ C.α = r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β := fun Z r => by
    refine ⟨C.α_cart.1.lift (r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β)
      (r ≫ pullback.snd G''.hom (jK W') ≫ spMap ga) ?_, C.α_cart.1.lift_fst _ _ _⟩
    have w₁ := hG''.1.w
    simp only [Category.assoc] at w₁ ⊢
    rw [w₁, ← hga, pullback.condition_assoc]

  have key : ∀ {n : ℕ} (a : SecK C.P.L.L (β' ≫ β) n) (b : SecK C.P.L.L β n) (c : SecK C.P.L.L C.α n),
      Agree C.P.L.L a c → Agree C.P.L.L b c → ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
        sval a r z J = sval b (r ≫ β') z J := by
    intro n a b c ha hb
    have e₁ : a = ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec b β' := by
      refine sec_eq_of_inj hL (GlobalTheory.ExpInt.generic_app_injective G'') fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
      obtain ⟨q, hq⟩ := hgen _ (𝟙 _)
      have hq' : q ≫ C.α = (𝟙 _ ≫ pullback.fst G''.hom (jK W')) ≫ β' ≫ β := by rw [hq]; simp
      refine (ha _ _ q hq'.symm y J hJ).trans (hb _ _ q ?_ y J hJ).symm
      rw [hq']; simp
    intro Z r z J hJ
    rw [e₁, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
      sval (σ'' i) r z J = sval (σ i) (r ≫ β') z J := fun i => key _ _ _ (hσ'' i) (hσ i)
  have hvθ := key _ _ _ hθ'' hθ₀
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, β', κ, e, hW', hio, hfin,
    IsGrpPullback.cancel hpb (by rw [Category.assoc]; exact hG'') hβ'2, hκ, he, ?_⟩
  intro Ω _ p p' y hp hy
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := hfib Ω p p' y hp hy
  have hnzi : ∀ (x : Sp Ω) i, p' x ∈ nonzeroLocus (σ'' i) ↔ (p' ≫ β') x ∈ nonzeroLocus (σ i) := fun x i => by
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hv i _ _ _ _ hJ]
  have ht : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) (p' ≫ β')) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    rw [GlobalTheory.nonzeroLocus_secPull] at hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact (hnzi x i).1 hi
  refine ⟨⟨ht, ?_⟩, fun x hx => ?_⟩
  · rw [← hproj]
    refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs ht fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart hL ((p' ≫ β' ≫ β) x)
    have m₁ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    have m₂ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    refine ⟨(LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U (fun _ => fun _ => c) ⊓
      (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U (fun _ => fun _ => c),
      ⟨m₁, m₂⟩, _, inf_le_left, _, inf_le_right, 1, fun j => ?_⟩
    rw [_root_.one_mul]
    refine fn_ext fun z hz => ?_
    have hz' : (p' ≫ β' ≫ β) z ∈ C.P.L.L.U c := by
      have := Set.mem_iInter.1 (mem_pull.1 hz.1) 0
      simpa using this
    obtain ⟨J, hJ, eJ⟩ := exists_good C.P.L.L hL z (fun _ : PUnit => p' ≫ β' ≫ β) (fun _ => c)
      (fun _ _ _ => rfl) (fun _ => hz')
    rw [gs_res _ _ _ hz, gs_res _ _ _ hz]
    refine (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ j) (𝟙 _) z _ hz.2).trans
      (Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ'' j) (𝟙 _) z _ hz.1).symm)
    rw [Category.id_comp, Category.id_comp]
    exact (sval_of (σ j) (p' ≫ β') z J (fun _ => c) (fun _ => by rw [Category.assoc]; exact eJ ⟨⟩)).symm.trans
      ((hv j _ _ _ _ hJ).symm.trans (sval_of (σ'' j) p' z J (fun _ => c) (fun _ => eJ ⟨⟩)))
  · have h₁ := hnz x hx
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hvθ _ _ _ _ hJ] at h₁
    refine DVR.nonzeroLocus_secOfIso w θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β) ?_
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hθ₁ _ _ _ _ hJ]
    exact h₁

end GlobalTheory.Mum.SecEmb
end
end
