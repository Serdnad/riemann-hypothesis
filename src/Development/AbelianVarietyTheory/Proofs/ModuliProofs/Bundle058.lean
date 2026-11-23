module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Mathlib.RingTheory.Trace.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsBundle

theorem res_constFn' {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a := by
  exact congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem res_appLE {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) {O O' : Y.Opens} {W W' : Y'.Opens}
    (hW : W' ≤ W) (hO : O' ≤ O) (h : W ≤ ρ ⁻¹ᵁ O) (h' : W' ≤ ρ ⁻¹ᵁ O') (a : Γ(Y, O)) :
    resG Y' hW ((ρ.appLE O W h).hom a) = (ρ.appLE O' W' h').hom (resG Y hO a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem eps_sq {X : Scheme.{0}} (p : X ⟶ Sp (DualNumber ℂ)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem decomp {Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (O : Y.Opens)
    (H : ∀ F : Γ(Y', ρ ⁻¹ᵁ O), ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2)
    (W : Y'.Opens) (hW : ρ ⁻¹ᵁ O = W) (h : W ≤ ρ ⁻¹ᵁ O) (F : Γ(Y', W)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.appLE O W h).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE O W h).hom ab.2 := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact H F

theorem uniq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {a b a' b' : A}
    (h : φ a + e * φ b = φ a' + e * φ b') : a = a' ∧ b = b' := by
  have := (H (φ a + e * φ b)).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl h
  exact Prod.mk.inj this

theorem unit_form {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) (u : Bˣ) :
    ∃ b b' c : A, b * b' = 1 ∧ (u : B) = φ b + e * φ c := by
  obtain ⟨⟨b, c⟩, h, -⟩ := H u
  obtain ⟨⟨b', c'⟩, h', -⟩ := H (u⁻¹ : Bˣ)
  refine ⟨b, b', c, ?_, h⟩
  have h1 : (u : B) * (u⁻¹ : Bˣ) = 1 := u.mul_inv
  rw [h', h] at h1
  refine (uniq φ e H (a := b * b') (b := b * c' + c * b') (a' := 1) (b' := 0) ?_).1
  simp only [map_mul, map_add (f := _), map_one, map_zero] at h1 ⊢
  linear_combination h1 - (φ c * φ c') * he

theorem overlap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {b b' c d d' c' k : A}
    (hb : b * b' = 1) (hd : d * d' = 1)
    (h : φ b + e * φ c = (1 + e * φ k) * (φ d + e * φ c')) : k = c * b' - c' * d' := by
  obtain ⟨h1, h2⟩ := uniq φ e H (a := b) (b := c) (a' := d) (b' := c' + k * d) (by
    simp only [map_mul, map_add (f := _)]
    linear_combination h + (φ k * φ c') * he)
  subst h1
  have h3 : b' = d' := by linear_combination d' * hb - b' * hd + (0 : A)
  subst h3
  linear_combination (-b') * h2 - k * hb

theorem trivial_iff_coboundary : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (Q : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → ((∃ t : Q.Gen, t.IsGen) ↔ ∃ a : ∀ i, Γ(Y, j ⁻¹ᵁ Q.U i), ∀ i i', k i i' = resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i from fun _ hy => hy.1) (a i) - resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' from fun _ hy => hy.2) (a i')) := by
  intro Y Y' q π ρ j hp hj hq Q k _ hg
  obtain ⟨hO, -, hD⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have H : ∀ (W : Y'.Opens) (F : Γ(Y', W)), ∃! ab : Γ(Y, j ⁻¹ᵁ W) × Γ(Y, j ⁻¹ᵁ W),
      F = (ρ.appLE _ W (le W)).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE _ W (le W)).hom ab.2 :=
    fun W F => decomp π ρ _ (hD _) W (hO W) (le W) F
  constructor
  · rintro ⟨t, ht⟩
    choose b b' c hb hs using fun i =>
      unit_form (ρ.appLE _ (Q.U i) (le _)).hom _ (eps_sq π _) (H (Q.U i)) (t.s i)
    refine ⟨fun i => c i * b' i, fun i i' => ?_⟩
    have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have E : resG Y' inf_le_left (t.s i : Γ(Y', Q.U i)) =
        (Q.g i i').val * resG Y' inf_le_right (t.s i' : Γ(Y', Q.U i')) := congrArg Units.val (ht i i')
    rw [hg i i' (le _), hs, hs, map_add (f := _), map_add (f := _), map_mul, map_mul, res_constFn', res_constFn',
      res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _),
      res_appLE ρ _ l₂ _ (le _)] at E
    rw [map_mul, map_mul]
    exact overlap _ _ (eps_sq π _) (H _) (by rw [← map_mul, hb, map_one])
      (by rw [← map_mul, hb, map_one]) E
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun i => ⟨1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i),
      1 - constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i), ?_, ?_⟩⟩, fun i i' => ?_⟩
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
      have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
      apply Units.ext
      change resG Y' inf_le_left (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i)) =
        (Q.g i i').val * resG Y' inf_le_right
          (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i') (le _)).hom (a i'))
      rw [hg i i' (le _), map_add (f := _), map_add (f := _), map_mul, map_mul, map_one, map_one, res_constFn', res_constFn',
        res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), ha i i', map_sub]
      linear_combination (-((ρ.appLE _ _ (le _)).hom (resG Y l₁ (a i)) -
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) * (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) *
        eps_sq π (Q.U i ⊓ Q.U i')

end GlobalTheory.KS.EpsBundle
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def RigAlong {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (ε : G' ⟶ G) (L : RigLB G) (L' : RigLB G') (w : LB.Iso L'.L (L.L.pull ε.left)) : Prop :=
  w.IsGen ∧ PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (𝟙 _)

variable {R : Type} [CommRing R] [IsDomain R]

def SameUnif {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G' G : Over (Sp R)}
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (ε : G' ≅ G)
    (U : UnifPre I D A G) (U' : UnifPre I D A G') : Prop :=
  U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧
    ∃ w : LB.Iso U'.LG.L (U.LG.L.pull ε.hom.left), RigAlong ε.hom U.LG U'.LG w ∧ ∀ e : ℕ,
      (U'.gt e).q = (Over.pullback (thick R I e)).map ε.hom ≫ (U.gt e).q ∧
      (∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ ((U'.gt e).t χ)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map ε.hom).left)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
        (jL' : U'.LG.L.ι), (U'.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
        ε.hom.left ((fstG I e G').left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
        gw (U'.w e) r z jM (fun _ => jL') =
          gw (U.w e) (r ≫ ((Over.pullback (thick R I e)).map ε.hom).left) z jM (fun _ => jL) *
            gw w (r ≫ (fstG I e G').left) z jL jL'

def IsIdPull {D : DegPre R} (hD : IsPullDeg (RingHom.id R) D D) : Prop :=
  (∀ x, hD.xe x = x) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ∧
    ∀ (Y : Scheme.{0}) (f : Y ⟶ D.P.A.left) (y : Y) (j k : D.P.L.ι), f y ∈ D.P.L.U j → f y ∈ D.P.L.U k →
      gw hD.w f y j k = gm f y _ (D.P.L.g j k)

theorem rigAlong_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by
  have he : eSec G ≫ (𝟙 G : G ⟶ G).left = 𝟙 _ ≫ eSec G := by simp
  exact ⟨(isGen_iff _).2 (isoPullId_pgen (idIso_isGen L.isLB) rfl),
    (maps_iff _ _ (fun _ => eSec G) _ L.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L) (fun _ => rfl)).1
      (isoPullId_maps (idIso_maps L) rfl rfl he)⟩

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.ProjClosure

theorem exists_isProjOver_isPullback_of_isLocalization {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (M : Submonoid O) [IsLocalization M R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsProjOver s) :
    ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'),
      IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) := by
  obtain ⟨N, c, hc, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)
  have hf : Flat (spMap (algebraMap O R)) := GlobalTheory.flat_specMap_localization M R
  have hm : Mono (spMap (algebraMap O R)) := GlobalTheory.mono_specMap_localization M R
  have hq : QuasiCompact (spMap (algebraMap O R)) := inferInstance
  have : Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) := MorphismProperty.of_isPullback P.flip hf
  have : Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    (MorphismProperty.monomorphisms _).of_isPullback P.flip hm
  have : QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    MorphismProperty.of_isPullback P.flip hq
  let j := c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)
  have H := GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl
  exact ⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩,
    H.flip.paste_vert P⟩

theorem exists_projective_closure : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (a : O) [IsLocalization.Away a R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'), IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) :=
  fun _ _ _ _ _ a _ _ s hs =>
    exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs

end GlobalTheory.ProjClosure
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  haveI : IsIso (PSpace.str R 0) := by
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      rw [GlobalTheory.ProjSpace.opensRange_chartι, ← GlobalTheory.ProjSpace.iSup_chart R 0]
      apply le_antisymm (le_iSup _ 0)
      apply iSup_le
      intro i
      rw [Subsingleton.elim i 0]
    haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0 ≫ PSpace.str R 0) := by
      rw [GlobalTheory.ProjSpace.chartι_str]
      exact inferInstanceAs (IsIso (Spec.map
        (MvPolynomial.isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
    exact IsIso.of_isIso_comp_left (GlobalTheory.ProjSpace.chartι R 0 0) _
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Point

end
end

section

noncomputable section

namespace GlobalTheory.DvrDataCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Ext

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Ext

section Move

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem psiUnitOn_of_ne_univ (D : DegPre R) (χ : D.X) {U : Set (Sp R)} (hU : U ≠ Set.univ) : PsiUnitOn D χ U := by
  intro j V _ hVU _ h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} e => ⟨1, by rw [IsFractionRing.injective R _ e]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (pow_ne_zero n hϖ.ne_zero))
    · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Rˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have e₁ : ϖ ^ n = (b : R) * (u⁻¹ : Rˣ) := by rw [hu, _root_.mul_right_comm, Units.mul_inv, _root_.one_mul]
      show z * algebraMap R _ (ϖ ^ n) = algebraMap R _ (a * (u⁻¹ : Rˣ))
      rw [e₁, map_mul, map_mul, ← _root_.mul_assoc]
      exact congrArg (· * _) e
  have : IsOpenImmersion (jK R) := IsOpenImmersion.of_isLocalization ϖ
  have hV : V ≤ (jK R).opensRange := by
    intro x hx
    have hx' : x ≠ closedPoint R := fun e => hU (Set.eq_univ_of_univ_subset (by
      have : V = ⊤ := (closedPoint_mem_iff V).1 (e ▸ hx)
      rw [this] at hVU
      exact hVU))
    have hb : x.asIdeal = ⊥ := by
      by_contra hb
      have := x.isPrime
      exact hx' (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hb)))
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    rw [hb]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  have := (jK R).isIso_app V hV
  have hb := ConcreteCategory.bijective_of_isIso ((jK R).app V)
  obtain ⟨r, hr⟩ := hb.2 (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
  refine ⟨r, ?_, hr⟩
  have hu : IsUnit (((jK R).app V).hom r) := by
    have : ((jK R).app V).hom r = _ := hr
    rw [this]
    exact (Units.isUnit _).map _
  exact (MulEquiv.isUnit_map (RingEquiv.ofBijective ((jK R).app V).hom hb)).1 hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

end GlobalTheory.DvrDataCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    GlobalTheory.T.torsion_local_presentation_smooth_group O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    GlobalTheory.T.exists_integral_of_local_presentation_pow O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (GlobalTheory.T.dvd_trace_of_tensor_lmul_eq O H Θ (ε l) hΘ h)

end GlobalTheory
end
