module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle558
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.MulLift

variable {S S' : Scheme.{0}}

theorem isPullback_tensor {A' B' : Over S'} {A B : Over S} {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsPullback f A'.hom A.hom b) (n : IsPullback g B'.hom B.hom b) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsPullback h (A' ⊗ B').hom (A ⊗ B).hom b := by
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A' B').left (snd A' B').left A'.hom B'.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← n.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert n
  rwa [Over.w, Over.w] at r

theorem smooth_tensor {X Y : Over S} (hX : Smooth X.hom) (hY : Smooth Y.hom) : Smooth (X ⊗ Y).hom := by
  haveI := hX
  haveI := hY
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    i ≫ (lift U V).left = (lift u v).left ≫ l := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_match {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀} {A : Over (Sp R₀)} [GrpObj A]
    {X : Over (Sp R)} {i : A.left ⟶ X.left} (h : IsPullback i A.hom X.hom (spMap π)) {e : Sp R ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 _) (hie : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A).left ≫ i = spMap π ≫ e) :
    i ≫ (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)).left = (1 : A ⟶ A).left ≫ i := by
  have e₁ : (1 : 𝟙_ (Over (Sp R₀)) ⟶ A) = η[A] := by simp [Hom.one_def]
  change _ = (toUnit A ≫ η[A]).left ≫ i
  rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left]
  change i ≫ X.hom ≫ e = (A.hom ≫ η[A].left) ≫ i
  rw [← Category.assoc i, h.w, Category.assoc, Category.assoc, ← e₁]
  exact congrArg (A.hom ≫ ·) hie.symm

end GlobalTheory.Obs.MulLift

namespace GlobalTheory.Obs


open MulLift in
theorem mul_lifts : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left),
    IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left),
    l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  intro hF hAx R R₀ _ _ I hI π hπ hk A₀ _ g hab hg X i h hX e he hie l hl₁ hl₂
  have hl : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := isPullback_tensor h h hl₁ hl₂
  have hsm : Smooth (X ⊗ X).hom := smooth_tensor hX hX
  obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
  obtain ⟨S', ⟨P'⟩⟩ :=
    GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (X ⊗ X).left (X ⊗ X).hom l hl hsm
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.T.exists_squareZeroAugmentedAlgebra R R₀ I hI π hπ hk
  have hh : (μ[A₀]).left ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀) := overW μ[A₀]
  have hlift : ∀ T : (Pair (μ[A₀]).left)ᵒᵖ,
      ∃ ρ : (ofSys S).B ((pairPull hh).G.obj T) →ₐ[R] (pairPre S' (μ[A₀]).left).B T,
        ∀ b, (pairPre S' (μ[A₀]).left).p T (ρ b) = (pairPull hh).α T ((ofSys S).p _ b) := fun T ↦ by
    haveI := (ofSys S).smooth ((pairPull hh).G.obj T)
    exact GlobalTheory.T.exists_lift_hom_of_reduction_squareZero_smooth R R₀ I hI π hπ hk _ _ ((ofSys S).p _) ((ofSys S).semi _) ((ofSys S).surj _)
      ((ofSys S).ker _) _ _ ((pairPre S' (μ[A₀]).left).p T) ((pairPre S' (μ[A₀]).left).semi T)
      ((pairPre S' (μ[A₀]).left).surj T) ((pairPre S' (μ[A₀]).left).ker T) (coefHom (pairPull hh) T)
  choose l₀ hl₀ using hlift
  have hL : (ofSys S).IsLift (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ := hl₀
  obtain ⟨Pp, Fa, -⟩ := hF R₀ A₀ g hab hg
  have hu : (lift (𝟙 A₀) 1).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one, Over.id_left]
  have hu' : (lift 1 (𝟙 A₀)).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul, Over.id_left]
  have hob : ∀ w, (ofSys S).IsOb1 (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeOneObstructionClass R R₀ I hI π hπ hk R₁ α _ _ _ _ (ofSys S) (pairPre S' (μ[A₀]).left) (pairPull hh)
      l₀ (ofSys_isFun S) ((ofSys_isFun S').restrict _) hL w
    obtain ⟨⟨-, hsurj⟩, -⟩ := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ _ _ (A₀ ⊗ A₀).hom (μ[A₀]).left).1
    obtain ⟨c', rfl⟩ := hsurj c
    have ax₁ : IsExtendedPullbackDegOne R₁ (overW (lift (𝟙 A₀) 1)) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift (𝟙 A₀) 1).left (overW _)
        (lift (𝟙 X) (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X))).left hu
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (by simp) (one_match h he hie)) l₀ hL w c' hc
    have ax₂ : IsExtendedPullbackDegOne R₁ (overW (lift 1 (𝟙 A₀))) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift 1 (𝟙 A₀)).left (overW _)
        (lift (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)) (𝟙 X)).left hu'
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (one_match h he hie) (by simp)) l₀ hL w c' hc
    have h0 : c' = 0 := hAx R₀ R₁ α.q α.sq A₀ g hab hg c' ax₁ ax₂
    subst h0
    simpa using hc
  obtain ⟨l', hL', hN'⟩ := GlobalTheory.T.lifts_natural_of_obstructionOne_zero R R₀ I hI π hπ hk R₁ α A₀.left A₀.hom Pp Fa _ _ (ofSys S)
    (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ hL hob
  obtain ⟨f, hfs, hfk⟩ := GlobalTheory.T.affinePairLifts_glue_to_morphism_of_lifts R R₀ I hI π hπ hk _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl
    S S' P P' (μ[A₀]).left hh l' hL' hN'
  exact ⟨Over.homMk f hfs, hfk⟩

end GlobalTheory.Obs
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.FracAway

variable (B : Type) [CommRing B] [IsDomain B]

structure Idx where

  val : B
  ne : val ≠ 0

instance : Preorder (Idx B) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val, mul_ne_zero a.ne b.ne⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (Idx B) := ⟨⟨1, one_ne_zero⟩⟩

variable {B}

theorem isUnit_of_dvd {a b : B} (h : a ∣ b) : IsUnit (algebraMap B (Localization.Away b) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b)

def tr {a b : B} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  Localization.awayLift (algebraMap B _) a (isUnit_of_dvd h)

theorem tr_comp {a b : B} (h : a ∣ b) : (tr h).comp (algebraMap B _) = algebraMap B _ :=
  IsLocalization.Away.lift_comp a (isUnit_of_dvd h)

theorem away_ext {a : B} {R : Type} [CommRing R] {f g : Localization.Away a →+* R}
    (h : f.comp (algebraMap B _) = g.comp (algebraMap B _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h


variable (B) in
def diag : Idx B ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (tr (leOfHom h : a.val ∣ b.val))
  map_id a := by
    ext1
    refine away_ext ?_
    simp [tr_comp]
  map_comp {a b c} f g := by
    ext1
    refine away_ext ?_
    simp [RingHom.comp_assoc, tr_comp]

def toFrac (a : Idx B) : Localization.Away a.val →+* FractionRing B :=
  Localization.awayLift (algebraMap B _) a.val
    (IsLocalization.map_units (FractionRing B) (⟨a.val, mem_nonZeroDivisors_of_ne_zero a.ne⟩ : nonZeroDivisors B))

theorem toFrac_comp (a : Idx B) : (toFrac a).comp (algebraMap B _) = algebraMap B (FractionRing B) :=
  IsLocalization.Away.lift_comp a.val
    (IsLocalization.map_units (FractionRing B) (⟨a.val, mem_nonZeroDivisors_of_ne_zero a.ne⟩ : nonZeroDivisors B))


variable (B) in
def cocone : Cocone (diag B) where
  pt := CommRingCat.of (FractionRing B)
  ι :=
    { app := fun a => CommRingCat.ofHom (toFrac a)
      naturality := fun a b h => by
        ext1
        refine away_ext ?_
        simp [diag, RingHom.comp_assoc, tr_comp, toFrac_comp] }

def idx1 : Idx B := ⟨1, one_ne_zero⟩

theorem desc_unit (s : Cocone (diag B)) (y : nonZeroDivisors B) :
    IsUnit (((s.ι.app idx1).hom.comp (algebraMap B (Localization.Away (1 : B)))) y) := by
  let b : Idx B := ⟨y.1, nonZeroDivisors.ne_zero y.2⟩
  have hw := s.w (homOfLE (show (idx1 : Idx B) ≤ b from one_dvd _))
  rw [← hw]
  change IsUnit ((s.ι.app b).hom ((tr (one_dvd y.1)) (algebraMap B _ y.1)))
  rw [← RingHom.comp_apply (tr _), tr_comp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.1) y.1).map (s.ι.app b).hom


variable (B) in
def isColim : IsColimit (cocone B) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s))
  fac s a := by
    have hw := s.w (homOfLE (show (idx1 : Idx B) ≤ a from one_dvd _))
    ext1
    change (IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s)).comp (toFrac a) = (s.ι.app a).hom
    refine away_ext ?_
    rw [RingHom.comp_assoc, toFrac_comp, IsLocalization.lift_comp, ← hw]
    ext b
    exact congrArg (s.ι.app a).hom (DFunLike.congr_fun (tr_comp (one_dvd a.val)) b)
  uniq s m hm := by
    ext1
    change m.hom = IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s)
    refine IsLocalization.ringHom_ext (S := FractionRing B) (nonZeroDivisors B) ?_
    rw [IsLocalization.lift_comp, ← hm idx1]
    ext b
    exact congrArg m.hom (DFunLike.congr_fun (toFrac_comp idx1) b).symm

theorem spMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC.FracAway

open GlobalTheory.EtC.FracAway in
theorem GlobalTheory.EtC.classVanishesAway : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) →
    ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 →
    ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q B _ _ hF hq n i x hx
  have hB1 := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag B) (cocone B) (isColim B) n i).2
  have hq1 : IsUnit (q : Localization.Away (idx1 : Idx B).val) := by
    have := hq.map (algebraMap B (Localization.Away (idx1 : Idx B).val))
    rwa [map_natCast] at this
  have h2 : pull _ (spMap (toFrac (idx1 : Idx B))) _ _
      (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) = 0 := by
    rw [← pull_comp, ← spMap_comp, toFrac_comp]
    exact hx
  obtain ⟨k, f, hk⟩ := hB1 idx1 (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) hq1 h2
  obtain ⟨g, hg0, hgu⟩ := Ring.exists_not_isUnit_of_not_isField hF
  have hf : (idx1 : Idx B).val ∣ k.val := leOfHom f
  refine ⟨k.val * g, mul_ne_zero k.ne hg0, fun hu => hgu (isUnit_of_mul_isUnit_right hu), ?_⟩
  have e : algebraMap B (Localization.Away (k.val * g)) =
      (tr (dvd_mul_right k.val g)).comp ((tr hf).comp (algebraMap B (Localization.Away (idx1 : Idx B).val))) := by
    rw [tr_comp, tr_comp]
  rw [e, spMap_comp, pull_comp, spMap_comp, pull_comp]
  have hk' : pull _ (spMap (tr hf)) _ _
      (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) = 0 := hk
  rw [hk', map_zero]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumZero

theorem isUnit_top {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have x' : U ⟶ X := x
  simpa using hX.map x'.appTop.hom

theorem unitSec_injective {X : Scheme.{0}} : Function.Injective (unitSec (U := X)) := by
  intro a b h
  have := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).1 h
  simpa using congrArg (fun z => Additive.toMul z.down) this

theorem unitSec_surjective {X : Scheme.{0}} (b : Sec Gm X) : ∃ v, unitSec v = b := by
  obtain ⟨w, hw⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).2 b
  exact ⟨Additive.toMul w.down, hw⟩

theorem sec_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (n : ℤ) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (n • φ) x = n • Sec.map φ x := by
  have h : (n • φ).hom = n • φ.hom := (sheafToPresheaf _ _).map_zsmul (X := F) (Y := G) (f := φ) (r := n)
  unfold Sec.map
  rw [h, NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]

theorem smul_unitSec (n : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) : (n : ℤ) • unitSec v = unitSec (v ^ n) := by
  unfold unitSec ofRings.sec
  refine (map_zsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op X))) (n : ℤ)
    (show (Scheme.Γ ⋙ unitsF).obj (op X) from ⟨Additive.ofMul v⟩)).symm.trans ?_
  congr 1

theorem map_q_unitSec (q : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) :
    Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) = unitSec (v ^ q) := by
  rw [sec_map_zsmul, ← smul_unitSec]
  rfl

theorem _root_.GlobalTheory.EtC.eq_pow_of_kum_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  intro q _ A _ hq u hu
  have hX := isUnit_top hq
  obtain ⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have h1 : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
    rw [hs _ u hX, hu, smul_zero]
  obtain ⟨y, hy⟩ := ((hex _ (inv_sch hX) 0).1 _).1 h1
  have hsc := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hsc.2.1.2 y
  rw [hsc.2.2.2.2] at hy
  have hb := hsc.2.1.1 hy
  obtain ⟨v, rfl⟩ := unitSec_surjective b
  rw [map_q_unitSec] at hb
  exact ⟨v, (unitSec_injective hb).symm⟩

end GlobalTheory.EtC.KumZero
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumSurj

theorem unitSec_mul' {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec
  exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_surj {U : Scheme.{0}} (b : Sec Gm U) : ∃ u : (Γ(U, ⊤))ˣ, unitSec u = b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective U).2 b
  exact ⟨Additive.toMul y.down, hy⟩

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := by
  intro U ⟨x⟩
  have h1 : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using h1.map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom

end GlobalTheory.EtC.KumSurj


open GlobalTheory.EtC.KumSurj in
theorem GlobalTheory.EtC.kum_surjective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  intro q _ A _ hq hp x
  obtain ⟨κ, hκ, bd, hbd, hex, ⟨s, hs⟩, hlast⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have hE : Inv q (sp A) := inv_sp q A hq
  have hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨_, h2, h3⟩ := hex (sp A) hE 0
  obtain ⟨_, _, _, hpc, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  obtain ⟨hpid, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  set y := HK.post ℤ ((chains ℤ).obj (sp A)) κ (0 + 1) (restrH (Int.castRingHom (ZMod q)) (sp A) (tw q 1) (0 + 1) x) with hy
  have hqy : (q : ℤ) • y = 0 := by
    have := (h3 y).2 ⟨x, rfl⟩
    rw [hpc, hpid] at this
    exact this
  have hy0 : y = 0 := by
    obtain ⟨e⟩ := GlobalTheory.T.etale_descent_picard_group A
    have h1 : (q : ℤ) • e y = 0 := by rw [← map_zsmul, hqy, map_zero]
    have h2' : (Additive.toMul (e y)) ^ q = 1 := by
      have := congrArg Additive.toMul h1
      rw [natCast_zsmul, toMul_nsmul] at this
      exact this
    have := hp _ h2'
    apply e.injective
    rw [map_zero]
    exact congrArg Additive.ofMul this
  obtain ⟨g, hg⟩ := (h2 x).1 hy0
  obtain ⟨-, hbij, hadd, -, -⟩ := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hbij.2 g
  obtain ⟨u, rfl⟩ := unitSec_surj b
  have hsu := hs _ u hqX
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨u, by rw [← hg, hsu, one_smul]⟩
  · refine ⟨u⁻¹, ?_⟩
    have hsi := hs _ u⁻¹ hqX
    have hsum : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u⁻¹)) +
        bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
      rw [← map_add (f := _), ← hadd, ← unitSec_mul', inv_mul_cancel]
      have h0 : unitSec (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) = 0 := by
        have := unitSec_mul' (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1
        rw [mul_one] at this
        exact (left_eq_add.1 this)
      have h00 : secClass Gm (0 : Sec Gm (Spec (CommRingCat.of A))) = 0 := by
        have := hadd 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0, h00, map_zero]
    rw [hsi, hsu, Units.neg_smul, Units.neg_smul, one_smul, one_smul] at hsum
    rw [← hg, hsu, Units.neg_smul, one_smul]
    rw [← neg_add] at hsum
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.1 hsum)
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LiftSys.summand_of_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S' hS' hN S
  obtain ⟨N, hN⟩ := hN
  obtain ⟨hinf, hfull⟩ := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const S' S
  have hS : S.Full hI := hfull hS'
  have hsup : S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    ext c
    rw [GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hS c, GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S' hρ hS' c]
  exact ⟨⟨N, (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S.K hI) N hN hsup).1 hinf.symm⟩, hsup⟩
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_generic_member_linearSystem : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  first | exact @GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | exact GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | (intros; apply GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme <;> assumption)
end
