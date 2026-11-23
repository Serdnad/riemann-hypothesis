module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle134
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.torsionPairing_values_of_familiesValues : BrGtSt → BrFamSt → BrWpSt := by
  first | exact @GlobalTheory.WeilValues.weil_eq_values | exact GlobalTheory.WeilValues.weil_eq_values | (intros; apply GlobalTheory.WeilValues.weil_eq_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.torus_torsion_points_correspond_values : BrGtSt := by
  first | exact @GlobalTheory.Ex.GtValues.points_correspond | exact GlobalTheory.Ex.GtValues.points_correspond | (intros; apply GlobalTheory.Ex.GtValues.points_correspond <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  first | exact @GlobalTheory.fibNZ_prod_and_baseChange | exact GlobalTheory.fibNZ_prod_and_baseChange | (intros; apply GlobalTheory.fibNZ_prod_and_baseChange <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.AbelianTrait

theorem isProper_snd_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (hp : t p ∈ abLocus G) : IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Sp K' := (default : PrimeSpectrum K')
  have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
  have h₁ := hp K' (u ≫ t) ⟨q, e⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₃ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]
    infer_instance
  have : Nonempty (Sp K') := ⟨q⟩
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₃
  exact ⟨⟩

theorem nonempty_pelUnif_of_abLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  intro hU E _ _ _ H S t W _ _ _ hW χ t' m hpol hr
  have hG := t'.semi
  have := hG.smooth
  have := hG.separated
  let r : Sp (W ⧸ maximalIdeal W) ⟶ Sp W := spMap (Ideal.Quotient.mk (maximalIdeal W))
  have p : Sp (W ⧸ maximalIdeal W) := (default : PrimeSpectrum (ResidueField W))
  have h₀ : r p ∈ abLocus t'.G := (abLocus_pullback abLocusOne t.semi m.cart.1 (r p)).1 (hr ⟨_, rfl⟩)
  have h₁ : IsProper (pullback.snd t'.G.hom r) := isProper_snd_of_mem_abLocus t'.G (K := ResidueField W) r p h₀
  have := hG.comm
  have := hG.geomConnected
  obtain ⟨P, -⟩ := hU E H W hW t' hpol
    ⟨_, ZJ.isGt_splitExtOfAbelian _ ⟨inferInstance, by
      change Smooth (pullback.snd t'.G.hom r)
      infer_instance, h₁, by
      change GeometricallyConnected (pullback.snd t'.G.hom r)
      infer_instance⟩⟩
  exact ⟨P⟩

end GlobalTheory.AbelianTrait
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arc_generic_point_extends_powerSeries : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  first | exact @GlobalTheory.LN.ArcExtends.exists_extension | exact GlobalTheory.LN.ArcExtends.exists_extension | (intros; apply GlobalTheory.LN.ArcExtends.exists_extension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) → ∃ (B : Over (Sp k)) (_ : GrpObj B) (q : G ⟶ B), IsQuot i q ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  first | exact @GlobalTheory.TorusQuotientGlue.main | exact GlobalTheory.TorusQuotientGlue.main | (intros; apply GlobalTheory.TorusQuotientGlue.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.LN.homExt_of_laws : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → _root_.GlobalTheory.LN.HomExtSt := by
  intro _ _
  unfold _root_.GlobalTheory.LN.HomExtSt
  exact _root_.GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (_root_.GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion
      (_root_.GlobalTheory.UU.TorsionCount.card_torsion_points _root_.GlobalTheory.globalFns_holds
        _root_.GlobalTheory.rigidity_holds))

end GlobalTheory.LN
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.KerCut

theorem hom_ext_of_appLE {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by
  have : IsAffine V.toScheme := hV
  have r : ∀ (f : Y ⟶ X), ⊤ ≤ f ⁻¹ᵁ V → ∃ f' : Y ⟶ V.toScheme, f = f' ≫ V.ι := by
    intro f hf
    refine ⟨IsOpenImmersion.lift V.ι f ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hf (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨f', ef⟩ := r f hf
  obtain ⟨g', eg⟩ := r g hg
  rw [← GlobalTheory.FunDescent.res_comp_appTop V f' f ef, ← GlobalTheory.FunDescent.res_comp_appTop V g' g eg] at e
  have : f' = g' := by
    apply ext_of_isAffine
    ext x
    obtain ⟨y, rfl⟩ := (GlobalTheory.FunDescent.res_bijective V).2 x
    exact congrArg (fun ψ => ψ.hom y) e
  rw [ef, eg, this]

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (k : Z ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ q ⁻¹ᵁ V) (h' : ⊤ ≤ k ⁻¹ᵁ W) (p : Z ⟶ X) (e : k ≫ q = p) (h'' : ⊤ ≤ p ⁻¹ᵁ V) (v : Γ(X, V)) :
    (k.appLE W ⊤ h').hom ((q.appLE V W h).hom v) = (p.appLE V ⊤ h'').hom v := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE k q V W ⊤ h h']
  rfl

end GlobalTheory.ZJ.KerCut

namespace GlobalTheory.ZJ

theorem Charts.kerIs_of_torus : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  intro K _ H _ _ _ _ _ C d c i a j hc hT hB
  obtain ⟨B, _, q, -, hq, -, -, -, hP, hV⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  obtain ⟨V, hW, hVa, hu⟩ := hV a
  have one_mem : ∀ Y : Over (Sp K), ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := by
    intro Y y _
    exact hB.1 (show (toUnit Y).left y ∈ (⊤ : (Sp K).Opens) from trivial)
  refine ⟨⟨fun {Y} s t e => hP.hom_ext e (toUnit_unique _ _)⟩, fun Y k => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, h₁, hr⟩
    have key : k ≫ q = (1 : Y ⟶ H) ≫ q := by
      apply Over.OverMorphism.ext
      have m : ∀ g : Y ⟶ H, ⊤ ≤ g.left ⁻¹ᵁ C.W a → ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := by
        intro g hg
        rw [hW] at hg
        exact hg
      refine KerCut.hom_ext_of_appLE V hVa _ _ (m k h) (m 1 h₁) ?_
      ext v
      have hv := hT.gen a _ ((hu _).2 ⟨v, rfl⟩)
      have eq := RingHom.eqOn_set_closure (f := (k.left.appLE _ ⊤ h).hom)
        (g := ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom) (by
          rintro u (⟨w, rfl⟩ | ⟨j', hj', rfl⟩)
          · exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w k) le_rfl w).trans
              (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w _) le_rfl w).symm
          · exact hr j' hj') hv
      exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m k h) v).symm.trans
        (eq.trans (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m 1 h₁) v))
    have w : k ≫ q = toUnit Y ≫ η[B] := by
      rw [key, MonObj.one_comp]
      rfl
    exact ⟨hP.lift _ _ w, (hP.lift_fst _ _ w).symm⟩
  · rintro ⟨t, rfl⟩
    have h' := hT.stable a Y t 1 (one_mem Y)
    have hr := fun j' hj' => hT.inv a j' hj' Y t 1 (one_mem Y) h'
    revert h' hr
    rw [_root_.mul_one]
    intro h' hr
    refine ⟨h', one_mem Y, fun j' hj' => ?_⟩
    rw [hr j' hj', charUnit_zero_val, map_one, _root_.one_mul]
  · intro Y t n h h₁
    have := hT.wt a (j n) n (hB.2 n).1 Y t 1 h₁
    rw [_root_.mul_one] at this
    exact this h

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.IndepFib

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩

  rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem change_mul_change {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} [Fintype J]
    {A : Subalgebra o Ω} {B B' C : Matrix J J Ω} (hC : C * B' = 1) {g g' : Matrix J J A}
    (h : B' = g.map (↑) * B) (h' : B = g'.map (↑) * B') : g * g' = 1 := by
  have h1 : B' * C = 1 := mul_eq_one_comm.1 hC
  have h2 : (g.map (↑) * g'.map (↑) : Matrix J J Ω) = 1 := by
    calc (g.map (↑) * g'.map (↑) : Matrix J J Ω) = (g.map (↑) * (g'.map (↑) * B')) * C := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = 1 := by rw [← h', ← h, h1]
  ext i j
  have := congrFun (congrFun h2 i) j
  by_cases hij : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, hij] using this

theorem indep_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hB Q hBig hGeo l z hz hcl
  obtain ⟨hT, hC⟩ := GlobalTheory.T.exists_geometricTest_map_classicalPoint L o Ω S ρ M U₀ EE hB Q hBig hGeo
  obtain ⟨p, hp, y, hy, hyU⟩ := hC z hcl
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := hT p y hyU
  have hG := GlobalTheory.T.testModel_maps_into_openPart L o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hBig
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hx : (rPt p ≫ y) (IsLocalRing.closedPoint (kb p)) = z := by
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans hy)
  have hr : Set.range (rPt p ≫ y) = {z} := hx ▸ RatModel.range_eq_singleton _ _
  refine ⟨kb p, inferInstance, rPt p ≫ y, hr, fun a ha => ?_⟩
  have hz' : z ∈ Q.W tm.l := hy ▸ tm.mem
  obtain ⟨g, hg, -⟩ := InFibChart.exists_change Q tm.l l hz' hz
  obtain ⟨g', hg', hc'⟩ := InFibChart.exists_change Q l tm.l hz hz'
  have hgg := change_mul_change (Q.c_inv l) hg hg'
  let χ := RatModel.valHom (rPt p ≫ y) z hr
  have hGG : g.map χ * g'.map χ = 1 := by
    rw [← Matrix.map_mul, hgg, Matrix.map_one _ χ.map_zero χ.map_one]
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : spMap ψ = rPt p ≫ spMap t.u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have h0 := lin_eq_zero t.mod.Φ t.mod.good (Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ)) ?_
  · have hdet : (tm.m.map ψ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (tm.unit.map ψ).ne_zero
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
    have h2 := congrArg (Matrix.vecMul · (g'.map χ)) h1
    simpa [Matrix.vecMul_vecMul, hGG] using h2
  rintro v ⟨x, hxs, hv⟩
  have h1 := t.mod.red (Over.homMk x hxs) v hv
  have hxG : (x ≫ t.mod.r) ≫ t.u.G.hom = spMap ψ := by
    rw [Category.assoc, pb.w, ← Category.assoc, hxs, Category.id_comp, hψ]
  have h2 := tm.crd (kb p) ψ (x ≫ t.mod.r) v hxG h1
  have hov : ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [Category.assoc, tm.f_over, ← Category.assoc, hxG, hψ, Category.assoc, c.fac]
  obtain ⟨x', hx'⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom ((((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) w) = z := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hov, Subsingleton.elim w (IsLocalRing.closedPoint (kb p)), hx]
      show Q.P.hom _ ∈ Q.W l
      rw [e]
      exact hz), IsOpenImmersion.lift_fac _ _ _⟩
  have hov' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [← Category.assoc, hx', Category.assoc, hov]
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
  obtain ⟨u, hu⟩ := InFibChart.crd_change Q hB.ov.ne l tm.l x' _ (rPt p ≫ y) hx'.symm hov' hx hz hz' g' hc' hw h2
  have h3 : a ⬝ᵥ w = 0 := by
    obtain ⟨j, e, -, he⟩ := hw
    have h4 := ha x' j (by
      rw [hx', Category.assoc]
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hG (Set.mem_univ _)) hov'
    rw [dotProduct, ← mul_zero (e : kb p), ← h4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i, mul_left_comm]
    rfl
  have h5 : (tm.m.map ψ).mulVec v = u • (g'.map χ).mulVec w := hu
  show Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ) ⬝ᵥ v = 0
  rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, h5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG,
    Matrix.one_mulVec, dotProduct_smul, h3, smul_zero]

end GlobalTheory.ZH.IndepFib
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_finiteDimensional_field_degenerationValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  first | exact @GlobalTheory.FiniteValues.exists_finite_field_of_values | exact GlobalTheory.FiniteValues.exists_finite_field_of_values | (intros; apply GlobalTheory.FiniteValues.exists_finite_field_of_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N : NumD F) (N' : NumD F') (ν : NumOf D F N) (ν' : NumOf D F' N'), ν'.th = ν.th → ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.GaugeHom.exists_hom | exact GlobalTheory.GaugeHom.exists_hom | (intros; apply GlobalTheory.GaugeHom.exists_hom <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.existsUnique_expansion_section_admissible_base : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.CompleteBaseExpansion.main | exact GlobalTheory.CompleteBaseExpansion.main | (intros; apply GlobalTheory.CompleteBaseExpansion.main <;> assumption)
end
