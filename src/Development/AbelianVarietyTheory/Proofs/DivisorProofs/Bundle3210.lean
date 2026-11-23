module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3155
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.generator_values_mem_subfield_galoisDescent : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  first | exact @GlobalTheory.Poinc.Sep.gen_values_mem | exact GlobalTheory.Poinc.Sep.gen_values_mem | (intros; apply GlobalTheory.Poinc.Sep.gen_values_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.rescaled_degenerationData_differ_by_scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  first | exact @GlobalTheory.RatioScalar.scalar | exact GlobalTheory.RatioScalar.scalar | (intros; apply GlobalTheory.RatioScalar.scalar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_eq_closedPoint_iff {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hρ : ρ.Finite) (y : Sp R') : spMap ρ y = closedPoint R ↔ y = closedPoint R' := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hρ
  haveI : Algebra.IsIntegral R R' := inferInstance
  constructor
  · intro h
    have hc : (y.asIdeal.comap (algebraMap R R')).IsMaximal := by
      have : (spMap ρ y).asIdeal = y.asIdeal.comap ρ := rfl
      rw [h] at this
      change (y.asIdeal.comap ρ).IsMaximal
      rw [← this]; exact IsLocalRing.maximalIdeal.isMaximal R
    haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum R')
    have hm : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under y.asIdeal hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
  · rintro rfl
    have hc : ((maximalIdeal R').comap (algebraMap R R')).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R')
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hc)

theorem exists_open_secNz_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ ⟨g0, hg0c, hg0⟩
  have hfin : IsFinite (spMap ρ) := by rw [IsFinite.SpecMap_iff]; exact hF.2.2
  haveI hβfin : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hfin
  have hcl : IsClosedMap β := β.isClosedMap
  have hsq : ∀ g' : G'.left, G.hom (β g') = spMap ρ (G'.hom g') := fun g' => by
    change (β ≫ G.hom) g' = (G'.hom ≫ spMap ρ) g'
    rw [hβ.1.w]

  obtain ⟨s, hs⟩ : ∃ s : (Sp R' : Scheme.{0}), s = closedPoint R' := ⟨_, rfl⟩
  rw [← hs] at hg0c
  haveI hirr : IrreducibleSpace (G'.hom.fiber s) :=
    GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G' hS' _ ((Sp R').fromSpecResidueField s)
  obtain ⟨η', hη'⟩ : ∃ η' : G'.left, η' = G'.hom.fiberι s (genericPoint (G'.hom.fiber s)) := ⟨_, rfl⟩
  have hspec : ∀ g' : G'.left, G'.hom g' = s → η' ⤳ g' := by
    intro g' hg'
    obtain ⟨z, hz⟩ : g' ∈ Set.range (G'.hom.fiberι s) := (Scheme.Hom.range_fiberι G'.hom s).ge hg'
    rw [← hz, hη']
    exact ((genericPoint_spec (G'.hom.fiber s)).specializes trivial).map (G'.hom.fiberι s).continuous
  have hηs : G'.hom η' = s := by
    rw [hη']; exact (Scheme.Hom.range_fiberι G'.hom s).le ⟨_, rfl⟩
  have hηnz : η' ∈ secNz θ := (hspec g0 hg0c).mem_open (secNz θ).isOpen hg0
  refine ⟨⟨farSet β θ, isOpen_farSet β hcl θ⟩, ⟨β η', ?_, ?_⟩, ?_⟩
  · show ∀ g', β g' = β η' → g' ∈ secNz θ
    intro g' hg'
    have hg's : G'.hom g' = s := by
      rw [hs, ← spMap_eq_closedPoint_iff ρ hF.2.2, ← hsq, hg', hsq, hηs]
      exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
    have := GlobalTheory.eq_of_specializes_of_isIntegralHom β (hspec g' hg's) hg'.symm
    rw [← this]; exact hηnz
  · rw [hsq, hηs]; exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
  · intro g' hg' _
    exact hg' g' rfl

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  first | exact @GlobalTheory.MumTwistCP.exists_cp_transl | exact GlobalTheory.MumTwistCP.exists_cp_transl | (intros; apply GlobalTheory.MumTwistCP.exists_cp_transl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  first | exact @GlobalTheory.Mum.thetaNZ_of_preU | exact GlobalTheory.Mum.thetaNZ_of_preU | (intros; apply GlobalTheory.Mum.thetaNZ_of_preU <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_fixed_unramified_complete_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.UnramTorsPull.torsion_fixed_unramified | exact GlobalTheory.UnramTorsPull.torsion_fixed_unramified | (intros; apply GlobalTheory.UnramTorsPull.torsion_fixed_unramified <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tripleIso_of_linear_degenerationData_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  first | exact @GlobalTheory.triple_iso_of_linear_data_iso | exact GlobalTheory.triple_iso_of_linear_data_iso | (intros; apply GlobalTheory.triple_iso_of_linear_data_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArc.exists_input_recovering | exact GlobalTheory.TraitArc.exists_input_recovering | (intros; apply GlobalTheory.TraitArc.exists_input_recovering <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_off_closedFibre_descended : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  first | exact @GlobalTheory.Mum.OffClosed.exists_gen_off_closed | exact GlobalTheory.Mum.OffClosed.exists_gen_off_closed | (intros; apply GlobalTheory.Mum.OffClosed.exists_gen_off_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  first | exact @GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | exact GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | (intros; apply GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_descendedBundle_near_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  first | exact @GlobalTheory.Mum.ClosedPt.exists_gen_near_closed_point | exact GlobalTheory.Mum.ClosedPt.exists_gen_near_closed_point | (intros; apply GlobalTheory.Mum.ClosedPt.exists_gen_near_closed_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens), IsAffineOpen W → ∀ (U : M.S.Opens), IsAffineOpen U → W ≤ G.hom ⁻¹ᵁ U → ∀ (f : Γ(Y, α ⁻¹ᵁ W)) (x ζ : G.left), x ∈ W → G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → (∃ c : Γ(G.left, W), ζ ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f)) → ∃ c : Γ(G.left, W), x ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f) := by
  first | exact @GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | exact GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | (intros; apply GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic <;> assumption)
end
