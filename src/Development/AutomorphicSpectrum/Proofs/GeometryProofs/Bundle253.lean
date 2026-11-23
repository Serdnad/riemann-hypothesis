module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceTestFunction
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeDedekindTwist
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle251
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_fibreSlice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (B ×ˢ Set.univ) y)
    {b : V} (hb : b ∈ B) : IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨hb, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem tangent_of_isGrpPullback {tB : SAB H (Sp ℂ)} (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left)
    (hφ : IsGrpPullback A tB.G (𝟙 _) φ) (hP : IsPrincipal tB) {g : ℕ} (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hu : u.IsAH Hm χ) :
    IsAbelianScheme A ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := by
    have := hAb.comm
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hAb.geomConnected⟩
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hφ ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hφ fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hφ.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hφ tB.PP.isLB hL' hw hP.2.2 }
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hu
  exact ⟨hA, h₁, h₂⟩

theorem exists_isAbLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ hb hφ hu hP
  obtain ⟨hA, h₁, h₂⟩ := tangent_of_isGrpPullback A φ hφ hP u Hm χ hu
  obtain ⟨p, hp⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv P.m.cart (𝟙_ _) (s := spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨c, hc⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv hφ (𝟙_ _) (s := 𝟙 _) (Category.comp_id _).symm
  letI := P.τ.grpB
  haveI : IsMonHom P.τ.q := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let r : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) := fun y => p.symm (e.ex b y) ≫ P.τ.q ≫ P.e.hom
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun y => c.symm (r y)
  have hr : ∀ z w, r (z + w) = r z * r w := fun z w => by
    simp only [r, e.add b hb, map_mul, MonObj.mul_comp]
  have hG : ∀ z w, G (z + w) = G z * G w := fun z w => by
    simp only [G, hr, map_mul]
  have hGr : ∀ y, (G y).left ≫ φ = (r y).left := fun y => by
    rw [← hc, c.apply_symm_apply]
  have hs : IsHolTo Set.univ (fun y => (p.symm (e.ex b y)).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback P.m.cart.1 ?_ ?_
    · have h := isHolTo_fibreSlice e.hol hb
      have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.m.cm.F) = fun y => (e.ex b y).left :=
        funext fun y => by rw [← hp, p.apply_symm_apply]
      rw [e₁]
      exact h
    · have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.tK.G.hom) = fun _ => 𝟙 (Sp ℂ) :=
        funext fun y => Over.w (p.symm (e.ex b y))
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (G z).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback hφ.1 ?_ ?_
    · have h := GlobalTheory.CMSpreadCompare.isHolTo_postcomp hs (P.τ.q ≫ P.e.hom).left
      have e₁ : (fun y => (G y).left ≫ φ) = fun y => (p.symm (e.ex b y)).left ≫ (P.τ.q ≫ P.e.hom).left :=
        funext fun y => by rw [hGr]; rfl
      rw [e₁]
      exact h
    · have e₁ : (fun y => (G y).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun y => Over.w (G y)
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ g' g u h₁ h₂ G hG hol
  refine ⟨F, fun y s hs' => ?_⟩
  have es : s = p.symm (e.ex b y) := by
    rw [eq_comm, MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext ((hp s).trans hs').symm
  rw [hF, hGr, es]

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_model_prime_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), P.Dh.HasTestPoints (algebraMap O (CR O y c') w) := by
  first | exact @PositivityTheory.Xgn.sequence_test_function | exact PositivityTheory.Xgn.sequence_test_function
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem m2Model_holds : RootLineDeRhamModel := GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian GlobalTheory.T.curveSemiAbelianConjecture

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem complex_uniformisation_holds : N1c := GlobalTheory.closing_of_abelianSchemeLaws

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem weilSt : Out.WeilSt := GlobalTheory.allSixLaws.1.weil

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_lattice_dedekind_twist : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω) (S : Finset ℕ) (R : ℕ → ℕ) [IsLocallyNoetherian X], ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → IsCptGen ξ → Flat.NormalCpt ξ → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → (∀ p ∈ S, ∀ s, ((M.htOm t.PP.L (p ^ R p)).map (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsVB (labelRk D s) ⊤) → ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s))) fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB | exact GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_comp_field_extension : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | exact GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_label_bases : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (d : ℕ), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 𝔐.R p)) → (∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s) → (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) → (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b d) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐' : HodgeCpt Y S y') (g : 𝔐'.X ⟶ 𝔐.X) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g (RingHom.id Ω) ∧ 𝔐'.f = g ≫ 𝔐.f ∧ 𝔐'.R = 𝔐.R ∧ 𝔐'.cst = 𝔐.cst ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.deg = d ∧ (∀ s i, (𝔐'.M.pt (Fl.b s i)).left ≫ 𝔐'.m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (𝔐.M.pt (b s i)).left ≫ 𝔐.m.φ) ∧ Fl.RootLines xdeg e ∧ (∀ s, (𝔐'.dR s).IsFlagVBOn Set.univ (Fl.b s)) ∧ ∀ q ∈ genFib 𝔐.ξ, (∀ s, (𝔐.V s).IsFlagVBOn {q} (b s)) → IsoAt 𝔐'.ξ g (RingHom.id Ω) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | exact GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model <;> assumption)
end
