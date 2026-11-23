module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle079
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle080
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle081
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def zPt {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift z.x (spMap (algebraMap c.F S)) (by
    rw [z.x_over]
    simp only [Formalism.L2.Pj.sOf, spMap, ← Spec.map_comp]
    rfl)

theorem zPt_fst {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.fst _ _ = z.x := pullback.lift_fst _ _ _

theorem zPt_snd {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem eq_zPt {S B : Type} [CommRing S] [Algebra c.F S] [CommRing B] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* B) (y : Sp B ⟶ Xo.XF c) (h₁ : under y = spMap ψ ≫ z.x)
    (h₂ : y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S))) : y = spMap ψ ≫ zPt z := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, zPt_fst]; exact h₁
  · rw [Category.assoc, zPt_snd, h₂]
    simp only [spMap, ← Spec.map_comp]
    rfl

def Tied {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {B : Type} [CommRing B] (y : Sp B ⟶ Xo.XF c)
    (v : Sp (DualNumber B) ⟶ Xo.univ.t.G.left) (v' : Sp (DualNumber B) ⟶ Y.t.G.left) : Prop :=
  ∃ u : Sp (DualNumber B) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v ∧ u ≫ Y.m.φ = v'

def StableEig {X : Scheme.{0}} (t : SAB H X) {A : Type} [CommRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ)
    {r : ℕ} (e : Fin r → (epsAt x ⟶ t.G)) : Prop :=
  ∀ (T : Type) [CommRing T] (θ : A →+* T) (x' : Sp T ⟶ X), spMap θ ≫ x = x' →
    ∀ v : Fin r → (epsAt x' ⟶ t.G), (∀ i, (v i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) →
      IsEigFrame t.act x' ((θ.comp κ).comp (tauIn c σ)) v

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CstChart

theorem germ_top_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫
        Scheme.stalkClosedPointTo ξ = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem ringHom_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] (φ : O →+* Ω) (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom φ)) (p : Cpt ξ) (o : O) : φ o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial)
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom φ := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem segre_adjoin_le {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) :
    Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩) ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)).restrictScalars ℤ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩ ∈
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)
  rw [← Finset.prod_div_distrib]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem cst_mem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 cc hcc r
  have hx : (∏ k, y ⟨k, cc k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hcc k
  have hint : ∀ a : 𝓞 c.F, 𝔐.cst (algebraMap (𝓞 c.F) c.F a) ∈
      Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := fun a =>
    segre_adjoin_le y cc ((𝔐.tie.ring cc hx _).2 fun p _ =>
      ringHom_mem_regAt 𝔐.ξ (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) (𝔐.f ≫ Y.s) 𝔐.cst_over p a)
  haveI : FiniteDimensional ℚ c.F := c.fin
  have halg : IsAlgebraic ℤ r := (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic r)
  obtain ⟨n, hn, hr⟩ := halg.exists_integral_multiple
  have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  have e : 𝔐.cst r = algebraMap ℚ Ω (n : ℚ)⁻¹ *
      𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) (n • r) hr)) := by
    rw [IsIntegralClosure.algebraMap_mk', zsmul_eq_mul, map_mul, map_intCast]
    simp [hn']
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hint _)

end GlobalTheory.CompanionTheory.Ar.CstChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.adapted_basis_spans_eigenspace : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W),
    IsAdapted ρH σ v w u → LinearIndependent K v → Module.finrank K (HT.eigSp ρH σ) = p + q →
    FiniteDimensional K (HT.eigSp ρH σ) →
    LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.homogeneous_form_nonvanishing_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | exact GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_over_lie_model_base_change : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeLin

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

abbrev tanEquiv (hp : IsGrpPullback A G z φ) : (epsR ℂ ⟶ A) ≃* (epsAt z ⟶ G) :=
  LiePull.pts hp (T := epsR ℂ) (g := (epsAt z).hom) rfl

theorem unit_left (hp : IsGrpPullback A G z φ) : η[A].left ≫ φ = (1 : Over.mk z ⟶ G).left := by
  have e := map_one (LiePull.pts hp (T := 𝟙_ (Over (Sp ℂ))) (g := z) (Category.id_comp z))
  have e' := congrArg (fun q => q.left) e
  have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1] at e'
  exact e'

theorem isTangent_iff (hp : IsGrpPullback A G z φ) (x : epsR ℂ ⟶ A) :
    IsTangent x ↔ IsTanAt G z (tanEquiv hp x) := by
  unfold IsTangent IsTanAt
  constructor
  · intro t
    rw [← unit_left hp, ← t, Category.assoc]
    rfl
  · intro t
    apply hp.1.hom_ext
    · rw [Category.assoc, unit_left hp, ← t]
      rfl
    · have e : (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext r
        simp
      have e' := congrArg Spec.map e
      simp only [Spec.map_comp, Spec.map_id] at e'
      have hx : x.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w x
      have h0 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hx, h0]
      exact e'

theorem exists_linearEquiv : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type)
    [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left)
    (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
    (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
    ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  intro X G _ z V _ _ M A _ φ L g u hp h1 h2
  let Φ := tanEquiv hp
  let x : V → (epsR ℂ ⟶ A) := fun v => Φ.symm (M.pt v)
  have hΦx : ∀ v, Φ (x v) = M.pt v := fun v => Φ.apply_symm_apply _
  have hleft : ∀ v, (x v).left ≫ φ = (M.pt v).left := fun v => congrArg (fun q => q.left) (hΦx v)
  have tx : ∀ v, IsTangent (x v) := fun v => (isTangent_iff hp _).2 (by
    change IsTanAt G z (Φ (x v))
    rw [hΦx]
    exact M.tan v)
  have xadd : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    simp only [x]
    rw [M.add, map_mul]
  have xsmul : ∀ (c : ℂ) v, x (c • v) = Chart.spMap (Chart.scaleD c) ≫ x v := fun c v => by
    apply Φ.injective
    rw [hΦx]
    apply Over.OverMorphism.ext
    rw [M.smul c v, ← hleft v]
    exact (Category.assoc _ _ _).symm
  have tan' : ∀ {y : epsR ℂ ⟶ A}, IsTangent y → Chart.IsTan y := fun h => (Chart.isTan_iff _).2 h
  choose d hd hu using fun v => h1 (x v) (tx v)
  let Dl : V →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := d
      map_add' := fun v v' => by
        symm
        apply hu
        rw [xadd]
        exact UnifDifferential.isDiff_mul u (tan' (tx v)) (tan' (tx v')) (hd v) (hd v')
      map_smul' := fun c v => by
        symm
        apply hu
        rw [xsmul]
        exact UnifDifferential.isDiff_scale u (hd v) c }
  have inj : Function.Injective Dl := fun v v' e => by
    have e' : d v = d v' := e
    have h : x v = x v' := (h2 (d v')).unique ⟨tx v, e' ▸ hd v⟩ ⟨tx v', hd v'⟩
    exact M.inj (by rw [← hΦx, ← hΦx, h])
  have surj : Function.Surjective Dl := fun w => by
    obtain ⟨y, ⟨ty, dy⟩, -⟩ := h2 w
    obtain ⟨v, hv⟩ := M.onto _ ((isTangent_iff hp y).1 ty)
    have hy : x v = y := Φ.injective (by rw [hΦx]; exact hv)
    exact ⟨v, (hu v w (hy ▸ dy)).symm⟩
  exact ⟨LinearEquiv.ofBijective Dl ⟨inj, surj⟩, fun v => ⟨x v, tx v, hleft v, hd v⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeLin
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.twisted_frame_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.snc_model_from_local_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.torsion_points_number_field : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField | exact GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField | (intros; apply GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.plurisubharmonic_local : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U → (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | exact GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | (intros; apply GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.number_field_point_integral_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers | exact GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers <;> assumption)
end
