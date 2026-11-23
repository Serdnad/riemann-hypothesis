module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullLevelFiniteExtension
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RefLowerOfFibreInput
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle180
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle178
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle179
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle181
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lattice_frame_open_condition : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | exact GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | (intros; apply GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_full_level_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (N : ℕ), 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ) (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)), FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite | exact GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.tower_i6_of_reference : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | exact GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.ref_lower_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (R : RootModel Ψ (j + 1 + (k + 1))), AmpleQ R.y R.A.a → FlatUnit R → FibreInput R → RefLower R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | exact GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.tower_i5_of_reference : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → (∀ c, RefLower (R c)) → T.I5 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower | exact GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_eigen_tangent_extension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T] (GK : Over (Sp K)) [GrpObj GK] (φ₀ : GK.left ⟶ T.left)
    (Oe : Type) [CommRing Oe] (actT : OAct Oe T) (actK : OAct Oe GK) (g n : ℕ) (ML : LieModel GK (𝟙 _) (Fin g → K))
    (ρK : Oe →+* Module.End K (Fin g → K)) (σV : Oe →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T)) (b : Fin n → Fin g → K),
    IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ → (∀ a, (actK.act a).left ≫ φ₀ = φ₀ ≫ (actT.act a).left) →
    ML.IsActOf actK.act ρK → IsEigFrame actT (𝟙 _) σV vV →
    (∀ i, (ML.pt (b i)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left) →
    ∀ w, w ∈ Submodule.span V (Set.range b) ↔
      (∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ (ML.pt w).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ∧
        ∀ r, ρK r w = algebraMap V K (σV r) • w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.EigLin.mem_span_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.EigLin.mem_span_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.EigLin.mem_span_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lie_model_with_cm_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P → ∃ (M : LieModel Xo.univ.t.G (FU.u i P) (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ a w, ρ a w = fun k => ty k (a : E) * w k) ∧ (∀ w, IsDerivAt0 (fun z => (FU.ex i P z).left) w (M.pt w).left) ∧ ∀ τ w, HT.eigProj ρ τ w = tyPart ty τ w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action | exact GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

open _root_.GlobalTheory.CompanionTheory.Ar (dualMap)

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_spMap_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B)
    {T : Scheme.{0}} (g : Sp A ⟶ T) : spMap a ≫ spMap b ≫ g = spMap (a.comp b) ≫ g := by
  rw [← Category.assoc, spMap_spMap]

theorem spMap_idR (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ :=
  Spec.map_id (CommRingCat.of A)

theorem algebraMap_dual (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

theorem dualMap_comp_algebraMap (f : R →+* R) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R (DualNumber R)).comp f := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_epsMul (f : R →+* R) (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  ext a <;> simp [dualMap, epsMul, algebraMap_dual]

theorem fst_comp_dualMap (f : R →+* R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_dualMap (f : R →+* R) (hf : ∀ a, f (f a) = a) :
    (dualMap f).comp (dualMap f) = RingHom.id _ := by
  ext a <;> simp [dualMap, hf, algebraMap_dual]

def trM (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    subst hx
    change spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R (DualNumber R)) ≫ spMap f ≫ x
    rw [spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_algebraMap])

def tr (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  trM f hx ≫ v

theorem tr_left (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) :
    (tr f hx v).left = spMap (dualMap f) ≫ v.left := rfl

variable {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S}

theorem tr_mul (f : R →+* R) (hx : x' = spMap f ≫ x) (a b : epsAt x ⟶ G) :
    tr f hx (a * b) = tr f hx a * tr f hx b :=
  MonObj.comp_mul _ _ _

theorem tr_one (f : R →+* R) (hx : x' = spMap f ≫ x) : tr f hx (1 : epsAt x ⟶ G) = 1 := by
  rw [tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]

def trHom (f : R →+* R) (hx : x' = spMap f ≫ x) : (epsAt x ⟶ G) →* (epsAt x' ⟶ G) where
  toFun := tr f hx
  map_one' := tr_one f hx
  map_mul' := tr_mul f hx

theorem tr_prod (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    tr f hx (List.ofFn u).prod = (List.ofFn fun i => tr f hx (u i)).prod := by
  have := map_list_prod (trHom (G := G) f hx) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact this

theorem isTanAt_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {v : epsAt x ⟶ G} (h : IsTanAt G x v) :
    IsTanAt G x' (tr f hx v) := by
  have h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  unfold IsTanAt at h ⊢
  rw [h1, Over.comp_left, ← h, tr_left]
  change spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left
  rw [spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]

theorem isEigVec_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hx : x' = spMap f ≫ x) {τ : O →+* R}
    {v : epsAt x ⟶ G} (h : IsEigVec act x τ v) : IsEigVec act x' (f.comp τ) (tr f hx v) := by
  refine ⟨isTanAt_tr f hx h.1, fun a => ?_⟩
  have h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left := by
    rw [tr, Category.assoc]; rfl
  rw [h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem isComb_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsAt x ⟶ G)}
    {w : epsAt x ⟶ G} (h : IsComb c v w) : IsComb (fun i => f (c i)) (fun i => tr f hx (v i)) (tr f hx w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩
  rw [tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem back (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) : x = spMap f ≫ x' := by
  have : f.comp f = RingHom.id R := RingHom.ext hf
  rw [hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]

theorem tr_tr (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) (hx' : x = spMap f ≫ x')
    (v : epsAt x ⟶ G) : tr f hx' (tr f hx v) = v := by
  apply Over.OverMorphism.ext
  rw [tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]

theorem isEigFrame_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hf : ∀ a, f (f a) = a)
    (hx : x' = spMap f ≫ x) {τ : O →+* R} {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (h : IsEigFrame act x τ v) :
    IsEigFrame act x' (f.comp τ) (fun i => tr f hx (v i)) := by
  have hx' := back f hf hx
  refine ⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩
  have hw0 : IsEigVec act x τ (tr f hx' w) := by
    have := isEigVec_tr act f hx' hw
    have e : f.comp (f.comp τ) = τ := RingHom.ext fun a => hf _
    rwa [e] at this
  obtain ⟨c, hc, hu⟩ := h.2 _ hw0
  refine ⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩
  · have := isComb_tr f hx hc
    rwa [tr_tr f hf hx' hx] at this
  · have h3 := isComb_tr f hx' hc'
    simp only [tr_tr f hf hx hx'] at h3
    have h4 := hu _ h3
    funext i
    rw [← h4]
    exact (hf _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

namespace GlobalTheory.CompanionTheory.Ar.Flat


open ConjPt in
theorem hasInfNorm_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  intro E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ
  have hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := fun z => Complex.conj_conj z
  obtain ⟨h1, h2, h3, h4⟩ := hfr
  have hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y := Category.assoc _ _ _
  have hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g :=
    fun g => RingHom.ext fun a => hcc _
  let v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p := fun i => tr (starRingEnd ℂ) hy (v i)
  let w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q := fun i => tr (starRingEnd ℂ) hy (w i)
  have hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, spMap_spMap, hcomp]
    · rintro _ ⟨a, rfl⟩
      exact h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ) :=
        RingHom.ext fun a => hcc _
      rwa [e] at this
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) =
          s.comp (tauIn c (ComplexEmbedding.conjugate τ)) := RingHom.ext fun a => hcc _
      rwa [e] at this
  have hΓ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ
  have hΔ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ
  have hnat := hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w'
    ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)
  have hm := hs _ v' w' _ _ hfr' hΓ' hΔ'
  have hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖ := by
    intro n M
    have : (M.map star).det = (starRingEnd ℂ) M.det := by
      rw [RingHom.map_det]; rfl
    rw [this, RCLike.norm_conj]
  rw [hnat, RCLike.norm_conj, hdet, hdet] at hm
  exact hm

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_block_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | exact GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_lattice_constant_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω), ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → FiniteDimensional Ω Li ∧ ∀ s, Module.finrank Ω (eigSp ρ (cst.comp (labelEmb c s))) = labelRk D s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label | exact GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label | (intros; apply GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.stable_eigen_at_component_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.frame_function_exterior_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point | exact GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point <;> assumption)
end
