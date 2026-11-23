module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle073
public import Mathlib.Tactic.ENatToNat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGlobalGenerators
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_point_eigen_frame_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem _root_.GlobalTheory.T.iso_line_on_equivalence : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | exact GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.degree_lattices_prime_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | exact GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_over_ramified_extension : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  intro X Ω _ ξ G G' _ _ GΩ _ φ φ' h h' V _ _ M
  obtain ⟨M₀, h₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G GΩ φ V h).1 M
  obtain ⟨M', h₁⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G' GΩ φ' V h').2 M₀
  exact ⟨M', fun e => ⟨M₀.pt e, h₀ e, h₁ e⟩⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_correspondence : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L], IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧ ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieMove.main | exact GlobalTheory.CompanionTheory.Ar.LieMove.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieMove.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange

open GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange in
theorem GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' :=
  PositivityTheory.HtPt.Htat.ht_bc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_mcPts_iff_exists_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  intro X Ω _ ξ K _ J _ y tie w
  have key := GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie ℂ
  have hval : ∀ g : MvPolynomial (Σ k, J k) ℤ,
      MvPolynomial.aeval w g = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) := by
    intro g
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  constructor
  · rintro ⟨hne, hvan⟩
    obtain ⟨z, ⟨hz, hc⟩, -⟩ := key.1 w
      (fun k => (hne k).imp fun _ h => isUnit_iff_ne_zero.mpr h)
      (fun g hg => by rw [hval]; exact hvan g hg)
    exact ⟨z, hz, hc⟩
  · rintro ⟨z, hz, hc⟩
    refine ⟨fun k => (hc.1 k).imp fun _ h => h.ne_zero, fun f hf => ?_⟩
    rw [← hval]
    exact (key.2.2 z w hz hc).1 f hf

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.line_bundle_normal_proper_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | exact GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.norm_scale_conjugate_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (M : ℕ) (f g : MRing ι) (dg : K → ℕ) (κ : (F →+* ℂ) → ℝ), OverInt y φ → 0 < M → IsMultiHomog g dg → g ∉ mCoordIdeal y → IsConjInvariantH A → (∀ σ, 0 < κ σ) → (∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖) → ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.kappa_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.line_bundle_global_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Λ : Lat ξ Ω), CoordTie ℤ ξ x → Λ.IsVB 1 ⊤ → ∃ (n m : ℕ) (s : Fin (m + 1) → Ω), (∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∀ i, s i / x c ^ n ∈ Λ p) ∧ ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ i, Λ.IsGenAt p (s i / x c ^ n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.line_twist_generated | exact GlobalTheory.CompanionTheory.Ar.line_twist_generated | (intros; apply GlobalTheory.CompanionTheory.Ar.line_twist_generated <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.degree_lattice_quotient_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (a a' : K → ℤ) (e₀ : E) (ρ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → L.IsDegOn Set.univ y a e₀ → L.IsDegOn Set.univ y a' (ρ • e₀) → ∃ f g : MRing ι, IsLineIso (mCoordIdeal y) a a' f g ∧ aeval y f = ρ * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LineIso.lineIso_of_two_degrees | exact GlobalTheory.CompanionTheory.Ar.LineIso.lineIso_of_two_degrees | (intros; apply GlobalTheory.CompanionTheory.Ar.LineIso.lineIso_of_two_degrees <;> assumption)
end
