module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.exterior_coeff_ratio_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.constants_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc | exact GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_point_component_eigen_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_cptOver_mem_isClopen_isIrreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (u : Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ (U : Set (Xo.XF c)) (_ : CptOver Y U), u ∈ U ∧ IsClopen U ∧ IsIrreducible U := by
  intro E _ _ _ H D l Xo c O _ β Y u hyp
  obtain ⟨hinj, hnoeth, hfrac⟩ := hyp
  have hmem := irreducibleComponent_mem_irreducibleComponents u
  obtain ⟨Z⟩ := nonempty_cptOver_of_fraction hinj hfrac Y _ hmem
  obtain ⟨U', hU', -⟩ := cptOver_isOpen_isDomain E H D l Xo c O β Y _ Z ⟨hinj, hnoeth, hfrac⟩
  refine ⟨irreducibleComponent u, Z, mem_irreducibleComponent, ⟨isClosed_of_mem_irreducibleComponents _ hmem, ?_⟩,
    isIrreducible_irreducibleComponent⟩
  rw [← hU']
  exact U'.isOpen

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.universal_lie_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieTransport.main | exact GlobalTheory.CompanionTheory.Ar.LieTransport.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieTransport.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_component_integral_at_prime_in_S : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | exact GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.eigenvector_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (EC : Type) [AddCommGroup EC] [Module ℂ EC] (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC) (t : 𝓞 E →+* c.F) (e : Z.V) (w : EC), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap σ → N.IsActOf Y.t.act.act ρ → e ∈ eigSp Z.ρ (Z.inc.comp t) → Z.M.ValAt (y ≫ Y.j) e (N.pt w) → w ∈ eigSp ρ (σ.comp t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FramesEig.mem_eigSp_of_valAt | exact GlobalTheory.CompanionTheory.Ar.FramesEig.mem_eigSp_of_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.FramesEig.mem_eigSp_of_valAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.dedekind_constants_degree_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L : Lat ξ E), L.IsFlagVBOn (overPrime ξ p) w → ∃ B : ChartBundle O (segreVec y) r E, (∀ c, segreVec y c ≠ 0 → ∀ v, v ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → v ∈ L q) ∧ ∀ (x : Fin r → K → ℤ) (e : Fin r → Ω) (he : ∀ i, e i ≠ 0), (∀ i, (L.gr w i).IsDegOn (overPrime ξ p) y (x i) (e i)) → IsFlagFrame y B (w.unitsSMul fun i => Units.mk0 (e i) (he i)) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn | exact GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem exists_isActOf_lemma {S : Scheme} {R : Type} [CommRing R]
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V]
    [Module R V] (M : GlobalTheory.CompanionTheory.Ar.LieModel G x V) {O : Type} [CommRing O]
    (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) :
    ∃ ρ : O →+* Module.End R V, M.IsActOf act.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by
      rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h).symm
  have hact0 : act.act 0 = 1 := by
    have h : act.act 0 * 1 = act.act 0 * act.act 0 := by
      rw [_root_.mul_one, ← act.add, add_zero]
    exact (mul_left_cancel h).symm
  have htan : ∀ (a : O) (e : V), GlobalTheory.CompanionTheory.Ar.IsTanAt G x (M.pt e ≫ act.act a) := by
    intro a e
    haveI := act.hom a
    have h1 := M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  choose f hf using fun (a : O) (e : V) => M.onto _ (htan a e)
  have hadd : ∀ (a : O) (e e' : V), f a (e + e') = f a e + f a e' := by
    intro a e e'
    haveI := act.hom a
    apply M.inj
    rw [hf, M.add, M.add, hf, hf, MonObj.mul_comp]
  have hsmul : ∀ (a : O) (r : R) (e : V), f a (r • e) = r • f a e := by
    intro a r e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hf, M.smul, hf, Over.comp_left, Over.comp_left, M.smul, Category.assoc]
  refine ⟨{
      toFun := fun a => { toFun := f a, map_add' := hadd a, map_smul' := hsmul a }
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_⟩
  · ext e
    show f 1 e = e
    apply M.inj
    rw [hf, act.one, Category.comp_id]
  · intro a b
    ext e
    show f (a * b) e = f a (f b e)
    apply M.inj
    rw [hf, hf, hf, mul_comm a b, act.mul, Category.assoc]
  · ext e
    show f 0 e = 0
    apply M.inj
    rw [hf, hact0, MonObj.comp_one, hpt0]
  · intro a b
    ext e
    show f (a + b) e = f a e + f b e
    apply M.inj
    rw [hf, M.add, hf, hf, act.add, MonObj.comp_mul]
  · unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    exact hf a e

theorem exists_lieModel_tied_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (y : Sp ℂ ⟶ Xo.XF c), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module ℂ EC) (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC), N.IsActOf Y.t.act.act ρ ∧ ∀ (ch : 𝓞 E →+* ℂ) (n : ℕ) (v : Vecs y n) (w : Fin n → EC), LieMult Xo.univ.t.act (under y) ch n → (∀ i, SameVec Y y (v i) (N.pt (w i))) → LinearIndependent ℂ w → (∀ i, w i ∈ eigSp ρ ch) → IsEigFrame Xo.univ.t.act (under y) ch v := by
  intro E _ _ _ H D l Xo c O _ β Y y
  haveI := Xo.univ.t.comm
  obtain ⟨V, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Xo.univ.t.G ℂ (under y)
  obtain ⟨ρ, hρ⟩ := exists_isActOf_lemma M₀ Xo.univ.t.act
  obtain ⟨M', hM'⟩ :=
    (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m0.toSABMap.cart ℂ y V).1 M₀
  obtain ⟨N, hN⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m.cart ℂ y V).2 M'
  have hsame : ∀ e, SameVec Y y (M₀.pt e) (N.pt e) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.Flat.SameVec
    exact ⟨(M'.pt e).left, Over.w (M'.pt e), hM' e, hN e⟩
  have hK : ∀ (a : 𝓞 E) (e : V),
      (M'.pt (ρ a e)).left = (M'.pt e).left ≫ (Y.oF.t.act.act a).left := by
    intro a e
    refine Y.m0.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [hM', Category.assoc, Y.m0.toSABMap.act a, ← Category.assoc, hM', ← Over.comp_left,
        ← hρ a e]
    · rw [Over.w, Category.assoc, Over.w, Over.w]
  have hNact : N.IsActOf Y.t.act.act ρ := by
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    apply Over.OverMorphism.ext
    rw [← hN, hK, Over.comp_left, ← hN, Category.assoc, Category.assoc, Y.m.act a]
  refine ⟨V, i1, i2, N, ρ, hNact, ?_⟩
  intro ch n v w hmult hsv hli hmem
  have hv : v = fun k => M₀.pt (w k) := by
    funext k
    exact SameVec.unique_left (hsv k) (hsame (w k))
  obtain ⟨v₀, hv₀⟩ := hmult
  have hfr₀ : IsEigFrame Xo.univ.t.act (under y) ch v₀ := hv₀
  have htan₀ : ∀ k, IsTanAt Xo.univ.t.G (under y) (v₀ k) := fun k => (hfr₀.1 k).1
  choose u hu using fun k => M₀.onto (v₀ k) (htan₀ k)
  have hI := (GlobalTheory.T.lie_model_eigenvectors_action _ ℂ Xo.univ.t.G (under y) V M₀).2 _ Xo.univ.t.act ρ ch hρ
  have hv₀' : v₀ = fun k => M₀.pt (u k) := funext fun k => (hu k).symm
  rw [hv₀'] at hfr₀
  obtain ⟨hu_li, hu_span⟩ := (hI.2 n u).1 hfr₀
  haveI : FiniteDimensional ℂ (eigSp ρ ch) := by
    rw [← hu_span]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hspan : Submodule.span ℂ (Set.range w) = eigSp ρ ch := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmem k
    · rw [finrank_span_eq_card hli, ← hu_span, finrank_span_eq_card hu_li]
  rw [hv]
  exact (hI.2 n w).2 ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isEigFrame_of_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (κ : 𝓞 E →+* F) {n : ℕ}
    (v : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)) (v₀ : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (hs : ∀ i, SameVec Y y (v i) (v₀ i)) (hf : IsEigFrame Y.t.act (y ≫ Y.j) κ v₀) :
    IsEigFrame Xo.univ.t.act (under y) κ v := by
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  choose u hu₀ hu₁ hu₂ using hs
  let a : Fin n → (epsAt y ⟶ Y.oF.t.G) := fun i => Over.homMk (u i) (hu₀ i)
  have e₀ : (fun i => tanMap hq y (a i)) = v₀ := funext fun i => Over.OverMorphism.ext (hu₂ i)
  have e₁ : (fun i => tanMap hp y (a i)) = v := funext fun i => Over.OverMorphism.ext (hu₁ i)
  have h₁ : IsEigFrame Y.oF.t.act y κ a :=
    (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y κ a).1 (by rw [e₀]; exact hf)
  have h₂ := (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y κ a).2 h₁
  rw [e₁] at h₂
  exact h₂

theorem isFramed_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ y v w v₀ w₀ hy hv hw fv fw
  exact ⟨hy, Set.subset_univ _, isEigFrame_of_sameVec Y y _ v v₀ hv fv, isEigFrame_of_sameVec Y y _ w w₀ hw fw⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

-- Some dependency stubs refer to this doubly qualified name when unfolding `LieModel.Lifts`.
-- Keep it definitionally equal to the actual map.
abbrev GlobalTheory.CompanionTheory.Ar.GlobalTheory.CompanionTheory.Ar.dualMap
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    DualNumber R →+* DualNumber R' :=
  _root_.GlobalTheory.CompanionTheory.Ar.dualMap φ

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.punctured_polydisc_open_connected : ∀ (n a : ℕ) (ρ : ℝ), 0 < ρ → IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty | exact GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty <;> assumption)
end
