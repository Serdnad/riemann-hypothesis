module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle171
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle165
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GDerivLin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle172
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_injective_on_open : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective | exact GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_ringHom {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    (z : Sp B ⟶ X) (hr : Set.range z ⊆ Set.range x) : ∃ a : A →+* B, spMap a ≫ x = z := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem ringHom_ext {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    {a b : A →+* B} (h : spMap a ≫ x = spMap b ≫ x) : a = b := by
  have h2 := Spec.map_injective ((cancel_mono x).1 h)
  exact congrArg (fun g => g.hom) h2

theorem exists_frac {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] (P : X)
    (hP : P ∈ x.opensRange) (θ : R →+* X.presheaf.stalk P) (hθ : spMap θ ≫ x = X.fromSpecStalk P)
    (a : X.presheaf.stalk P) : ∃ r s : R, IsUnit (θ s) ∧ a * θ s = θ r := by
  have hU : IsAffineOpen x.opensRange := isAffineOpen_opensRange x
  let R₂ : Type := Γ(X, x.opensRange)
  let x₂ : Sp R₂ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₂ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range x₂ = Set.range x := by
    change Set.range hU.fromSpec = _
    rw [hU.range_fromSpec]
    rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom x x₂ hrange.le
  obtain ⟨φ', hφ'⟩ := exists_ringHom x₂ x hrange.ge
  have hcomp : φ.comp φ' = RingHom.id R₂ := ringHom_ext x₂ (by
    rw [spMap_comp, Category.assoc, hφ', hφ]
    simp [spMap])
  let g : R₂ →+* X.presheaf.stalk P := (X.presheaf.germ x.opensRange P hP).hom
  have hg : spMap g ≫ x₂ = X.fromSpecStalk P := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]
    rfl
  have hgφ : g.comp φ = θ := ringHom_ext x (by
    rw [spMap_comp, Category.assoc, hφ, hg, hθ])
  have hgs : ∀ t, θ (φ' t) = g t := fun t => by
    rw [← hgφ]
    exact congrArg g (RingHom.congr_fun hcomp t)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)
  haveI := hU.isLocalization_stalk ⟨P, hP⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a
  refine ⟨φ' r, φ' s, ?_, ?_⟩
  · rw [hgs]
    exact IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s
  · rw [hgs, hgs]
    exact hrs

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem exists_chart_spread : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  intro X G _ _ _ P ι _ e f he
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩ := LieVB.exists_chart G P
  have hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  obtain ⟨θ₁, hθ₁⟩ := LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'
  obtain ⟨Fs, _, _, ⟨Ms⟩⟩ := lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)
  obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b
  choose s hs using fun i => Ms.onto (e i) (he i)
  let c : ι → Fin n → X.presheaf.stalk P := fun i k => B.repr (s i) k
  choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁
  let h : R₁ := den f * ∏ i, ∏ k, den (c i k)
  have hunit : IsUnit (θ₁ h) := by
    simp only [h, map_mul, map_prod]
    exact (hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)
  let R : Type := Localization.Away h
  let θ : R →+* X.presheaf.stalk P := IsLocalization.Away.lift h hunit
  have hθc : θ.comp (algebraMap R₁ R) = θ₁ := IsLocalization.Away.lift_comp h hunit
  let x : Sp R ⟶ X := spMap (algebraMap R₁ R) ≫ x₁
  have hopen : IsOpenImmersion (spMap (algebraMap R₁ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))
  have hx : IsOpenImmersion x := inferInstance
  have hxθ : spMap θ ≫ x = X.fromSpecStalk P := by
    change spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _
    rw [← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]
  have hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a := fun a hd => by
    have hu : IsUnit (algebraMap R₁ R (den a)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)
    obtain ⟨u, hu⟩ := hu
    have hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a) := RingHom.congr_fun hθc _
    refine ⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩
    have h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1 := by
      rw [← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a) := RingHom.congr_fun hθc _
    rw [map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]
  have hdvd : ∀ i k, den (c i k) ∣ h := fun i k =>
    Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _
  choose c' hc' using fun i k => hlift (c i k) (hdvd i k)
  obtain ⟨f', hf'⟩ := hlift f (Dvd.intro _ rfl)
  obtain ⟨F', _, _, ⟨MR⟩⟩ := lieModel_exists X G R x
  obtain ⟨β₁, B₁, hB₁, hβ₁⟩ := LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms
  have hjB : ∀ k, j (B₁ k) = B k := fun k => LieVB.pt_left_inj Ms (by
    rw [hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])
  refine ⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf',
    fun i => MR.tan _, fun i => ?_⟩
  · refine ⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hxθ]
    exact Scheme.fromSpecStalk_closedPoint
  · have hsum : j (∑ k, c' i k • B₁ k) = s i := by

      rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))
      rw [j.map_smulₛₗ, hc', hjB]
    rw [← hj, hsum, hs]

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_hodge_tate_functional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | exact GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_character_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_character_section | exact GlobalTheory.CompanionTheory.Relay.exists_character_section | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_character_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_open_forall {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (p : Cpt ξ) {I : Type} [Finite I]
    (P : I → Cpt ξ → Prop) (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  classical
  have := Fintype.ofFinite I
  have key : ∀ s : Finset I, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i ∈ s, P i q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨U, hU, HU⟩ := ih
      obtain ⟨V, hV, HV⟩ := h a
      refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact HV q hq.2
      · exact HU q hq.1 i hi
  obtain ⟨U, hU, HU⟩ := key Finset.univ
  exact ⟨U, hU, fun q hq i => HU q hq i (Finset.mem_univ i)⟩

theorem exists_open_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  obtain ⟨U, hU, HU⟩ := exists_open_forall p (fun (j : Fin n) (q : Cpt ξ) => (f j : Ω) ∈ regAt ξ q)
    fun j => exists_open_mem_regAt ξ p _ (f j).2
  refine ⟨U, hU, fun q hq => ?_⟩
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (⟨(f j : Ω), HU q hq j⟩ : regAt ξ q) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_span_field_of_mem_span_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type}
    [AddCommGroup E] [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) : e ∈ Submodule.span Ω (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (f j : Ω) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_span_and_nhd : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  intro X G _ _ _ Ω _ ξ E _ _ M p g b hb
  obtain ⟨R, _, x, hx, F, _, _, MR, n, bR, hp⟩ := exists_chart G p.1
  have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR bR ξ M φ hφ
  have hc : ∀ q : Cpt ξ, q.1 ∈ x.opensRange → M.lat.IsFrameAt c q := by
    intro q hq
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  have hbc : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range c) :=
    hb.2.symm.trans (hc p hp).2
  have hbi : ∀ i, b i ∈ Submodule.span (regAt ξ p) (Set.range c) := fun i => by
    rw [← hbc]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcj : ∀ j, c j ∈ Submodule.span (regAt ξ p) (Set.range b) := fun j => by
    rw [hbc]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨top_le_iff.1 (hsp.ge.trans (Submodule.span_le.2 ?_)), ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact mem_span_field_of_mem_span_regAt ξ p b _ (hcj j)
  obtain ⟨U, hU, HU⟩ := exists_open_forall p
    (fun (i : Fin g) (q : Cpt ξ) => b i ∈ Submodule.span (regAt ξ q) (Set.range c))
    fun i => exists_open_mem_span ξ p c _ (hbi i)
  obtain ⟨V, hV, HV⟩ := exists_open_forall p
    (fun (j : Fin n) (q : Cpt ξ) => c j ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun j => exists_open_mem_span ξ p b _ (hcj j)
  refine ⟨x.opensRange ⊓ (U ⊓ V), ⟨hp, hU, hV⟩, fun q hq => ⟨hb.1, ?_⟩⟩
  rw [(hc q hq.1).2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact HV q hq.2.2 j
  · rintro _ ⟨i, rfl⟩
    exact HU q hq.2.1 i

end GlobalTheory.CompanionTheory.Ar.LieVB
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.UpperTower

theorem proj_inl_mem {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L} (hz : z ∈ ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    (fun p => z (joinInl ι₁ ι₂ p)) ∈ ptsOver L (mCoordIdeal y₁) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have key : ∀ g : MRing ι₁, mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) g) =
      rename (Sum.inl : K₁ → K₁ ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hmem : rename (joinInl ι₁ ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
    have hf' : mConeMap y₁ f = 0 := hf
    change mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) f) = 0
    rw [key, hf', map_zero]
  have h := hz.2 _ hmem
  rw [aeval_rename] at h
  exact h

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem weightAbsEntrySum_nonneg (mu : Wt Ψ N) : 0 ≤ l1 mu :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_le_card_mul_norm (mu : Wt Ψ N) (h : ‖mu‖ ≤ 2) : l1 mu ≤ (Fintype.card Ψ : ℝ) * (N * 2) := by
  have h1 : ∀ τ i, |mu τ i| ≤ 2 := fun τ i =>
    ((norm_le_pi_norm (mu τ) i).trans (norm_le_pi_norm mu τ)).trans h
  calc l1 mu ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => h1 τ i
    _ = _ := by simp

theorem rootHt_le (R : RootModel Ψ N) (t : ℝ) (mu : Wt Ψ N) (s D : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) (hw : ∀ j, |lineHt (R.line t j) L w| ≤ D) :
    rootHt R t mu s L w ≤ (l1 mu + |s|) * D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hw none)
  have h1 : ∀ j, R.coef mu s j * lineHt (R.line t j) L w ≤ |R.coef mu s j| * D := fun j =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _))
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hD
  rw [Fintype.sum_option, add_comm]
  refine add_le_add (le_of_eq ?_) ?_
  · simp [RootModel.coef, l1, Fintype.sum_prod_type]
  · have hk : (1 : ℝ) ≤ R.kA := by exact_mod_cast R.kA_pos
    simp only [RootModel.coef, abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) hk

theorem line_smooth (R : RootModel Ψ N) (t : ℝ) : ∀ j, IsSmoothHerm (R.line t j)
  | some r => R.x_smooth t r
  | none => R.A_smooth

theorem tower_upper : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
    (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  intro Ψ _ _ N T II R hII href c₀ hc₀
  obtain ⟨C, s₀, hs₀, href⟩ := href
  obtain ⟨θ₁, hθ₁, hθ₁1, hwt⟩ := GlobalTheory.T.dominant_weight_gap_shift Ψ N T.j T.nu c₀ T.j_pos T.j_lt hc₀
  choose D hD using fun c : T.Comp =>
    GlobalTheory.T.bounded_height_points_dense (R c).K (R c).ι (R c).P _ (R c).arith _ ((R c).line 1) (line_smooth (R c) 1)
  set D' : ℝ := ∑ c, |D c| with hD'
  have hDle : ∀ c, D c ≤ D' := fun c =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |D c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
  have hD'0 : 0 ≤ D' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Λ : ℝ := (Fintype.card Ψ : ℝ) * (N * 2) + 1 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨min θ₁ s₀, lt_min hθ₁ hs₀, 2 * (Λ * D' + |C|) + Λ * |C|, ?_⟩
  intro B hB c lam θ s _ hlam hθ hθle hs hgap hcg
  have hθ1 : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθs : θ ≤ s₀ := hθle.trans (min_le_right _ _)
  have hsθ : (s : ℝ) ≤ θ := by rw [hs]; nlinarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  obtain ⟨hdom, hnorm, -⟩ := hwt lam θ hlam hθ hθ1 hgap hcg
  rw [← hs] at hdom hnorm
  obtain ⟨i, u, hclose, harch⟩ := href B hB c
  have harch' := harch (T.lamS lam s) s hdom hnorm hs0 (hsθ.trans hθs)
  have hl : l1 (T.lamS lam s) + |(s : ℝ)| ≤ Λ := by
    rw [abs_of_pos hs0]
    exact add_le_add (l1_le_card_mul_norm _ hnorm) (by linarith)
  have hl0 : 0 ≤ l1 (T.lamS lam s) + |(s : ℝ)| := add_nonneg (weightAbsEntrySum_nonneg _) (abs_nonneg _)
  have hlog : 1 ≤ 2 * Real.log B := by
    have h2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
    have := Real.log_two_gt_d9
    linarith
  refine ⟨{W | (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ (2 * (Λ * D' + |C|) + Λ * |C|) * Real.log B}, ?_,
    fun W hW => hW⟩
  intro f hf hfP
  obtain ⟨L, _, _, L', _, _, e, w, z, hz, hw, hQ, hze, hfz⟩ :=
    GlobalTheory.T.join_model_points_lift Ψ N (T.M B c) (R c) i
      (fun L _ w => ∀ _ : NumberField L, ∀ j, |lineHt ((R c).line 1 j) L w| ≤ D c)
      (fun g hg hgP => by
        obtain ⟨L, _, _, w, hw, hgw, hb⟩ := hD c g hg hgP
        exact ⟨L, inferInstance, inferInstance, w, hw, hgw, fun _ => hb⟩) f hf hfP
  have hz₁ : (fun p => z (joinInl (T.M B c).ι (R c).ι p)) ∈ ptsOver L' (T.M B c).P := proj_inl_mem _ _ hz
  obtain ⟨hA, hle, hmem, hht⟩ := GlobalTheory.T.number_field_point_height _ _ II hII _ _ (T.M B c).arith L' _ hz₁
  refine ⟨mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p), ⟨⟨hA, hle⟩, ?_⟩, fun h => hfz ((hmem f hf).1 h)⟩
  have e1 : T.mbarHt II B c lam s (mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p)) =
      rootHt (T.M B c) (scale s) (T.lamS lam s) s L' (fun p => z (joinInl (T.M B c).ι (R c).ι p)) := by
    simp only [RootTower.mbarHt, RootModel.ht, rootHt, Finset.sum_div, mul_div_assoc]
    exact Finset.sum_congr rfl fun j _ => by rw [hht _ (line_smooth _ _ j)]
  have hcl := (GlobalTheory.T.root_height_difference_bound Ψ N (T.M B c) (R c) i u _ _ _ _ _ _ hclose harch' L' z hz).2
  have hR : rootHt (R c) 1 (T.lamS lam s) s L' (fun p => z (joinInr (T.M B c).ι (R c).ι p)) ≤
      (l1 (T.lamS lam s) + |(s : ℝ)|) * D' := by
    refine rootHt_le _ _ _ _ _ _ _ fun j => ?_
    have h := GlobalTheory.T.line_height_invariant_scaling _ _ ((R c).line 1 j) L L' e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simp only [one_mul] at h
    rw [hze, h]
    exact (hQ inferInstance j).trans (hDle c)
  rw [e1]
  have hlog0 : 0 ≤ Real.log B := by linarith
  have b1 : (l1 (T.lamS lam s) + |(s : ℝ)|) * D' ≤ Λ * D' := mul_le_mul_of_nonneg_right hl hD'0
  have b2 : (l1 (T.lamS lam s) + |(s : ℝ)|) * (C * Real.log B) ≤ Λ * (|C| * Real.log B) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0) hl0).trans
      (mul_le_mul_of_nonneg_right hl (mul_nonneg (abs_nonneg _) hlog0))
  have b3 : Λ * D' + |C| ≤ (Λ * D' + |C|) * (2 * Real.log B) :=
    le_mul_of_one_le_right (add_nonneg (mul_nonneg hΛ0 hD'0) (abs_nonneg _)) hlog
  have b4 := le_abs_self C
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.UpperTower
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.hodge_gram_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P → ∃ (M : LieModel Xo.univ.t.G (FU.u i P) (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ a w, ρ a w = fun k => ty k (a : E) * w k) ∧ (∀ w, IsDerivAt0 (fun z => (FU.ex i P z).left) w (M.pt w).left) ∧ ∀ τ w, HT.eigProj ρ τ w = tyPart ty τ w := by
  first | exact @PositivityTheory.Xgf.lie_model_with_cm_action | exact PositivityTheory.Xgf.lie_model_with_cm_action
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.sandwich_point_over_field_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich | exact GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich <;> assumption)
end
