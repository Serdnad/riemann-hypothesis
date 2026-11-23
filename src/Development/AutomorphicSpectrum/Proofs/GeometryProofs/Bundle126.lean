module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfIsIntegralLoc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle117
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.snc_chart_local_normal_form : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | exact GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom

theorem exists_den {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (φ : R →+* A) {f : A} (hf : f ≠ 0) (T : Set (R × R × A))
    (hT : ∀ q ∈ T, q.2.1 ≠ 0 ∧ φ q.2.1 * q.2.2 = φ q.1 * f) :
    ∃ D : R, D ≠ 0 ∧ ∀ q ∈ T, φ q.2.1 ∣ φ (D * q.1) := by
  classical
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    ((fun q : R × R × A => q.2.2) '' T)).1
    (IsNoetherian.noetherian (Ideal.span ((fun q : R × R × A => q.2.2) '' T)))
  have hex : ∀ g ∈ s, ∃ q ∈ T, q.2.2 = g := fun g hg => by
    obtain ⟨q, hq, rfl⟩ := hsS hg
    exact ⟨q, hq, rfl⟩
  choose! q hqT hqg using hex
  refine ⟨∏ g ∈ s, (q g).2.1, Finset.prod_ne_zero_iff.2 fun g hg => (hT _ (hqT g hg)).1, ?_⟩
  set D := ∏ g ∈ s, (q g).2.1 with hD
  have key : ∀ a ∈ Submodule.span A (s : Set A), ∃ b, φ D * a = b * f := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg =>
      have hg' : g ∈ s := hg
      refine ⟨φ (∏ g' ∈ s.erase g, (q g').2.1) * φ (q g).1, ?_⟩
      have e := (hT _ (hqT g hg')).2
      rw [hqg g hg'] at e
      rw [hD, ← Finset.prod_erase_mul s _ hg', map_mul, _root_.mul_assoc, e, _root_.mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [mul_add, ha', hb', add_mul]⟩
    | smul c a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      refine ⟨c * a', ?_⟩
      rw [smul_eq_mul, mul_left_comm, ha', _root_.mul_assoc]
  intro r hr
  obtain ⟨b, hb⟩ := key r.2.2 (by
    rw [← hs]
    exact Ideal.subset_span ⟨r, hr, rfl⟩)
  refine ⟨b, mul_right_cancel₀ hf ?_⟩
  have e := (hT r hr).2
  calc φ (D * r.1) * f = φ D * (φ r.1 * f) := by rw [map_mul, _root_.mul_assoc]
    _ = φ r.2.1 * (φ D * r.2.2) := by rw [← e, mul_left_comm]
    _ = φ r.2.1 * b * f := by rw [hb, _root_.mul_assoc]

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}}

theorem f_ne_zero [IsIntegral X] {p : X ⟶ Sp R} {M : LB X} {t : SecMod p M} {i j : M.ι}
    (hi : LB.Sec.f t i ≠ 0) (hj : (M.U j : Set X).Nonempty) : LB.Sec.f t j ≠ 0 := by
  intro h0
  have hine : (M.U i : Set X).Nonempty := by
    by_contra hc
    have hb : M.U i = ⊥ := by
      ext x
      simp only [Set.not_nonempty_iff_eq_empty] at hc
      simp [hc]
    have : Subsingleton Γ(X, M.U i) := by
      rw [hb]
      infer_instance
    exact hi (Subsingleton.elim _ _)
  have hne : ((M.U i ⊓ M.U j : X.Opens) : Set X).Nonempty :=
    nonempty_preirreducible_inter (M.U i).isOpen (M.U j).isOpen hine hj
  have : Nonempty (M.U i ⊓ M.U j : X.Opens) := hne.to_subtype
  have e := LB.Sec.compat t i j
  rw [h0, map_zero, MulZeroClass.mul_zero] at e
  refine hi (map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) ?_)
  exact e.trans (map_zero _).symm

theorem exists_den_open [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp R) (M : LB X) (t : SecMod p M) (j : M.ι)
    (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) (hVj : V ≤ M.U j) (ht : LB.Sec.f t j ≠ 0) :
    ∃ D : R, D ≠ 0 ∧ ∀ (x d : R) (u : SecMod p M), d ≠ 0 → d • u = x • t →
      constHom p V d ∣ constHom p V (D * x) := by
  have : Nonempty V := hne.to_subtype
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let r := (X.presheaf.map (homOfLE hVj).op).hom
  have hinj : Function.Injective r := map_injective_of_isIntegral X (homOfLE hVj)
  obtain ⟨D, hD, h⟩ := exists_den (constHom p V) (f := r (LB.Sec.f t j))
    (fun h0 => ht (hinj (by rw [map_zero]; exact h0)))
    {q | q.2.1 ≠ 0 ∧ constHom p V q.2.1 * q.2.2 = constHom p V q.1 * r (LB.Sec.f t j)} fun q hq => hq
  refine ⟨D, hD, fun x d u hd e => h (x, d, r (LB.Sec.f u j)) ⟨hd, ?_⟩⟩
  have e' := congrArg r (congrArg (fun s : SecMod p M => LB.Sec.f s j) e)
  simp only [smul_f, r, map_mul, res_constFn] at e'
  exact e'

theorem dvd_of_forall_point (p : X ⟶ Sp R) [Flat p] (hp : Function.Surjective p) {a b : R} (ha : a ≠ 0)
    (h : ∀ y : X, cst p y a ∣ cst p y b) : a ∣ b := by
  have hh : ∀ z ∈ (⊤ : (Sp R).Opens), cst (𝟙 (Sp R)) z a ∣
      gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
    intro z _
    obtain ⟨y, rfl⟩ := hp z
    apply dvd_descend p y
    rw [cst, ← gs_stalkMap p y ⊤ trivial, ← gs_stalkMap p y ⊤ trivial]
    exact h y
  obtain ⟨g, hg⟩ := exists_div (𝟙 (Sp R)) ha ⊤ _ hh
  have e : constFn (𝟙 (Sp R)) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
    have e₀ : (𝟙 (Sp R) : Sp R ⟶ Sp R).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Sp R).presheaf.map_id _
    rw [constFn, e₀]
    rfl
  rw [e] at hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g, ?_⟩
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hg
  simpa using this

theorem bounded_denominators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB →
    ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t →
      d ∣ d₀ * x := by
  classical
  intro R _ _ _ G _ _ _ _ M hM t ht
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hsurj : Function.Surjective G.hom := (inferInstance : Surjective G.hom).surj
  obtain ⟨i₀, hi₀⟩ : ∃ i, LB.Sec.f t i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ht (SecMod.ext fun i => by rw [hc i]; rfl)
  have hc : ∀ y : G.left, ∃ j, y ∈ M.U j := fun y => by
    have : y ∈ (⨆ i, M.U i : G.left.Opens) := by rw [hM.cover]; trivial
    simpa using this
  choose j hj using hc
  have hV : ∀ y : G.left, ∃ V : G.left.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ M.U (j y) := fun y => by
    obtain ⟨V, hVa, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (hj y)
    exact ⟨V, hVa, hy, hle⟩
  choose V hVa hVy hVj using hV
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun y => (V y : Set G.left))
    (fun y => (V y).isOpen.mem_nhds (hVy y))
  have hD := fun y => exists_den_open G.hom M t (j y) (V y) (hVa y) ⟨y, hVy y⟩ (hVj y)
    (f_ne_zero hi₀ ⟨y, hj y⟩)
  choose D hD0 hD using hD
  refine ⟨∏ y ∈ s, D y, Finset.prod_ne_zero_iff.2 fun y _ => hD0 y, fun x d u hd e => ?_⟩
  refine dvd_of_forall_point G.hom hsurj hd fun y => ?_
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ s, y ∈ V w := by
    have : y ∈ ⋃ x ∈ s, (V x : Set G.left) := by rw [hs]; trivial
    simpa using this
  have h₁ : constHom G.hom (V w) d ∣ constHom G.hom (V w) ((∏ y ∈ s, D y) * x) := by
    refine (hD w x d u hd e).trans (map_dvd _ ?_)
    exact mul_dvd_mul_right (Finset.dvd_prod_of_mem _ hw) _
  obtain ⟨c, hc⟩ := h₁
  have e' := congrArg (gs (𝟙 G.left) y (V w)) hc
  rw [constHom_apply, constHom_apply, gs_mul _ y _ hyw, gs_constFn _ _ _ y hyw, gs_constFn _ _ _ y hyw,
    Category.id_comp] at e'
  exact ⟨_, e'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  first | exact @PositivityTheory.Xgn.sequence_ring_exists | exact PositivityTheory.Xgn.sequence_ring_exists
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.hodge_comp_descent_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | exact GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.hodge_comp_descent_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks | exact GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.log_resolution_potential_pullback : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | exact GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp

theorem iter_sum {B J : Type} [AddCommMonoid B] (D : B →+ B) (s : Finset J) (k : ℕ) (g : J → B) :
    D^[k] (∑ j ∈ s, g j) = ∑ j ∈ s, D^[k] (g j) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]

    rw [map_sum, ih]

theorem iter_const_mul {B : Type} [CommRing B] (D : B →+ B) (c : B) (hc : ∀ g, D (c * g) = c * D g) (k : ℕ) (g : B) :
    D^[k] (c * g) = c * D^[k] g := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [hc, ih]

theorem jet_cmp_ring {B K : Type} [CommRing B] [Field K] (D : B →+ B)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : B →+* K) (r : ℕ) (c a a' : Fin r → B) (u : B)
    (hc : ∀ j g, D (c j * g) = c j * D g) (hu : e u ≠ 0) (ha : ∀ j, a j = u * a' j) (i : ℕ)
    (h : ∀ k < i, ∑ j, e (c j) * e (D^[k] (a j)) = 0) :
    ∑ j, e (c j) * e (D^[i] (a j)) = e u * ∑ j, e (c j) * e (D^[i] (a' j)) := by
  have hval : ∀ (b : Fin r → B) (k : ℕ), e (D^[k] (∑ j, c j * b j)) = ∑ j, e (c j) * e (D^[k] (b j)) := by
    intro b k

    rw [iter_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iter_const_mul D (c j) (hc j), map_mul]
  have hΦ : ∑ j, c j * a j = u * ∑ j, c j * a' j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]; ring
  have h1 : ∀ k < i, e (D^[k] (u * ∑ j, c j * a' j)) = 0 := by
    intro k hk
    rw [← hΦ, hval]; exact h k hk
  have h2 := jet_vanish_of_mul D hD e u _ hu i h1
  have h3 := jet_mul_of_vanish D hD e i u _ h2
  rw [← hΦ, hval, hval] at h3
  exact h3

theorem iter_der_res {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (v : epsAt (𝟙 (Sp R)) ⟶ G)
    (hv : IsTanAt G (𝟙 (Sp R)) v) {V V' : G.left.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (le : V' ≤ V) (k : ℕ) (g : Γ(G.left, V)) :
    (der v hv hV')^[k] ((G.left.presheaf.map (homOfLE le).op).hom g) =
      (G.left.presheaf.map (homOfLE le).op).hom ((der v hv hV)^[k] g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [der_res v hv hV hV' le, ih]

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (l1 : V ≤ U) (l2 : W ≤ V) (l3 : W ≤ U) (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE l2).op).hom ((X.presheaf.map (homOfLE l1).op).hom g) =
      (X.presheaf.map (homOfLE l3).op).hom g := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem jet_cmp : ∀ (R K : Type) [CommRing R] [Field K] (G : Over (Sp R)) [GrpObj G] (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (y : Sp K ⟶ G.left) (V₀ V₁ : G.left.Opens) (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (t₀ : ⊤ ≤ y ⁻¹ᵁ V₀) (t₁ : ⊤ ≤ y ⁻¹ᵁ V₁) (t : ⊤ ≤ y ⁻¹ᵁ (V₀ ⊓ V₁)) (r : ℕ) (f : Fin r → Γ(G.left, V₀)) (f' : Fin r → Γ(G.left, V₁)) (uu : Γ(G.left, V₀ ⊓ V₁)), ev y _ t uu ≠ 0 → (∀ j, (G.left.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom (f j) = uu * (G.left.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom (f' j)) → ∀ (i : ℕ) (c : Fin r → R), (∀ k < i, ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[k] (f j)) = 0) → ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[i] (f j)) = ev y _ t uu * ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₁ t₁ ((der v₀ hv₀ h₁)^[i] (f' j)) := by
  intro R K _ _ G _ v₀ hv₀ y V₀ V₁ h₀ h₁ t₀ t₁ t r f f' uu hu hf i c hyp
  obtain ⟨W, hWa, hWy, hWle'⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.left) (x := y (default : PrimeSpectrum K)) (U := V₀ ⊓ V₁) (t (show _ ∈ (⊤ : (Sp K).Opens) from trivial))
  have hWle : W ≤ V₀ ⊓ V₁ := hWle'
  have tW : ⊤ ≤ y ⁻¹ᵁ W := by
    intro p _
    rw [Subsingleton.elim p (default : PrimeSpectrum K)]
    exact hWy
  have l0 : W ≤ V₀ := hWle.trans inf_le_left
  have l1 : W ≤ V₁ := hWle.trans inf_le_right
  have key := jet_cmp_ring (der v₀ hv₀ hWa) (der_mul v₀ hv₀ hWa) (ev y W tW) r
    (fun j => constFn G.hom W (c j))
    (fun j => (G.left.presheaf.map (homOfLE l0).op).hom (f j))
    (fun j => (G.left.presheaf.map (homOfLE l1).op).hom (f' j))
    ((G.left.presheaf.map (homOfLE hWle).op).hom uu)
    (fun j g => der_const_mul v₀ hv₀ hWa (c j) g)
    (by rw [ev_res y hWle t tW]; exact hu)
    (fun j => by
      have := congrArg (G.left.presheaf.map (homOfLE hWle).op).hom (hf j)
      rw [map_mul, res_res _ _ l0, res_res _ _ l1] at this
      exact this)
    i
    (fun k hk => by
      have := hyp k hk
      simp only [iter_der_res v₀ hv₀ h₀ hWa l0, ev_res y l0 t₀ tW, ev_const]
      exact this)
  simp only [iter_der_res v₀ hv₀ h₀ hWa l0, iter_der_res v₀ hv₀ h₁ hWa l1, ev_res y l0 t₀ tW, ev_res y l1 t₁ tW,
    ev_res y hWle t tW, ev_const] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer

theorem ev_pull {C : Type} [CommRing C] {Y Y' : Scheme.{0}} (x : Sp C ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens)
    (h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (f : Γ(Y', U)) :
    ev x (ψ ⁻¹ᵁ U) h' (ψ.app U f) = ev (x ≫ ψ) U h f := by
  simp only [ev, RingHom.comp_apply, Scheme.Hom.comp_appLE, CommRingCat.hom_comp]

theorem valAt'_pull {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (ψ ⁻¹ᵁ U) (ψ.app U f) = valAt' (x ≫ ψ) U f := by
  by_cases h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dite_eq_left h, dite_eq_left h']
    exact ev_pull x ψ U h h' f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dite_eq_right h, dite_eq_right h']

theorem tr_eq_pull {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A]
    {z : Sp ℂ ⟶ Sp R} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G)
    (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v' : epsR ℂ ⟶ A)
    (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) :
    tr v₀ (a.left ≫ φ) = ((toUnit (epsR ℂ) ≫ a) * v').left ≫ φ := by
  have hb : (a.left ≫ φ) ≫ G.hom = z := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w a]
    exact Category.id_comp z
  let J : Over.mk ((epsR ℂ).hom ≫ z) ⟶ epsAt ((a.left ≫ φ) ≫ G.hom) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (a.left ≫ φ) ≫ G.hom = (epsR ℂ).hom ≫ z
      rw [hb, Category.id_comp]
      rfl)
  let P := piE ((a.left ≫ φ) ≫ G.hom) ≫ (Over.homMk (a.left ≫ φ) rfl : Over.mk ((a.left ≫ φ) ≫ G.hom) ⟶ G)
  let Q := rhoE ((a.left ≫ φ) ≫ G.hom) ≫ v₀
  have e := h.2 (epsR ℂ) (toUnit (epsR ℂ) ≫ a) v' (J ≫ P) (J ≫ Q) ?_ ?_
  · rw [← MonObj.comp_mul] at e
    have e' : (J ≫ (P * Q)).left = (P * Q).left := Category.id_comp _
    rw [← e, e']
    rfl
  · have hu : (toUnit (epsR ℂ)).left = (epsR ℂ).hom := (Over.w (toUnit (epsR ℂ))).symm ▸ (Category.comp_id _).symm
    show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ a.left ≫ φ = (toUnit (epsR ℂ) ≫ a).left ≫ φ
    rw [Over.comp_left, hu, Category.id_comp, Category.assoc]
    rfl
  · show 𝟙 _ ≫ spMap (dualMap (bmap ((a.left ≫ φ) ≫ G.hom))) ≫ v₀.left = v'.left ≫ φ
    rw [hb, Category.id_comp, hv]

theorem fderiv_valAt_eq_der (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left)
    (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ)
    (v' : epsR ℂ ⟶ A) (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) (hd : u.IsDiff c v')
    (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ)
    (hw : ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V) :
    fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c =
      valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  let t : A ⟶ A := (toUnit A ≫ u.ex w) * 𝟙 A
  have hE : v' ≫ t = (toUnit (epsR ℂ) ≫ u.ex w) * v' := by
    have e : v' ≫ toUnit A = toUnit (epsR ℂ) := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e]
  have ht : ∀ x, u.ex x ≫ t = u.ex (w + x) := by
    intro x
    have e : u.ex x ≫ toUnit A = 𝟙 _ := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e, Category.id_comp, u.ex_add]
  have htr : tr v₀ ((u.ex w).left ≫ φ) = v'.left ≫ t.left ≫ φ := by
    rw [tr_eq_pull h v₀ (u.ex w) v' hv, ← hE, Over.comp_left, Category.assoc]
  have hT := tr_top v₀ hv₀ _ V hw
  have hU : ⊤ ≤ v'.left ⁻¹ᵁ ((t.left ≫ φ) ⁻¹ᵁ V) := by
    have h2 := hT
    rw [htr] at h2
    exact h2
  have key := hd ((t.left ≫ φ) ⁻¹ᵁ V) hU ((t.left ≫ φ).app V f)
  have hF : (fun x => valAt' (u.ex x).left ((t.left ≫ φ) ⁻¹ᵁ V) ((t.left ≫ φ).app V f)) =
      fun x => (fun x => valAt' ((u.ex x).left ≫ φ) V f) (w + x) := by
    funext x
    rw [valAt'_pull, ← Category.assoc, ← Over.comp_left, ht]
  have hG := fderiv_comp_add_left (𝕜 := ℂ) (f := fun x => valAt' ((u.ex x).left ≫ φ) V f) (x := 0) w
  rw [add_zero] at hG
  rw [hF, hG] at key
  rw [← key, valAt', dite_eq_left hw]
  have e1 := snd_ev_tr v₀ hv₀ hV ((u.ex w).left ≫ φ) hw hT f
  have hT' : ⊤ ≤ (v'.left ≫ t.left ≫ φ) ⁻¹ᵁ V := hU
  have e2 : ev (v'.left ≫ t.left ≫ φ) V hT' f = ev (tr v₀ ((u.ex w).left ≫ φ)) V hT f :=
    congrArg (fun m => m f) (ev_congr htr.symm V hT' hT)
  have e3 := ev_pull v'.left (t.left ≫ φ) V hT' hU f
  exact (congrArg TrivSqZeroExt.snd (e3.trans e2)).trans e1

end GlobalTheory.CompanionTheory.Ar.InvDer
end
end
