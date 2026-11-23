module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ThetaQuotient

theorem eval_div_of_isHomogeneous {σ : Type*} {F : MvPolynomial σ ℂ} {d : ℕ} (hF : F.IsHomogeneous d) (v : σ → ℂ)
    (t : ℂ) : MvPolynomial.eval (fun i => v i / t) F = MvPolynomial.eval v F / t ^ d := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hd, mul_div_assoc]

theorem valAt'_eval₂ {σ : Type*} {X : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {U : X.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : σ → Γ(X.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) F := by
  have hx : x.left ≫ X.hom = 𝟙 _ := Over.w x
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact valAt'_constFn x.left X.hom hx U a h
  | add p q hp hq => rw [MvPolynomial.eval₂_add, map_add (f := _), valAt'_add, hp, hq]
  | mul_X p i hp => rw [MvPolynomial.eval₂_mul, map_mul, valAt'_mul, hp, MvPolynomial.eval₂_X, MvPolynomial.eval_X]

theorem exists_glue_of_values {X : Over (Sp ℂ)}
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)),
      (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    {κ : Type} (V : κ → X.left.Opens) (s : ∀ i, Γ(X.left, V i)) (a : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ)
    (hs : ∀ i x, ⊤ ≤ x.left ⁻¹ᵁ V i → valAt' x.left (V i) (s i) = a x) :
    ∃ φ : Γ(X.left, ⨆ i, V i), ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ (⨆ i, V i) →
      valAt' x.left (⨆ i, V i) φ = a x := by
  obtain ⟨φ, hφ, -⟩ := X.left.sheaf.existsUnique_gluing V s (by
    intro i j
    refine hext _ _ _ fun x hx => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x.left _ _).1 hx
    refine (valAt'_map x.left _ (s i) hx).trans (Eq.trans ?_ (valAt'_map x.left _ (s j) hx).symm)
    rw [hs i x hi, hs j x hj])
  refine ⟨φ, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem x.left _).1 hx)
  have hi' := (top_le_preimage_iff_mem x.left _).2 hi
  rw [← hs i x hi', ← hφ i]
  exact (valAt'_map x.left _ φ hi').symm

theorem exists_div_basicOpen {X : Scheme.{0}} {U : X.Opens} (f g : Γ(X, U)) :
    ∃ s : Γ(X, X.basicOpen g), ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ X.basicOpen g →
      valAt' x (X.basicOpen g) s = valAt' x U f / valAt' x U g := by
  have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f * (u⁻¹).val, fun x hx => ?_⟩
  have h1 : valAt' x (X.basicOpen g) u.val = valAt' x U g := by
    rw [hu]
    exact valAt'_map x _ g hx
  rw [valAt'_mul, valAt'_map x _ f hx, div_eq_mul_inv, ← h1]
  congr 1
  exact valAt'_units_inv x hx u

end ThetaQuotient


open ThetaQuotient in
theorem theta_quotient_regular : (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z))) := by
  intro hext g τ _ N _ hpoly X ex D ⟨hint, hprop, hsurj, _, _, hD, hcov⟩ d p q hp hq
  have hext' := hext X inferInstance inferInstance
  obtain ⟨P, hP, hPv⟩ := hpoly d p hp
  obtain ⟨Q, hQ, hQv⟩ := hpoly d q hq
  generalize hθ : (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) = θ
  have hθ' : ∀ c z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = θ c z :=
    fun c z => congrFun (congrFun hθ c) z
  simp only [hθ'] at hD hPv hQv
  have hmem : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ θ c z ≠ 0 := fun c => (hD c).2.2.1
  choose r hr using fun c => (hD c).2.2.2
  have hφ : ∀ (F : MvPolynomial (Fin g → Fin N) ℂ), F.IsHomogeneous d → ∀ c, ∃ φ : Γ(X.left, D c), ∀ z, θ c z ≠ 0 →
      valAt' (ex z).left (D c) φ = MvPolynomial.eval (fun c' => θ c' z) F / θ c z ^ d := by
    intro F hF c
    refine ⟨_, fun z hz => (valAt'_eval₂ (ex z) ((hmem c z).2 hz) (r c) F).trans ?_⟩
    rw [← eval_div_of_isHomogeneous hF]
    congr 2
    funext c'
    exact (hr c).1 c' z hz
  choose φp hφp using hφ P hP
  choose φq hφq using hφ Q hQ
  simp only [← hPv, ← hQv] at hφp hφq
  choose s hs using fun c => exists_div_basicOpen (φp c) (φq c)
  have hV : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) ↔ θ c z ≠ 0 ∧ q z ≠ 0 := by
    intro c z
    rw [top_le_preimage_basicOpen_iff]
    constructor
    · intro h
      have h1 := (hmem c z).1 (top_le_preimage_of_valAt'_ne_zero _ h)
      rw [hφq c z h1] at h
      exact ⟨h1, fun h0 => h (by rw [h0, zero_div])⟩
    · rintro ⟨h1, h2⟩
      rw [hφq c z h1]
      exact div_ne_zero h2 (pow_ne_zero _ h1)
  have hsv : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) →
      valAt' (ex z).left _ (s c) = p z / q z := by
    intro c z h
    obtain ⟨h1, _⟩ := (hV c z).1 h
    rw [hs c _ h, hφp c z h1, hφq c z h1, div_div_div_cancel_right₀ (pow_ne_zero _ h1)]
  choose σ hσ using hsurj
  obtain ⟨φ, hφ⟩ := exists_glue_of_values hext' (fun c => X.left.basicOpen (φq c)) s (fun x => p (σ x) / q (σ x))
    (fun c x hx => by
      have := hsv c (σ x) (by rw [hσ]; exact hx)
      rwa [hσ] at this)
  have hU : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (⨆ c, X.left.basicOpen (φq c)) ↔
      ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z
    refine (top_le_preimage_iff_mem _ _).trans (TopologicalSpace.Opens.mem_iSup.trans (exists_congr fun c => ?_))
    exact (top_le_preimage_iff_mem _ _).symm
  have hU' : ∀ z, q z ≠ 0 → ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z hz
    have : (ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hcov]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨c, (hV c z).2 ⟨(hmem c z).1 ((top_le_preimage_iff_mem _ _).2 hc), hz⟩⟩
  refine ⟨_, φ, fun z => ⟨⟨fun h => ?_, fun h => (hU z).2 (hU' z h)⟩, fun h => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (hU z).1 h
    exact ((hV c z).1 hc).2
  · obtain ⟨c, hc⟩ := hU' z h
    rw [hφ _ ((hU z).2 ⟨c, hc⟩), ← hsv c z hc]
    have := hsv c (σ (ex z)) (by rw [hσ]; exact hc)
    rw [hσ] at this
    exact this.symm

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaOnto

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  unfold constFn
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {K : Type}
    [Fintype K] (a : K → R) (s : K → L.Sec) : L.Sec where
  f j := ∑ i, constFn p _ (a i) * (s i).f j
  compat j k := by

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (s i).compat j k]
    ring

def secConst {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (L : LB X) (a : R) :
    (lbPow L 0).Sec where
  f j := constFn p _ a
  compat j k := by
    have : (lbPow L 0).g j k = 1 := by
      unfold lbPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [res_constFn, res_constFn, this, Units.val_one, _root_.one_mul]

theorem mem_span_of_card_le {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V → Prop) {N : ℕ}
    (hN : ∀ (M : ℕ) (f : Fin M → V), (∀ k, Q (f k)) → LinearIndependent ℂ f → M ≤ N)
    (f : Fin N → V) (hf : ∀ k, Q (f k)) (hli : LinearIndependent ℂ f) {v : V} (hv : Q v) :
    ∃ a : Fin N → ℂ, ∑ i, a i • f i = v := by
  by_contra hne
  have hv' : v ∉ Submodule.span ℂ (Set.range f) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact hne
  have hli' : LinearIndependent ℂ (Fin.cons v f : Fin (N + 1) → V) :=
    linearIndependent_finCons.mpr ⟨hli, hv'⟩
  have hQ : ∀ k, Q ((Fin.cons v f : Fin (N + 1) → V) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hf i
  have := hN (N + 1) _ hQ hli'
  omega

theorem theta_from_section :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) := by
  intro hval hdim hsec hfun P u Hm χ Ef hAH hfr hEf n θ hθ
  have hpt : ∀ z, (u.ex z).left ≫ P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hconst : ∀ z (U : P.A.left.Opens) (a : ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      valAt' (u.ex z).left U (constFn P.A.hom U a) = a :=
    fun z U a hU => (hval _ _).2.2.2.2.2 P.A.hom (hpt z) U a hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hper : ∀ (l : u.Λ) z, θ (z + l) = θ z := fun l z => by
      rw [hθ.2 l z, pow_zero, _root_.one_mul]
    have := u.discrete
    have : IsZLattice ℝ u.Λ := ⟨u.full⟩
    let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
    have hb : Bornology.IsBounded (Set.range θ) := by
      have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (ZSpan.fundamentalDomain_isBounded b).closure
      refine (hK.image hθ.1.continuous).isBounded.subset ?_
      rintro _ ⟨z, rfl⟩
      refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
      have hfl : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ u.Λ := by
        have h : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ Submodule.span ℤ (Set.range b) :=
          (ZSpan.floor b z).2
        exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ).le h
      rw [← hper ⟨_, hfl⟩ (ZSpan.fract b z), ZSpan.fract_apply, sub_add_cancel]
    have hc : ∀ z, θ z = θ 0 := fun z => hθ.1.apply_eq_apply_of_bounded hb z 0
    refine ⟨secConst P.A.hom P.L (θ 0), ?_⟩
    intro j z hz
    show valAt' _ _ (constFn P.A.hom _ (θ 0)) = _
    rw [hconst z _ _ hz, pow_zero, _root_.mul_one, hc z]
  ·
    obtain ⟨s, hs⟩ := hsec P n hn
    have hex : ∀ i, ∃ T, u.IsThetaFn Hm χ n T ∧ u.IsFnPow n (s i) T :=
      fun i => ((hfun P u Hm χ Ef hfr n).1 (s i)).exists
    choose T hT using hex
    have hcomb : ∀ a : Fin (n ^ P.g) → ℂ,
        u.IsFnPow n (secComb P.A.hom a s) (fun z => ∑ i, a i * T i z) := by
      intro a j z hz
      obtain ⟨e, he⟩ := (hval _ (u.ex z).left).2.1 _ hz
      have hca : ∀ i, e (constFn P.A.hom ((lbPow P.L n).U j) (a i)) = a i := fun i => by
        rw [← he]; exact hconst z _ (a i) hz
      have hsi : ∀ i, e ((s i).f j) = T i z * u.fr (j PUnit.unit) z ^ n := fun i => by
        rw [← he]; exact (hT i).2 j z hz
      rw [he]
      show e (∑ i, constFn P.A.hom _ (a i) * (s i).f j) = _

      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hca, hsi, _root_.mul_assoc]
    have hli : LinearIndependent ℂ T := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hz : ∀ z, ∑ i, a i * T i z = 0 := fun z => by
        simpa [Finset.sum_apply] using congrFun ha z
      have h0 : u.IsFnPow n (secComb P.A.hom (0 : Fin (n ^ P.g) → ℂ) s)
          (fun z => ∑ i, a i * T i z) := by
        intro j z hz'
        rw [hcomb 0 j z hz']
        simp [hz]
      have heq := (hfun P u Hm χ Ef hfr n).2 _ _ _ (hcomb a) h0
      have ha0 : a = 0 := by
        apply hs a
        intro j
        have hj := congrArg (fun t => LB.Sec.f t j) heq
        simp only [secComb] at hj
        rw [hj]
        simp [constFn_zero]
      intro i
      rw [ha0]
      rfl
    obtain ⟨a, ha⟩ := mem_span_of_card_le (u.IsThetaFn Hm χ n)
      (fun M f hf hlin => hdim P.g u.Λ u.discrete u.full Hm χ Ef hfr.1 hAH.2.1 hfr.2.1 hfr.2.2.1 hEf
        n hn M f (fun k => ⟨(hf k).1, fun l z => (hf k).2 l z⟩) hlin)
      T (fun i => (hT i).1) hli hθ
    refine ⟨secComb P.A.hom a s, ?_⟩
    intro j z hz
    rw [hcomb a j z hz, ← ha]
    simp [Finset.sum_apply]

end GlobalTheory.ThetaOnto
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

include e in
theorem chart_eq (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) := by
  ext y
  have h : σ (ρ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  constructor
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have := Set.mem_iInter.1 hy PUnit.unit
    show σ (ρ y) ∈ L.U (j PUnit.unit)
    rw [h]; exact this
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have : σ (ρ y) ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy 0
    rw [h] at this; exact this

theorem appLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V h₁ = g.appLE U V h₂ := by subst h; rfl

def down (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) :
    (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)).Sec where
  f j := (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (b.f (fun _ => j PUnit.unit))
  compat i j := by
    have hle : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j ≤
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      inf_le_inf (chart_eq L σ ρ e i).le (chart_eq L σ ρ e j).le
    have := congrArg (ρ.appLE _ _ hle).hom (b.compat (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    replace this := this.trans (map_mul _ _ _)
    refine Eq.trans ?_ (this.trans (congrArg₂ (· * ·) ?_ ?_))
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)

theorem appLE_injective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (ρ.app U)).1

end Transport

attribute [local instance] Over.cartesianMonoidalCategory


open Out in
theorem exists_indep_sections (H : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ,
      (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0 := by
  have hr := H ℂ P n hn
  let T : Over (Sp ℂ) := baseOver (Sp ℂ)
  let c : Γ(T.left, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  haveI : Nontrivial Γ(T.left, ⊤) := c.symm.injective.nontrivial
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hr.ge
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨fun i => down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A (b i)), fun a ha => ?_⟩
  have h0 : ∑ i, c.symm (a i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  funext i
  exact c.symm.injective ((Fintype.linearIndependent_iff.1 hb _ h0 i).trans (map_zero _).symm)

end GlobalTheory.PowSec
end
end
