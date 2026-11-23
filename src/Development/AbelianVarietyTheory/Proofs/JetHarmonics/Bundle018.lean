module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zero' (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero, AddMonoidHom.zero_apply] at h
  omega

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nonneg_of_pos (hQ : ∀ x, 2 * Q x = Bf x x) (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x)
    (x : X) : 0 ≤ Q x := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
  · linarith [hpos x hx]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_eq_add_add_bilin (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (x y : X) : Q (x + y) = Q x + Q y + Bf x y := by
  have h := hQ (x + y)
  simp only [map_add (f := _), AddMonoidHom.add_apply] at h
  linarith [hQ x, hQ y, hsym y x]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (k : ℤ) (x : X) :
    Q (k • x) = k ^ 2 * Q x := by
  have h := hQ (k • x)
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at h
  have h2 : 2 * Q (k • x) = 2 * (k ^ 2 * Q x) := by rw [h, ← hQ x]; ring
  exact mul_left_cancel₀ two_ne_zero h2

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma bilin_sq_le_four_mul_quad (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) (x y : X) : Bf x y ^ 2 ≤ 4 * Q x * Q y := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
    simp
  · have hx1 := hpos x hx
    have hw := quad_nonneg_of_pos hQ hpos (Bf x y • x + (-(2 * Q x)) • y)
    rw [quad_add_eq_add_add_bilin hsym hQ, quad_zsmul' hQ, quad_zsmul' hQ] at hw
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at hw
    nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_le_add_sq_mul (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) {x y : X} {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hx : (Q x : ℝ) ≤ a ^ 2 * C) (hy : (Q y : ℝ) ≤ b ^ 2 * C) :
    (Q (x + y) : ℝ) ≤ (a + b) ^ 2 * C := by
  have hcs : (Bf x y : ℝ) ^ 2 ≤ 4 * (Q x : ℝ) * Q y := by
    exact_mod_cast bilin_sq_le_four_mul_quad hsym hQ hpos x y
  have hx0 : (0 : ℝ) ≤ Q x := by exact_mod_cast quad_nonneg_of_pos hQ hpos x
  have hy0 : (0 : ℝ) ≤ Q y := by exact_mod_cast quad_nonneg_of_pos hQ hpos y
  have hprod : (Q x : ℝ) * Q y ≤ (a ^ 2 * C) * (b ^ 2 * C) :=
    mul_le_mul hx hy hy0 (by positivity)
  have hB : (Bf x y : ℝ) ≤ 2 * a * b * C := by
    have h2 : (Bf x y : ℝ) ^ 2 ≤ (2 * a * b * C) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  have hadd : (Q (x + y) : ℝ) = Q x + Q y + Bf x y := by
    exact_mod_cast quad_add_eq_add_add_bilin hsym hQ x y
  rw [hadd]
  nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (m : ℕ) (x : X) :
    Q (m • x) = (m : ℤ) ^ 2 * Q x := by
  have h := quad_zsmul' hQ (m : ℤ) x
  rwa [natCast_zsmul] at h


variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
theorem _root_.GlobalTheory.small_combination_strict_min_mod :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) →
    (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) →
    ∀ (n D q : ℕ) (b : Fin n → X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) →
    (∀ j z, |(Bf (b j) z : ℝ)| ≤ M₀ * Q z) → (D : ℝ) * M₀ < q →
    ∀ e : Fin n → ℕ, ∑ j, e j ≤ D →
    ((Q (∑ j, e j • b j) : ℝ) ≤ (D : ℝ) ^ 2 * Cc) ∧
      ∀ z, z ≠ 0 → Q (∑ j, e j • b j) < Q (∑ j, e j • b j + q • z) := by
  intro X _ Bf Q hsym hQ hpos n D q b Cc M₀ hCc hM₀ hb hBb hq e he
  have hsumR : (∑ j, (e j : ℝ)) ≤ D := by exact_mod_cast he
  have hsum0 : (0 : ℝ) ≤ ∑ j, (e j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  constructor
  · have key : ∀ s : Finset (Fin n),
        (Q (∑ j ∈ s, e j • b j) : ℝ) ≤ (∑ j ∈ s, (e j : ℝ)) ^ 2 * Cc := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp [quad_zero' hQ]
      · intro j s hj ih
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        refine quad_add_le_add_sq_mul hsym hQ hpos (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hCc ?_ ih
        rw [quad_nsmul' hQ]
        push_cast
        exact mul_le_mul_of_nonneg_left (hb j) (by positivity)
    calc (Q (∑ j, e j • b j) : ℝ) ≤ (∑ j, (e j : ℝ)) ^ 2 * Cc := key Finset.univ
      _ ≤ (D : ℝ) ^ 2 * Cc :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 hsumR 2) hCc
  · intro z hz
    have hz1 : (1 : ℝ) ≤ Q z := by exact_mod_cast hpos z hz
    have hBv : Bf (∑ j, e j • b j) z = ∑ j, (e j : ℤ) * Bf (b j) z := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_nsmul, nsmul_eq_mul]
    have hBvR : (Bf (∑ j, e j • b j) z : ℝ) = ∑ j, (e j : ℝ) * Bf (b j) z := by
      rw [hBv]; push_cast; rfl
    have hMz : (0 : ℝ) ≤ M₀ * Q z := mul_nonneg hM₀ (by linarith)
    have habs : |(Bf (∑ j, e j • b j) z : ℝ)| ≤ (∑ j, (e j : ℝ)) * (M₀ * Q z) := by
      rw [hBvR, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hBb j z) (Nat.cast_nonneg _)
    have h2 : (∑ j, (e j : ℝ)) * (M₀ * Q z) ≤ D * (M₀ * Q z) :=
      mul_le_mul_of_nonneg_right hsumR hMz
    have hlow := neg_abs_le (Bf (∑ j, e j • b j) z : ℝ)
    have hbound : -((D : ℝ) * M₀ * Q z) ≤ (Bf (∑ j, e j • b j) z : ℝ) := by nlinarith
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hM₀) hq
    have hadd : (Q (∑ j, e j • b j + q • z) : ℝ)
        = Q (∑ j, e j • b j) + (q : ℝ) ^ 2 * Q z + q * Bf (∑ j, e j • b j) z := by
      rw [quad_add_eq_add_add_bilin hsym hQ, quad_nsmul' hQ, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    have hfin : (Q (∑ j, e j • b j) : ℝ) < Q (∑ j, e j • b j + q • z) := by
      rw [hadd]
      nlinarith [mul_pos hq0 (mul_pos (show (0 : ℝ) < q - D * M₀ by linarith)
        (show (0 : ℝ) < Q z by linarith)),
        mul_nonneg hq0.le (show (0 : ℝ) ≤ Bf (∑ j, e j • b j) z + D * M₀ * Q z by linarith)]
    exact_mod_cast hfin

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.LeadingMinors


open MvPowerSeries in
theorem _root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det.IsHomogeneous
      (Fintype.card ι) := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) (e i) i)
    (fun _ => 1) fun i _ => MvPolynomial.isHomogeneous_X k _
  simpa using h


open MvPowerSeries in
theorem _root_.GlobalTheory.LeadingMinors.det_X_mem_supported {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) (S : Set σ) (hS : ∀ a i, v a i ∈ S) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det ∈
      MvPolynomial.supported k S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  exact Algebra.subset_adjoin (Set.mem_image_of_mem MvPolynomial.X (hS (e i) i))


open MvPowerSeries in
theorem _root_.GlobalTheory.LeadingMinors.killCompl_det_X {k σ ρ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] {f : ρ → σ} (hf : Function.Injective f) (v : ι → ι → σ) (u : ι → ρ)
    (hd : ∀ a, v a a = f (u a)) (ho : ∀ a i, a ≠ i → v a i ∉ Set.range f) :
    MvPolynomial.killCompl hf
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det =
      MvPolynomial.monomial (∑ a, Finsupp.single (u a) 1) 1 := by
  rw [AlgHom.map_det]
  have hM : (MvPolynomial.killCompl hf).mapMatrix
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) =
      Matrix.diagonal fun a => MvPolynomial.X (u a) := by
    ext a i
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rw [hd, ← MvPolynomial.rename_X f, MvPolynomial.killCompl_rename_app]
    · rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right (ho a i h)]
  rw [hM, Matrix.det_diagonal, MvPolynomial.monomial_sum_one]
  rfl


open MvPowerSeries in
theorem _root_.GlobalTheory.LeadingMinors.coeff_prod_leading_minors : ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → P.coeff al = 1 ∧ P.IsHomogeneous al.degree ∧ al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) ∧ ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → ∃ i, col l.1 i = b := by
  intro k _ T _ _ r n col m hcol P al hP hal
  have hf : Function.Injective
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) :=
    fun a b h => congrArg Prod.fst h
  have hblock : ∀ τ (s : Fin (r τ)), MvPolynomial.killCompl hf
      (Matrix.of fun a i : Fin (s.val + 1) =>
        (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det =
      MvPolynomial.monomial
        (∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1)
        1 := fun τ s =>
    _root_.GlobalTheory.LeadingMinors.killCompl_det_X hf _ (fun a => ⟨τ, Fin.castLE s.isLt a⟩)
      (fun _ => rfl) (by
        rintro a i hai ⟨l, hl⟩
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, h⟩ := hl
        exact hai (Fin.castLE_injective _ (hcol τ h)))
  set B : (Σ τ : T, Fin (r τ)) →₀ ℕ := ∑ τ, ∑ s : Fin (r τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1
    with hBdef
  have hkill : MvPolynomial.killCompl hf P = MvPolynomial.monomial B 1 := by
    rw [hP, hBdef, map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, hblock, MvPolynomial.monomial_pow, one_pow]
  have hmap : Finsupp.mapDomain
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) B = al := by
    rw [hal, hBdef]
    simp [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hdeg : al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) := by
    rw [hal]

    simp [map_sum, Finsupp.degree_single]
  have hhom : P.IsHomogeneous (∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1)) := by
    rw [hP]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => ?_
    have h := (_root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := k)
      (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
        col τ (Fin.castLE s.isLt i)))).pow (m τ s)
    rw [Fintype.card_fin] at h
    rwa [mul_comm] at h
  have hsupp : P ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2} := by
    rw [hP]
    exact Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ =>
      Subalgebra.pow_mem _ (_root_.GlobalTheory.LeadingMinors.det_X_mem_supported
        (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)))
        {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2}
        fun a i => ⟨Fin.castLE s.isLt i, rfl⟩) _
  refine ⟨?_, by rw [hdeg]; exact hhom, hdeg, fun mo hmo l b hlb => ?_⟩
  · rw [← hmap, ← MvPolynomial.coeff_killCompl hf, hkill, MvPolynomial.coeff_monomial, if_pos rfl]
  · have hv : (l, b) ∈ P.vars :=
      (MvPolynomial.mem_vars_iff_mem_support _).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hlb⟩
    exact MvPolynomial.mem_supported.1 hsupp hv

end GlobalTheory.LeadingMinors
end

section

namespace GlobalTheory

open Metric Set Filter Topology

theorem exists_eventually_eq_mul_of_norm_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {O : Set V} (hO : IsOpen O) {P Q : V → ℂ} (hP : DifferentiableOn ℂ P O) (hQ : DifferentiableOn ℂ Q O)
    {x : V} (hx : x ∈ O) (h : ∀ᶠ y in 𝓝 x, ‖P y‖ = ‖Q y‖) :
    ∃ z ∈ O, ∃ c : ℂ, ∀ᶠ y in 𝓝 z, P y = c * Q y := by
  by_cases h0 : ∀ᶠ y in 𝓝 x, Q y = 0
  · refine ⟨x, hx, 0, ?_⟩
    filter_upwards [h, h0] with y hy hy0
    rw [hy0, norm_zero, norm_eq_zero] at hy
    simp [hy]
  · have hfr : ∃ᶠ y in 𝓝 x, Q y ≠ 0 := not_eventually.mp h0
    obtain ⟨z, hz0, hzO, hz⟩ :=
      (hfr.and_eventually (Filter.Eventually.and (hO.mem_nhds hx) h.eventually_nhds)).exists
    have hzO' : z ∈ O := hzO
    have hne : ∀ᶠ y in 𝓝 z, Q y ≠ 0 :=
      (hQ.continuousOn.continuousAt (hO.mem_nhds hzO')).eventually_ne hz0
    have hall : ∀ᶠ y in 𝓝 z, y ∈ O ∧ Q y ≠ 0 ∧ ‖P y‖ = ‖Q y‖ :=
      Filter.Eventually.and (hO.mem_nhds hzO') (hne.and hz)
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hall
    have hsub : ball z ε ⊆ O := fun y hy => (hb y hy).1
    have hd : DifferentiableOn ℂ (fun y => P y / Q y) (ball z ε) := by
      simp only [div_eq_mul_inv]
      exact (hP.mono hsub).mul ((hQ.mono hsub).inv (fun y hy => (hb y hy).2.1))
    have hn : ∀ y ∈ ball z ε, ‖P y / Q y‖ = 1 := by
      intro y hy
      rw [norm_div, (hb y hy).2.2, div_self (norm_ne_zero_iff.mpr (hb y hy).2.1)]
    have hmax : IsMaxOn (norm ∘ fun y => P y / Q y) (ball z ε) z := by
      intro y hy
      show ‖P y / Q y‖ ≤ ‖P z / Q z‖
      rw [hn y hy, hn z (mem_ball_self hε)]
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z ε).isPreconnected
      isOpen_ball hd (mem_ball_self hε) hmax
    refine ⟨z, hzO', P z / Q z, ?_⟩
    filter_upwards [ball_mem_nhds z hε] with y hy
    have e : P y / Q y = P z / Q z := hc hy
    rw [← e, div_mul_cancel₀ _ (hb y hy).2.1]

theorem exists_eq_const_mul_of_forall_exists_norm_eq :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι]
      (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ),
      DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) →
      ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  intro V _ _ _ ι _ O hO hc hne P Q hP hQ h
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : BaireSpace O := hO.baireSpace
  haveI : Nonempty O := hne.to_subtype
  have hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖} := fun i =>
    isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)
  have hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := h x x.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖ := mem_interior_iff_mem_nhds.mp hx
  have hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖ := by
    rw [← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact hx1
  obtain ⟨z, hz, c, hzc⟩ := exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2
  refine ⟨i, c, fun y hy => ?_⟩
  have hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O := hP.sub ((hQ i).const_mul c)
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz
    (by filter_upwards [hzc] with y hy; simp [hy]) y hy
  exact sub_eq_zero.mp this

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem exists_algHom_ker_eq_of_isMaximal (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb
  refine ⟨(e.symm : (B ⧸ m) →ₐ[F] F).comp (Ideal.Quotient.mkₐ F m), fun b h => ?_⟩
  have h' : e.symm (Ideal.Quotient.mk m b) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

theorem tensor_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by
  intro O F _ _ _ _ hinj A _ _ _ _ _ M _ _ _ t ht
  classical
  haveI : IsArtinianRing (TensorProduct O F A) := IsArtinianRing.of_finite F _
  have hpt : ∀ m : MaximalSpectrum (TensorProduct O F A),
      ∃ ψ : TensorProduct O F A →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m.asIdeal := fun m =>
    haveI := m.isMaximal
    exists_algHom_ker_eq_of_isMaximal F _ m.asIdeal
  choose ψ hψ using hpt
  let φ : MaximalSpectrum (TensorProduct O F A) → (A →ₐ[O] F) := fun m =>
    ((ψ m).restrictScalars O).comp Algebra.TensorProduct.includeRight
  let L : A →ₗ[O] (MaximalSpectrum (TensorProduct O F A) → F) :=
    LinearMap.pi fun m => (φ m).toLinearMap
  have hR : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O F A) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    apply hR
    rw [map_zero]
    have hmem : (Algebra.TensorProduct.includeRight a : TensorProduct O F A) ∈
        Ideal.jacobson (⊥ : Ideal (TensorProduct O F A)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hψ ⟨J, hJ⟩ _ (congrFun ha ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := TensorProduct O F A)
    have h2 := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsNilpotent.eq_zero ⟨n, by simpa using h2⟩
  have hLM : Function.Injective (L.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  haveI : Fintype (MaximalSpectrum (TensorProduct O F A)) := Fintype.ofFinite _
  apply hLM
  rw [map_zero]
  apply (TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)).injective
  rw [map_zero]
  funext m
  have key : ∀ s : TensorProduct O A M,
      TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)
        (L.rTensor M s) m
      = TensorProduct.map (φ m).toLinearMap (LinearMap.id : M →ₗ[O] M) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [L, TensorProduct.piLeft]
    | add s s' h h' => rw [map_add (f := _), map_add (f := _), Pi.add_apply, h, h', map_add (f := _)]
  rw [key, ht]
  rfl

end GlobalTheory
end
