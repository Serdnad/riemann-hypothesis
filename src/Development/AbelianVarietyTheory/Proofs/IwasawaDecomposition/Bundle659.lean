module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle647
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PolyBd

section Gen

variable {P : Type} {A : P → ℝ}

def PB (A : P → ℝ) (f : P → ℂ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k

theorem PB.const (a : ℂ) : PB A fun _ => a := ⟨‖a‖, 0, norm_nonneg _, fun _ => by simp⟩

theorem PB.of_le {f : P → ℂ} (h : ∀ p, ‖f p‖ ≤ A p) : PB A f := ⟨1, 1, zero_le_one, fun p => by simpa using h p⟩

theorem PB.mul {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p * g p := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨C * D, k + n, mul_nonneg hC hD, fun p => ?_⟩
  rw [norm_mul, pow_add]
  calc _ ≤ (C * A p ^ k) * (D * A p ^ n) :=
        mul_le_mul (h p) (h' p) (norm_nonneg _) ((norm_nonneg _).trans (h p))
    _ = _ := by ring

theorem PB.both (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k ∧ ‖g p‖ ≤ C * A p ^ k := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨max C D, max k n, le_max_of_le_left hC, fun p => ⟨(h p).trans ?_, (h' p).trans ?_⟩⟩
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (hA p) (le_max_left _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (hA p) (le_max_right _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)

theorem PB.add (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p + g p := by
  obtain ⟨C, k, hC, h⟩ := hf.both hA hg
  refine ⟨2 * C, k, by positivity, fun p => (norm_add_le _ _).trans ?_⟩
  linarith [(h p).1, (h p).2]

theorem PB.sum (hA : ∀ p, 1 ≤ A p) {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (hf a).add hA ih

theorem PB.prod {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∏ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 1
  | insert a s ha ih => simpa [Finset.prod_insert ha] using (hf a).mul ih

theorem PB.det (hA : ∀ p, 1 ≤ A p) {I : Type} [Fintype I] [DecidableEq I] {M : P → Matrix I I ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) : PB A fun p => (M p).det := by
  simp only [Matrix.det_apply']
  exact PB.sum hA _ fun s => (PB.const _).mul (PB.prod _ fun i => hM _ _)

theorem PB.matMul (hA : ∀ p, 1 ≤ A p) {a b d : Type} [Fintype b] {M : P → Matrix a b ℂ} {N : P → Matrix b d ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) (hN : ∀ i j, PB A fun p => N p i j) (i : a) (j : d) :
    PB A fun p => (M p * N p) i j := by
  simp only [Matrix.mul_apply]
  exact PB.sum hA _ fun k => (hM _ _).mul (hN _ _)

theorem horVal_bound (hA : ∀ p, 1 ≤ A p) {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : P → Matrix (m ⊕ n) m ℂ} {C : P → Matrix n (m ⊕ n) ℂ} {R : P → Matrix m (m ⊕ n) ℂ}
    {S : P → Matrix (m ⊕ n) n ℂ} (h : ∀ p, C p * K p = 0) (hR : ∀ p, R p * K p = 1) (hS : ∀ p, C p * S p = 1)
    (bK : ∀ i j, PB A fun p => K p i j) (bC : ∀ i j, PB A fun p => C p i j) (bR : ∀ i j, PB A fun p => R p i j)
    (bS : ∀ i j, PB A fun p => S p i j) :
    ∃ (D : ℝ) (k : ℕ), 0 ≤ D ∧ ∀ p, ‖horVal (K p) (C p)‖ ≤ D * A p ^ k ∧ ‖(horVal (K p) (C p))⁻¹‖ ≤ D * A p ^ k := by
  have h1 : PB A fun p => horVal (K p) (C p) := by
    simp only [fun p => horVal_eq (h p) (hR p) (hS p)]
    refine PB.det hA fun i j => ?_
    rcases i with i | i
    · simpa using bR i j
    · simpa using bC i j
  have h2 : PB A fun p => (horVal (K p) (C p))⁻¹ := by
    simp only [fun p => inv_eq_of_mul_eq_one_right (horVal_mul (h p) (hR p) (hS p))]
    refine PB.det hA fun i j => ?_
    rcases j with j | j
    · simpa using bK i j
    · simpa using bS i j
  exact h1.both hA h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Di : Datum H}

theorem exists_comb {J : Type} [Fintype J] (x : J → Di.La) (f : (E →+* ℂ) → (E →+* ℂ)) (v : Di.La)
    (hv : ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) :
    ∃ B : (E →+* ℂ) → J → ℂ, ∀ Q : Di.La →+ (Letter Dw → ℂ),
      (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = f z.1 (a : E) * Q v z) →
      ∀ z : Letter Dw, Q v z = ∑ k, B z.1 k * Q (x k) z := by
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨fun t k => (n : ℂ)⁻¹ * f t (a k : E), fun Q hQ z => ?_⟩
  have h := congrArg (fun w => Q w z) ha

  simp only [map_sum, Finset.sum_apply, hQ, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [_root_.mul_assoc]
  rw [← Finset.mul_sum, h, inv_mul_cancel_left₀ hn']

theorem perVal_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La)
    (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ)
    (hx : IsPerBasis Di x hm) : ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ))
      (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ),
      GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) →
      (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) →
      (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  let P : Type := {p : (Di.La →+ (Letter Dw → ℂ)) × Matrix (Letter Dw) (Fin g) ℂ × Matrix (Fin g) (Letter Dw) ℂ ×
      (Fin r → Fin g → ℂ) × ℝ // GoodPer c σ τ x hm p.1 ∧ p.2.1 * p.2.2.1 = 1 ∧
      (∀ v, ∑ z, p.1 v z • p.2.1 z = ∑ m, T₀ v m • p.2.2.2.1 m) ∧
      (∀ j, ∑ m, ρ j m • p.2.2.2.1 m = Pi.single j 1) ∧ 1 ≤ p.2.2.2.2 ∧ (∀ z j, ‖p.2.1 z j‖ ≤ p.2.2.2.2) ∧
      (∀ j z, ‖p.2.2.1 j z‖ ≤ p.2.2.2.2) ∧ (∀ m j, ‖p.2.2.2.1 m j‖ ≤ p.2.2.2.2)}
  let A : P → ℝ := fun p => p.1.2.2.2.2
  have hA : ∀ p, 1 ≤ A p := fun p => p.2.2.2.2.2.1
  choose B hB using fun m : Fin r =>
    exists_comb (Dw := Dw) x (Formalism.L2.PjFree.relab c σ) (T₀.symm (Pi.single m 1)) (hx.2.1 _)
  have hQ : ∀ (p : P) v z, p.1.1 v z = ∑ j, (∑ m, (T₀ v m : ℂ) * p.1.2.2.2.1 m j) * p.1.2.2.1 j z := by
    rintro ⟨⟨Q, W, Wi, lam, a⟩, -, h1, h2, -⟩ v z
    dsimp only at h1 h2 ⊢
    have h3 : ∀ j, ∑ m, (T₀ v m : ℂ) * lam m j = (Q v ᵥ* W) j := fun j => by
      have := congrFun (h2 v) j
      simp only [Finset.sum_apply, Pi.smul_apply] at this
      simp only [smul_eq_mul, zsmul_eq_mul] at this
      rw [← this]; rfl
    simp only [h3]
    have : Q v = (Q v ᵥ* W) ᵥ* Wi := by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    exact congrFun this z
  have bQ : ∀ v z, PB A fun p => p.1.1 v z := fun v z => by
    simp only [hQ]
    exact PB.sum hA _ fun j => (PB.sum hA _ fun m => (PB.const _).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.2 m j)).mul
      (PB.of_le fun p => p.2.2.2.2.2.2.2.1 j z)
  let S : ∀ t : E →+* ℂ, P → Matrix (Idx Dw τ) (Fin (Dw.mult t)) ℂ := fun t p =>
    Matrix.of fun k i => ∑ j, p.1.2.1 ⟨t, i⟩ j * ∑ m, ρ j m * B m t k
  have bS : ∀ t k i, PB A fun p => S t p k i := fun t k i => by
    simp only [S, Matrix.of_apply]
    exact PB.sum hA _ fun j => (PB.of_le fun p => p.2.2.2.2.2.2.1 _ j).mul (PB.const _)
  have hS : ∀ t (p : P), perMat x p.1.1 t * S t p = 1 := by
    intro t p
    have h4 : ∀ j z, ∑ m, ρ j m * p.1.1 (T₀.symm (Pi.single m 1)) z = p.1.2.2.1 j z := by
      intro j z
      have h5 : ∀ j', ∑ m, ρ j m * p.1.2.2.2.1 m j' = (Pi.single j (1 : ℂ) : Fin g → ℂ) j' := fun j' => by
        simpa [Finset.sum_apply] using congrFun (p.2.2.2.2.1 j) j'
      simp only [hQ, AddEquiv.apply_symm_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← _root_.mul_assoc, ← Finset.sum_mul, h5, Pi.single_apply, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ext i i'
    have h6 := congrFun (congrFun p.2.2.1 ⟨t, i'⟩) ⟨t, i⟩
    have h7 : (1 : Matrix (Letter Dw) (Letter Dw) ℂ) ⟨t, i'⟩ ⟨t, i⟩ =
        (1 : Matrix (Fin (Dw.mult t)) (Fin (Dw.mult t)) ℂ) i i' := by
      simp [Matrix.one_apply, eq_comm]
    rw [← h7, ← h6]
    simp only [Matrix.mul_apply, ← h4, hB _ _ p.2.1.1, perMat, S, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdet : IsUnit ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ).det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hx.2.2.2).isUnit
  obtain ⟨D, k, -, h⟩ := horVal_bound hA (K := fun p => kerMat c σ τ x hm p.1.1) (C := fun p => perMat x p.1.1 τ)
    (R := fun p => (S (conjEmb τ) p)ᵀ * (hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ) (S := S τ)
    (fun p => p.2.1.2.1)
    (fun p => by
      rw [kerMat, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.transpose_mul, hS,
        Matrix.transpose_one])
    (hS τ) (PB.matMul hA (fun _ _ => PB.const _) fun i j => bQ _ _) (fun i j => bQ _ _)
    (PB.matMul hA (fun i j => bS _ _ _) fun _ _ => PB.const _) (bS τ)
  exact ⟨D, k, fun Q W Wi lam a h1 h2 _ h3 h4 h5 h6 h7 h8 =>
    h ⟨⟨Q, W, Wi, lam, a⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

end GlobalTheory.ShFam.Hor.PolyBd
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isDerivAt0_of_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {g m : ℕ}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (e0 : e 0 = (1 : Over.mk x ⟶ t.G).left)
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : Fin m → Fin g → ℂ} (ht : ∀ i, IsTanAtG t x (v i))
    (hv : ∀ i, IsDerivAt0 e (w i) (v i)) {a : Fin m → ℂ} {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v')
    (hc : IsCombAtG t x v a v') : IsDerivAt0 e (∑ i, a i • w i) v' := by
  refine ⟨ht'.2.trans e0.symm, fun U h f => ?_⟩
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  refine key.trans ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg (a i * ·) ((hv i).2 U (hU i) f)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem frame_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := ℂ) (ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}
    (hx : IsUnivChart _ n xc) (cc : Letter Dw → Fin n → ℂ) (hcc : ∀ z, f.v z.1 z.2 = vec Z.t x xc (cc z)) :
    LinearIndependent ℂ cc ∧ ⊤ ≤ Submodule.span ℂ (Set.range cc) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨p, hp, hps⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hE : ∀ τ m, IsEigV (rho hx) (embK c τ) m ↔ ∀ a : 𝓞 E, vec Z.t x xc m ≫ (Z.t.act.act a).left =
      spMap (epsMul (σ (embK c τ a))) ≫ vec Z.t x xc m := fun τ m => by
    rw [vec_eig_iff hx (fun a => σ (embK c τ a)), ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    rfl
  have hv : ∀ τ, f.v τ = fun i => vec Z.t x xc (cc ⟨τ, i⟩) := fun τ => funext fun i => hcc ⟨τ, i⟩
  have hb : ∀ τ m, IsEigV (rho hx) (embK c τ) m → ∃! a : Fin (Dw.mult τ) → ℂ, m = ∑ i, a i • cc ⟨τ, i⟩ :=
    fun τ m hm => by
      have := f.basis τ _ (vec_tan hx m) ((hE τ m).1 hm)
      rw [hv] at this
      simpa only [LieLocBasis.comb_iff hx] using this
  have he : ∀ τ (a : Fin (Dw.mult τ) → ℂ), IsEigV (rho hx) (embK c τ) (∑ i, a i • cc ⟨τ, i⟩) := fun τ a r => by
    have h1 : ∀ i, IsEigV (rho hx) (embK c τ) (cc ⟨τ, i⟩) := fun i => (hE _ _).2 (hcc ⟨τ, i⟩ ▸ f.eig τ i)

    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, h1 i r, smul_comm]
  refine ⟨Fintype.linearIndependent_iff.2 fun a ha z => ?_, fun m _ => ?_⟩
  · rw [Fintype.sum_sigma] at ha
    have h1 := proj_sum_eig (rho hx) (embK c) α hinj _ (fun τ => he τ fun i => a ⟨τ, i⟩) z.1
    rw [ha, map_zero] at h1
    exact congrFun ((hb z.1 0 fun r => by simp).unique h1 (y₂ := 0) (by simp)) z.2
  · have h1 := LinearMap.congr_fun (sum_proj (rho hx) (embK c) α hinj) m
    rw [LinearMap.sum_apply, Module.End.one_apply] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := hb τ _ (eig_of_alpha _ _ α hN τ (proj_eig_alpha (rho hx) _ α hinj p hp hps τ m))
    rw [ha]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dirs_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)}
    (e0 : e 0 = (1 : Over.mk x ⟶ Z.t.G).left) (h1 : ∀ w, ∃! v, IsTanAtG Z.t x v ∧ IsDerivAt0 e w v)
    (h2 : ∀ v, IsTanAtG Z.t x v → ∃! w, IsDerivAt0 e w v) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, IsDerivAt0 e (W z) (f.v z.1 z.2)) : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W := by
  classical
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose cc hcc using fun z : Letter Dw => vec_exists hx _ (f.tan z.1 z.2)
  obtain ⟨hli, hsp⟩ := frame_basis f hx cc hcc
  choose u hu using fun j : Fin n => (h2 _ (vec_tan hx (Pi.single j 1))).exists
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ u
  have hT : ∀ m, IsDerivAt0 e (T m) (vec Z.t x xc m) := fun m =>
    isDerivAt0_of_comb e0 (fun j => vec_tan hx _) hu (vec_tan hx m) ((LieLocBasis.comb_iff hx _ m m).2 (by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]))
  have hbij : Function.Bijective T := by
    refine ⟨fun m m' h => vec_inj hx ((h1 (T m)).unique ⟨vec_tan hx m, hT m⟩ ⟨vec_tan hx m', h ▸ hT m'⟩), fun w => ?_⟩
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h1 w
    obtain ⟨m, rfl⟩ := vec_exists hx v hv
    exact ⟨m, (h2 _ hv).unique (hT m) hd⟩
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective T hbij), funext fun z => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact (h2 _ (f.tan z.1 z.2)).unique (hcc z ▸ hT (cc z)) (hW z)

theorem differentiableAt_dir {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (he : IsExpChart e ex) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {B : Set V} (hB : IsOpen B) {x : V → CxPts (genStr Z) σ}
    (hx : IsHolTo B fun b => (x b).1) (hs : ∀ b ∈ B, x b ∈ e.source) {v : V → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)}
    (hv : HolTan B v) {W : V → Fin g → ℂ} (hW : ∀ b ∈ B, IsDerivAt0 (fun w => (ex (x b) w).left) (W b) (v b))
    {b₀ : V} (hb₀ : b₀ ∈ B) : DifferentiableAt ℂ W b₀ := by
  obtain ⟨-, h1, -, h3, h4, h5⟩ := he
  let ε : CxPts (genStr Z) σ → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun y w => (ex y w).left
  have hz : DifferentiableAt ℂ (fun b => e (x b)) b₀ :=
    differentiableAt_pi.2 fun k => (h1 k V B x hB hx hs).differentiableAt (hB.mem_nhds hb₀)
  have ht := e.map_source (hs b₀ hb₀)
  have hl : ∀ b ∈ B, ε (e.symm (e (x b))) = ε (x b) := fun b hb => by rw [e.left_inv (hs b hb)]
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (U : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, U)), ⊤ ≤ ε (x b₀) 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (ε (x b₀) z) U f) 0 w = 0 := by
    intro U f hU
    have hU' : ⊤ ≤ ε (e.symm (e (x b₀))) 0 ⁻¹ᵁ U := by rwa [hl b₀ hb₀]
    have d := (HolLieFrame.differentiableAt_fderiv (e := fun z => ε (e.symm z)) h4 ht U f hU').comp b₀ hz
    have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ v b ⁻¹ᵁ U := by
      have hc : ContinuousAt (fun b => (e (x b), (0 : Fin g → ℂ))) b₀ := hz.continuousAt.prodMk continuousAt_const
      filter_upwards [hB.mem_nhds hb₀, hc.preimage_mem_nhds ((h4 U f).1.mem_nhds ⟨⟨ht, trivial⟩, hU'⟩)] with b hb hb'
      have h' : ⊤ ≤ ε (e.symm (e (x b))) 0 ⁻¹ᵁ U := hb'.2
      rw [hl b hb] at h'
      exact ⟨hb, (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(hW b hb).1]; exact h')⟩
    refine hw (fun b => fderiv ℂ (fun z => valAt' (ε (x b) z) U f) 0) (d.congr_of_eventuallyEq ?_)
      (((hv U f).differentiableAt hn).congr_of_eventuallyEq ?_)
    · filter_upwards [hB.mem_nhds hb₀] with b hb
      simp only [Function.comp_apply, hl b hb]
    · filter_upwards [hn] with b ⟨hb, h⟩
      refine ((hW b hb).2 U h f).symm.trans ?_
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dite_eq_left h]
  have d₁ := LocalLift.isDerivAt0_const (ε (x b₀)) w hw'
  have d₀ := LocalLift.isDerivAt0_const (ε (x b₀)) 0 fun _ _ _ => map_zero _
  have e0 : ex (x b₀) 0 = 1 := by simpa using h3 _ (hs b₀ hb₀) 0 0
  exact ((h5 _ (hs b₀ hb₀)).2 _ ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (ex (x b₀) 0))),
    d₁.1.trans (congrArg (·.left) e0)⟩).unique d₁ d₀

theorem exists_inverse {J : Type} [Fintype J] [DecidableEq J] {g : ℕ} (b : Module.Basis J ℂ (Fin g → ℂ)) :
    ∃ Wi : Matrix (Fin g) J ℂ, Matrix.of b * Wi = 1 ∧ Wi * Matrix.of b = 1 := by
  refine ⟨Matrix.of fun j z => b.repr (Pi.single j 1) z, ?_, ?_⟩
  · ext z z'
    have h : b z = ∑ j, b z j • (Pi.single j 1 : Fin g → ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun w => b.repr w z') h

    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_apply, Matrix.one_apply, h2]
    rfl
  · ext j k
    have h := congrFun (b.sum_repr (Pi.single j 1)) k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finset.sum_apply, Pi.single_apply, eq_comm] using h

theorem exists_dirs_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex he V _ _ _ B a hB ha hs
  have h5 := fun b hb => he.2.2.2.2.2 _ (hs b hb)
  choose! W hW using fun b hb (z : Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hbas : ∀ b ∈ B, ∃ bs : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑bs = W b := fun b hb => by
    have e0 : ex (a b).1 0 = 1 := by simpa using he.2.2.2.1 _ (hs b hb) 0 0
    exact dirs_basis (a b).2 (e := fun w => (ex (a b).1 w).left) (congrArg (·.left) e0) (h5 b hb).1 (h5 b hb).2 (hW b hb)
  have hinv : ∀ b ∈ B, ∃ Wi : Matrix (Fin g) (Letter Dw) ℂ, Matrix.of (W b) * Wi = 1 ∧ Wi * Matrix.of (W b) = 1 :=
    fun b hb => by
      obtain ⟨bs, h⟩ := hbas b hb
      rw [← h]
      exact exists_inverse bs
  choose! Wi hWi using hinv
  have hd : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => W b z) b := fun b hb z =>
    differentiableAt_dir he hB ha.1 hs (ha.2 z.1 z.2) (fun b hb => hW b hb z) hb
  refine ⟨fun b => Matrix.of (W b), Wi, fun b hb => ContinuousAt.continuousWithinAt ?_,
    fun b hb => ContinuousAt.continuousWithinAt ?_, fun b hb => ⟨hW b hb, hWi b hb⟩⟩
  · exact continuousAt_pi.2 fun z => (hd b hb z).continuousAt
  · obtain ⟨bs, -⟩ := hbas b hb
    let q : Fin g ≃ Letter Dw := (Pi.basisFun ℂ (Fin g)).indexEquiv bs
    refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun z => ?_
    have := HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (Wi b).submatrix id q)
      (fun b => (Matrix.of (W b)).submatrix q id) b (fun i k => differentiableAt_pi.1 (hd b hb (q i)) k) (by
        filter_upwards [hB.mem_nhds hb] with b' hb'
        rw [Matrix.submatrix_mul_equiv, (hWi b' hb').2]
        rfl) j (q.symm z)
    simpa using this.continuousAt

end GlobalTheory.ShFam.Hor.ExpDirs
end
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.column_params_instance_data : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  first | exact @GlobalTheory.Mem.R3.twArgs_exists | exact GlobalTheory.Mem.R3.twArgs_exists | (intros; apply GlobalTheory.Mem.R3.twArgs_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.Top.Closing

theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  refine GlobalTheory.Mem.Top.Bl.StepW.trans h (GlobalTheory.Mem.Top.Bl.StepW.of_all ?_)
  intro K B f T w _ _ hw Z l
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hw Z
    { g := l.g, coh := l.coh, Wt := l.Wt, p0 := l.p0, what₂ := l.what₂, rx := l.rx, nch := l.nch, n := l.n, xd := l.xd,
      chiT := l.chiT, nx := l.nx, col := l.col, real := l.real, dsig_eq := l.dsig_eq, del := l.del, sx := l.sx }
  refine ⟨Y, hY1, hY2, hY3, fun O t e1 e2 e3 => ?_⟩
  obtain ⟨o⟩ := hY4 O t e1 e2 e3
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem io_zero (𝒮 : Slots) (h : 𝒮.Rx = RX) : ∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0),
    𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0 := by
  intro K B f T w Z Wt p0 t r μ hμ j _
  rw [h] at r
  exact (RXs.io r μ j hμ).1

end GlobalTheory.Mem.Top.Closing
end
