module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsOfGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle015
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle600
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.weil_pairing_cocycle_uniqueness : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  first | (exact @GlobalTheory.TateGlue.exists_gTateIso) | (exact GlobalTheory.TateGlue.exists_gTateIso) | (intros; apply GlobalTheory.TateGlue.exists_gTateIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

theorem _root_.GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  first | exact @GlobalTheory.exists_holUnif_of_isExp | exact GlobalTheory.exists_holUnif_of_isExp | (intros; apply GlobalTheory.exists_holUnif_of_isExp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.comp_linearEquiv_intertwining : ∀ (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ) (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsPeriod D ρ P → (∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) → IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  first | exact @GlobalTheory.PELU.IsPeriod.comp_linearEquiv | exact GlobalTheory.PELU.IsPeriod.comp_linearEquiv | (intros; apply GlobalTheory.PELU.IsPeriod.comp_linearEquiv <;> assumption)
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

theorem _root_.GlobalTheory.T.isPeriodMap_comp_injective_realLinear : ∀ {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → Function.Injective R → (∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) → M.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) → (∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) → IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  first | exact @GlobalTheory.PELU.isPeriod_comp_realLinear | exact GlobalTheory.PELU.isPeriod_comp_realLinear | (intros; apply GlobalTheory.PELU.isPeriod_comp_realLinear <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.gram_re_posDef_adjoint_period : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P → ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧ ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  first | exact @GlobalTheory.PELU.gram_re_posdef_adj | exact GlobalTheory.PELU.gram_re_posdef_adj | (intros; apply GlobalTheory.PELU.gram_re_posdef_adj <;> assumption)
end

section

open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj imForm imForm_apply herm_add_left herm_add_right
  herm_smul_left herm_smul_right herm_conj riemann_symm eq_zero_of_imForm det_ne_zero_of_pos colMat colMat_apply
  exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

def Tsp {O : Type} [Ring O] (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) :
    Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) where
  carrier := {S | Sᵀ = S ∧ ∀ a, S * (ρ (bar a)).map star = (ρ a)ᴴ * S}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := by
    rintro S T ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [transpose_add, h1, h3], fun a => by rw [Matrix.add_mul, Matrix.mul_add, h2, h4]⟩
  smul_mem' := by
    rintro c S ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], fun a => by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩

theorem star_mulVec_map (M : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : star (M *ᵥ z) = M.map star *ᵥ star z := by
  funext i; simp [mulVec, dotProduct]

theorem herm_mulVec_left (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (A *ᵥ z) w = hermForm (Aᵀ * M) z w := by
  unfold hermForm
  rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem herm_mulVec_right (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M z (A *ᵥ w) = hermForm (M * A.map star) z w := by
  unfold hermForm
  rw [star_mulVec_map, mulVec_mulVec]

theorem herm_single (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (i j : Fin g) :
    hermForm M (Pi.single i c) (Pi.single j 1) = c * M i j := by
  simp [hermForm, ← Pi.single_star, mulVec_single]

theorem sesq_ext {N N' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z w, (hermForm N z w).im = (hermForm N' z w).im) : N = N' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 := h (Pi.single i Complex.I) (Pi.single j 1)
  simp only [herm_single] at h1 h2
  simp at h1 h2
  apply Complex.ext <;> linarith

variable {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

theorem ext_per {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_per hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc

  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
  LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

theorem exists_colMat_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ρ P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation_per hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by

    simp only [map_sub, map_sum, map_add (f := _), map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])

  simp only [map_sub, map_sum, map_add (f := _), map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add (f := _), map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem comm_realMap_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : O) :
    ρ a * A = A * ρ a ∧ ρ a * B = B * (ρ a).map star := by
  refine realMap_inj (ext_per hP₀ fun x => ?_)
  have := h (a • x)
  rw [hP.1, hP₀.1, h] at this
  simp only [realMap_apply, mulVec_add, mulVec_mulVec, star_mulVec_map] at this ⊢
  exact this

theorem comm_herm_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : O) :
    (ρ a)ᵀ * M = M * (ρ (bar a)).map star := by
  have key : (imForm M).compl₁₂ (realMap (ρ a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (ρ (bar a)) 0) := by
    refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← hP₀.1, imForm_apply, hM, D.adj]
  refine sesq_ext fun z w => ?_
  have := LinearMap.congr_fun₂ key z w
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply] at this
  rw [← herm_mulVec_left, ← herm_mulVec_right]
  exact this

theorem map_star_transpose (M : Matrix (Fin g) (Fin g) ℂ) : (M.map star)ᵀ = Mᴴ := rfl

theorem mem_Tsp_of_period {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) :
    (A⁻¹ * B)ᵀ * M₀ ∈ Tsp bar ρ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    ext i j
    rw [transpose_apply]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) j i
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [GlobalTheory.PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · obtain ⟨h1, h2⟩ := comm_realMap_per hP₀ hP h a
    have h3 : ρ a * (A⁻¹ * B) = A⁻¹ * B * (ρ a).map star := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (ρ a * A) * A⁻¹ = A⁻¹ * (A * ρ a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, h3, transpose_mul,
      map_star_transpose, Matrix.mul_assoc]

theorem comm_of_mem_Tsp {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M₀ : Matrix (Fin g) (Fin g) ℂ}
    (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y) (hdet : M₀.det ≠ 0) {C : Matrix (Fin g) (Fin g) ℂ}
    (hC : Cᵀ * M₀ ∈ Tsp bar ρ) (a : O) : ρ a * C = C * (ρ a).map star := by
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have h := hC.2 a
  rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, ← map_star_transpose,
    ← Matrix.mul_assoc, ← transpose_mul] at h
  have := congrArg (· * M₀⁻¹) h
  simp only [mul_nonsing_inv_cancel_right _ _ hu] at this
  exact transpose_injective this

theorem realMap_one_injective {C : Matrix (Fin g) (Fin g) ℂ} (h : (1 - C * C.map star).det ≠ 0) :
    Function.Injective (realMap 1 C) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  rw [realMap_apply, one_mulVec] at hz
  have h1 : z = -(C *ᵥ star z) := eq_neg_of_add_eq_zero_left hz
  have h2 : star z = -(C.map star *ᵥ z) := by
    have := congrArg star hz
    rw [star_add, star_mulVec_map, star_star, star_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  refine eq_zero_of_mulVec_eq_zero h ?_
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← neg_neg (C.map star *ᵥ z), ← h2, mulVec_neg, ← h1, sub_self]

end

end GlobalTheory.PerCoordU
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isogeny_degree_of_fibre_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  first | (exact @GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (exact GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (intros; apply GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HTTorsCount

theorem absNorm_pos_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (𝔟 : Ideal (𝓞 K)) (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) :
    0 < Ideal.absNorm 𝔟 ∧ (Ideal.absNorm 𝔟).Coprime p := by
  obtain ⟨β, hβ, z, hz, hsum⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hpos : 0 < Ideal.absNorm 𝔟 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [Submodule.mem_bot] at hβ
    subst hβ
    rw [zero_add, _root_.mul_comm] at hsum
    have hu : IsUnit (p : 𝓞 K) := isUnit_iff_exists_inv.2 ⟨y, hsum⟩
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [e, Algebra.norm_algebraMap, Int.isUnit_iff_natAbs_eq, Int.natAbs_pow, Int.natAbs_natCast] at hn
    rcases Nat.pow_eq_one.1 hn with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h1
  refine ⟨hpos, ?_⟩
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd => ?_))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hpos
  have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hpos.ne'
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
  have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h1 : Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟) = 1 := by
    have := congrArg (Ideal.Quotient.mk 𝔟) hsum
    rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟)) * x := by rw [h1, _root_.one_mul]
      _ = 0 := by rw [_root_.mul_assoc, hpx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

theorem card_killedBy_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  intro p _ D R _ b N S s o 𝔟 h𝔟 k _ _ t
  obtain ⟨hcpos, hcop⟩ := absNorm_pos_coprime p 𝔟 h𝔟
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, spMap β = t ≫ s := ⟨(Spec.preimage (t ≫ s)).hom, Spec.map_preimage _⟩
  obtain ⟨I, -⟩ := o.geom k t β hβ.symm
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (a : 𝓞 D.F) (x : D.La), a • x = (algebraMap (𝓞 D.F) D.O a) • x := fun _ _ => rfl
  have hcnt := GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow D.F D.La D.freeLa D.finLa (D.m * D.n) D.rankLa 𝔟 (Ideal.absNorm 𝔟) hcpos
    (Ideal.absNorm_mem 𝔟)
  rw [← hcnt]
  set c := Ideal.absNorm 𝔟 with hc
  set P : Submodule (𝓞 D.F) D.La := Ideal.span {(c : 𝓞 D.F)} • (⊤ : Submodule (𝓞 D.F) D.La) with hP
  have hmemP : ∀ x, x ∈ P ↔ ∃ y, x = c • y := by
    intro x
    rw [hP, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Submodule.mem_top, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
  let g : D.La → (Over.mk t ⟶ o.A) := I.ev c
  have hker : ∀ x, g x = 1 ↔ x ∈ P := fun x => by rw [hmemP]; exact I.ker c hcpos hcop x
  have hsub : ∀ x y, g (x - y) = g x * (g y)⁻¹ := fun x y =>
    eq_mul_inv_of_mul_eq (by rw [← I.add, sub_add_cancel])
  have hlin : ∀ (a : 𝓞 D.F) x, g (a • x) = g x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := fun a x => by
    rw [hsmul]; exact I.lin c _ x
  have hmap : 𝔟.map (algebraMap (𝓞 D.F) D.O) = Ideal.span (algebraMap (𝓞 D.F) D.O '' 𝔟) := rfl
  let f : D.La ⧸ P → (Over.mk t ⟶ o.A) := fun z => Quotient.liftOn' z g (fun x y hxy => by
    have h1 : g (x - y) = 1 := (hker _).2 ((Submodule.quotientRel_def P).1 hxy)
    rw [hsub] at h1
    exact mul_inv_eq_one.1 h1)
  have hf : ∀ x, f (Submodule.Quotient.mk x) = g x := fun _ => rfl
  have hkill : ∀ x, (∀ a ∈ 𝔟, a • (Submodule.Quotient.mk x : D.La ⧸ P) = 0) ↔
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) (g x) := by
    intro x
    rw [hmap, GlobalTheory.IwLevel.killedBy_span]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      rw [GlobalTheory.IwLevel.htAct_act, ← hlin, hker, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact h a ha
    · intro h a ha
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hker, hlin]
      have := h _ ⟨a, ha, rfl⟩
      rwa [GlobalTheory.IwLevel.htAct_act] at this
  have hpow : ∀ (q : Over.mk t ⟶ o.A) (n : ℕ), q ≫ o.act.act (n : D.O) = q ^ n := by
    intro q n
    have h0 : o.act.act 0 = 1 := by
      have := o.act.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]
  let F : {z : D.La ⧸ P // ∀ a ∈ 𝔟, a • z = 0} →
      {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} :=
    fun z => ⟨f z.1, by
      obtain ⟨z, hz⟩ := z
      induction z using Submodule.Quotient.induction_on with
      | H x => exact (hkill x).1 hz⟩
  refine (Nat.card_eq_of_bijective F ⟨?_, ?_⟩).symm
  · rintro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ h
    have h' : f z₁ = f z₂ := congrArg Subtype.val h
    induction z₁ using Submodule.Quotient.induction_on with
    | H x =>
    induction z₂ using Submodule.Quotient.induction_on with
    | H y =>
    rw [hf, hf] at h'
    apply Subtype.ext
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, ← hker, hsub, h', mul_inv_cancel]
  · rintro ⟨q, hq⟩
    have hq1 : q ^ c = 1 := by
      rw [← hpow, ← map_natCast (algebraMap (𝓞 D.F) D.O)]
      have := hq _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Ideal.absNorm_mem 𝔟))
      rwa [GlobalTheory.IwLevel.htAct_act] at this
    obtain ⟨x, hx⟩ := (I.onto c hcpos hcop q).1 hq1
    refine ⟨⟨Submodule.Quotient.mk x, (hkill x).2 (by change GlobalTheory.IwLevel.KilledBy _ _ (I.ev c x); rw [hx]; exact hq)⟩, Subtype.ext ?_⟩
    exact hx

end GlobalTheory.HTTorsCount
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def fracMap (ρ : R →+* R') (hρ : Function.Injective ρ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (A := R) (B := R') (K := FractionRing R) (L := FractionRing R') (j := ρ) hρ

theorem fracMap_algebraMap (ρ : R →+* R') (hρ : Function.Injective ρ) (r : R) :
    fracMap ρ hρ (algebraMap R _ r) = algebraMap R' _ (ρ r) := by
  simp [fracMap, IsFractionRing.map]

theorem jK_comp_spMap (ρ : R →+* R') (hρ : Function.Injective ρ) :
    jK R' ≫ spMap ρ = spMap (fracMap ρ hρ) ≫ jK R := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (fracMap_algebraMap ρ hρ r).symm

def fracAut (σ : R' ≃+* R') : FractionRing R' ≃+* FractionRing R' :=
  IsFractionRing.ringEquivOfRingEquiv σ

theorem fracAut_algebraMap (σ : R' ≃+* R') (x : R') :
    fracAut σ (algebraMap R' _ x) = algebraMap R' _ (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracAut_fracMap {ρ : R →+* R'} (hρ : Function.Injective ρ) (σ : Gal ρ) (x : FractionRing R) :
    fracAut σ.1 (fracMap ρ hρ x) = fracMap ρ hρ x := by
  have h : ((fracAut σ.1).toRingHom.comp (fracMap ρ hρ)) = fracMap ρ hρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracMap_algebraMap, fracAut_algebraMap, σ.2 r]
  exact congrArg (fun f : FractionRing R →+* FractionRing R' => f x) h

def genMap {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ) (β : G'.left ⟶ G.left)
    (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _ ≫ spMap (fracMap ρ hρ)) (by
    rw [Category.assoc, hβ, ← Category.assoc, pullback.condition, Category.assoc, jK_comp_spMap ρ hρ,
      Category.assoc])

theorem genMap_fst {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β :=
  pullback.lift_fst _ _ _

theorem genMap_snd {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap ρ hρ) :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.GenDesc
end
end
