module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OnCoord
variable {D : D7}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) :=
  D.host.conjE_apply (embT D τ) x

theorem coord_emb (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (y : Matrix (Fin N') (Fin N) D.host.E) :
    coordB D (tor0 D cc δ) b k (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D y (b k) : D.host.K) : D.host.E) := by
  unfold hYY
  rw [← h.2]

  simp only [coordB, embV, tor0, map_sum, map_mul, embT_conj]

theorem coord_add (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (z w : VC D N N') :
    coordB D T b k (z + w) = coordB D T b k z + coordB D T b k w := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coord_smul (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (c : ℂ) (z : VC D N N') :
    coordB D T b k (c • z) = c * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

noncomputable def coordL (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b k
  map_add' := coord_add T b k
  map_smul' := coord_smul T b k

theorem coord_sum (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) {ι : Type} (s : Finset ι) (z : ι → VC D N N') :
    coordB D T b k (∑ i ∈ s, z i) = ∑ i ∈ s, coordB D T b k (z i) :=
  map_sum (coordL T b k) z s

theorem embT_injective : Function.Injective (embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply Subtype.ext
  have h1 : D.host.sigmaOf (D.eTau τ : D.R.GG) = D.host.sigmaOf (D.eTau τ' : D.R.GG) := by
    ext x
    have := DFunLike.congr_fun h x
    exact D.host.φ₀.injective this
  exact (D.host.gal).symm.injective h1

theorem indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, embT D τ x * c τ = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp (fun τ => (embT D τ : D.host.E →* ℂ))
    (fun τ τ' h => embT_injective (RingHom.coe_monoidHom_injective h))
  refine Fintype.linearIndependent_iff.1 h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply, mul_comm] using h x

theorem lin_eq_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (f : VC D N N' →ₗ[ℂ] ℂ)
    (h : ∀ y, f (embV D (tor0 D cc δ) y) = 0) (z : VC D N N') : f z = 0 := by
  have h1 : ∀ τ i j, f (coordV D (τ, i, j)) = 0 := by
    intro τ i j
    refine indep (fun τ => f (coordV D (τ, i, j))) (fun x => ?_) τ
    rw [← h (Matrix.single i j x)]
    have : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • coordV D (τ, i, j) := by
      funext τ' i' j'
      simp only [embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]
      by_cases hi : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hi
        simp
      · have : ¬ (i' = i ∧ j' = j) := fun h => hi ⟨h.1.symm, h.2.symm⟩
        simp [hi, this]

    rw [this, map_sum]
    simp
  have h2 : z = ∑ τ, ∑ i, ∑ j, z τ i j • coordV D (τ, i, j) := by
    funext τ' i' j'
    simp [coordV, Finset.sum_apply, ite_and]
  rw [h2]

  simp [map_sum, h1]

theorem embV_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (x + y) = embV D (tor0 D cc δ) x + embV D (tor0 D cc δ) y := by
  funext τ i j
  simp [embV, tor0]

theorem embV_smul (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (a : D.host.K)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • y) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) y := by
  funext τ i j
  have : (a • y) i j = (a : D.host.E) * y i j := rfl
  simp only [embV, tor0, this, map_mul, h.1 τ a, Pi.smul_apply, smul_eq_mul]

theorem coords_of_orthonormal_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  intro D h cc δ N N' r b hb
  have h2 : ∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0 := by
    intro j k
    rw [coord_emb h, hb.1 k j]
    split_ifs <;> simp
  have hc : ∀ (c : Fin r → ℂ) j,
      coordB D (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j := by
    intro c j
    simp [coord_sum, coord_smul, h2]
  let P : VC D N N' →ₗ[ℂ] VC D N N' :=
    ∑ k, (coordL (tor0 D cc δ) b k).smulRight (embV D (tor0 D cc δ) (b k))
  have hP : ∀ z, P z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  have hE : ∀ y, P (embV D (tor0 D cc δ) y) = embV D (tor0 D cc δ) y := by
    intro y
    have hy : y ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hP]
      simp [h2]
    | zero =>
      have : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
        funext τ i j
        simp [embV, tor0]
      rw [this, map_zero]
    | add x y _ _ hx hy => rw [embV_add, map_add (f := _), hx, hy]
    | smul a x _ hx => rw [embV_smul h, map_smul, hx]
  have h1 : ∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    rw [← hP]
    funext τ i j
    let e : VC D N N' →ₗ[ℂ] ℂ :=
      { toFun := fun z => z τ i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have := lin_eq_zero cc δ (e ∘ₗ (LinearMap.id - P)) (fun y => by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, hE, LinearMap.id_apply, sub_self, map_zero]) z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at this
    exact sub_eq_zero.1 this
  refine ⟨h1, h2, fun z w => ?_, fun x => ⟨fun hx k => ?_, fun hx => ?_⟩, fun z w hzw => ?_, fun c => ?_⟩
  · have hw : ∀ τ i j, w τ i j = ∑ k, coordB D (tor0 D cc δ) b k w * (tor0 D cc δ).emb τ (b k i j) := by
      intro τ i j
      have := congrFun (congrFun (congrFun (h1 w) τ) i) j
      simpa [Finset.sum_apply, embV] using this
    obtain ⟨c, hcw⟩ : ∃ c : Fin r → ℂ, ∀ k, coordB D (tor0 D cc δ) b k w = c k := ⟨_, fun _ => rfl⟩
    simp only [hcw] at hw ⊢

    simp only [hw, map_sum, map_mul, Finset.mul_sum, coordB, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · induction hx using AddSubgroup.closure_induction generalizing k with
    | mem x hx =>
      obtain ⟨w, hw, j, rfl⟩ := hx
      rw [coord_smul, h2]
      split_ifs
      · rw [mul_one]; exact hw
      · rw [mul_zero]; exact zero_mem _
    | zero =>
      have : coordB D (tor0 D cc δ) b k 0 = 0 := map_zero (coordL (tor0 D cc δ) b k)
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy => rw [coord_add]; exact add_mem (hx k) (hy k)
    | neg x _ hx =>
      have : coordB D (tor0 D cc δ) b k (-x) = - coordB D (tor0 D cc δ) b k x :=
        map_neg (coordL (tor0 D cc δ) b k) x
      rw [this]; exact neg_mem (hx k)
  · rw [h1 x]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, hx k, k, rfl⟩
  · rw [h1 z, h1 w]
    exact Finset.sum_congr rfl fun k _ => by rw [show coordB D (tor0 D cc δ) b k z = coordB D (tor0 D cc δ) b k w from congrFun hzw k]
  · exact ⟨_, funext (hc c)⟩

end GlobalTheory.OnCoord
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem aut_conj_comm (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E) :
    σ (D.host.conj x) = D.host.conj (σ x) := by
  have h : σ * D.host.conj = D.host.conj * σ :=
    (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (fun f : D.host.E ≃ₐ[ℚ] D.host.E => f x) h

theorem hYY_map_aut (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (x.map σ) (y.map σ) = hYY D x y := by
  let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
  unfold hYY
  rw [← Algebra.trace_eq_of_algEquiv e (∑ i, ∑ j, x i j * D.host.conj (y i j))]
  congr 1
  show _ = σ _

  simp only [map_sum, map_mul, Matrix.map_apply, aut_conj_comm]

theorem onB_map_aut : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  intro D σ hσ N N' r b hb
  refine ⟨?_, ?_⟩
  · intro i j
    rw [hYY_map_aut D σ hσ]
    exact hb.1 i j
  · let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
    let L : Matrix (Fin N') (Fin N) D.host.E ≃ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E :=
      e.toLinearEquiv.mapMatrix
    have h : (fun j => (b j).map σ) = L.toLinearMap ∘ b := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, hb.2, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.NormSum
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Matrix

noncomputable section

namespace GlobalTheory.RatEqui

variable (D : D7) {N N' : ℕ}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) :=
  Formalism.HC.HostAx.conjE_apply D.host.toHostAx _ _

def adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  (M.map D.host.conj).transpose

theorem adj_map {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (adj D M).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp [adj, embT_conj]

def mulV (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) :
    VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ => (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ)
  map_add' z w := by
    funext τ
    change M'.map (embT D τ) * (Matrix.of (z τ) + Matrix.of (w τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    funext τ
    change M'.map (embT D τ) * (c • Matrix.of (z τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem mulV_apply (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') (τ : D.what₂.Tau) :
    mulV D M' M z τ = (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ) := rfl

theorem mulV_mulV (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M₁' M₁ (mulV D M₂' M₂ z) = mulV D (M₁' * M₂') (M₂ * M₁) z := by
  funext τ
  change M₁'.map (embT D τ) * (M₂'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)) * M₁.map (embT D τ) =
    (M₁' * M₂').map (embT D τ) * Matrix.of (z τ) * (M₂ * M₁).map (embT D τ)
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem mulV_one (z : VC D N N') : mulV D 1 1 z = z := by
  funext τ
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem mulV_sub_left (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D (M₁' - M₂') M z = mulV D M₁' M z - mulV D M₂' M z := by
  funext τ
  change (M₁' - M₂').map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) =
    M₁'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) - M₂'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, Matrix.sub_mul]

theorem mulV_sub_right (M' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M' (M₁ - M₂) z = mulV D M' M₁ z - mulV D M' M₂ z := by
  funext τ
  change M'.map (embT D τ) * Matrix.of (z τ) * (M₁ - M₂).map (embT D τ) =
    M'.map (embT D τ) * Matrix.of (z τ) * M₁.map (embT D τ) - M'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.mul_sub]

theorem Hf_eq_trace (T : Tor D) (z w : VC D N N') :
    Hf D T z w = (∑ τ, Matrix.trace (Matrix.of (z τ) * (Matrix.of (w τ))ᴴ)) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

theorem Hf_mulV (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T (mulV D M' M z) w = Hf D T z (mulV D (adj D M') (adj D M) w) := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change Matrix.trace (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) * (Matrix.of (w τ))ᴴ) =
    Matrix.trace (Matrix.of (z τ) * ((adj D M').map (embT D τ) * Matrix.of (w τ) * (adj D M).map (embT D τ))ᴴ)
  rw [adj_map, adj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pull_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' G = fun z => G (mulV D (adj D γ') γ z) := by
  funext z
  unfold pull
  congr 1
  funext τ
  rw [mulV_apply, adj_map]
  rfl

theorem mulV_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mulV D M' M (pt D (tor0 D cc δ) δ z) = pt D (tor0 D cc δ) δ (M' * z * M) := by
  unfold pt
  rw [map_smul]
  congr 1
  funext τ
  change M'.map (embT D τ) * z.map (embT D τ) * M.map (embT D τ) = (M' * z * M).map (embT D τ)
  simp only [Matrix.map_mul]

theorem adj_mul {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) D.host.E) : adj D (M₁ * M₂) = adj D M₂ * adj D M₁ := by
  unfold adj
  rw [← Matrix.transpose_mul]
  congr 1
  exact Matrix.map_mul (f := (D.host.conj : D.host.E →+* D.host.E))

theorem adj_one {n : ℕ} : adj D (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end GlobalTheory.RatEqui
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.LocIndex

theorem index_coprime_of_multiples {G : Type*} [AddCommGroup G] [AddGroup.FG G] (H : AddSubgroup G) (p : ℕ)
    (hp : p.Prime) (h : ∀ z : G, ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ H) : Nat.Coprime H.index p := by
  have hq : ∀ x : G ⧸ H, ∃ s : ℕ, Nat.Coprime s p ∧ s • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨s, hs, hz⟩ := h z
    refine ⟨s, hs, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hz
  have htor : AddMonoid.IsTorsion (G ⧸ H) := by
    intro x
    obtain ⟨s, hs, hx⟩ := hq x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨s, Nat.pos_of_ne_zero ?_, hx⟩
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hs)
  haveI : Finite (G ⧸ H) := AddCommGroup.finite_of_fg_torsion _ htor
  haveI := Fact.mk hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ H) p hd
  obtain ⟨s, hs, hs0⟩ := hq x
  have : p ∣ s := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hs0
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm this

theorem mul_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) {w : ℂ}
    (hw : w ∈ lamOf D cc δ) : w * D.host.φ₀ ((a : D.host.K) : D.host.E) ∈ lamOf D cc δ := by
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨c * a, cc.mul_mem_right a hc, ?_⟩
    rw [mul_assoc, ← map_mul]
    congr 2
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem exists_multiple_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) (hb : LocBasis D p (YYl D L L') b)
    (z : VC D N N') (hz : z ∈ La D (tor0 D cc δ) L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ LaB D (tor0 D cc δ) b := by
  unfold La at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, ?_⟩
    have key : s • w • embV D (tor0 D cc δ) A =
        ∑ i, (w * D.host.φ₀ ((c i : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) (b i) := by
      funext τ i j
      have h1 := congrArg (fun M => embT D τ (M i j)) hc

      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.sum_apply, map_sum] at h1
      simp only [hD.1 τ] at h1
      simp only [Pi.smul_apply, Finset.sum_apply, embV, tor0, smul_eq_mul, nsmul_eq_mul]
      rw [mul_left_comm, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [key]
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, mul_mem_lamOf D cc δ (c i) hw, i, rfl⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx t
    · rw [mul_smul]; exact nsmul_mem hy s
  | neg x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, by rw [smul_neg]; exact neg_mem hx⟩

theorem index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  intro D hD cc δ N N' r L L' b p hp hfg hb
  haveI : AddGroup.FG (La D (tor0 D cc δ) L L') := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine index_coprime_of_multiples _ p hp fun z => ?_
  obtain ⟨s, hs, hz⟩ := exists_multiple_mem D hD cc δ L L' b p hb z.1 z.2
  exact ⟨s, hs, AddSubgroup.mem_addSubgroupOf.2 hz⟩

end GlobalTheory.NormSum.LocIndex
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem finiteDimensional_of_Gamma_le :
    ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro M Γ k hM hle
  exact GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)

end GlobalTheory.OddFrame
end
