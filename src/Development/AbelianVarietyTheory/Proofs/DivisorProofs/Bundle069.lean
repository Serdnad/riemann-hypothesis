module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Basic.Real.Sign
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

section

namespace GlobalTheory.DiagonalConjugateExistence

theorem exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hA, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]
  have hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  ext i j
  have := congrFun (hv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

end GlobalTheory.DiagonalConjugateExistence
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericGroupDet

theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g

  simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end GlobalTheory.GenericGroupDet
end
end

section

open Matrix

namespace GlobalTheory

theorem herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by
  funext i
  simp only [mulVec, dotProduct, Pi.star_apply, star_sum, map_apply, star_mul', star_star]

theorem herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hz : star v ≠ 0 := by
    intro h; apply hv; simpa using congrArg star h
  have := hpos (star v) hz
  rw [star_star, hHv, dotProduct_zero] at this
  simp at this

theorem herm_gamma : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  intro g H₁ H₂ h1 h2 hpos
  have hdet : IsUnit H₁.det := isUnit_iff_ne_zero.2 (herm_gamma_det_ne_zero H₁ hpos)
  refine ⟨Matrix.toLin' ((H₁⁻¹ * H₂).map star), ?_, ?_⟩
  · intro z w
    rw [Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · intro z w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec,
      herm_gamma_map_mulVec_dot, mulVec_mulVec]
    congr 2
    have hT : ((H₁⁻¹ * H₂).map star)ᵀ = (H₁⁻¹ * H₂)ᴴ := rfl
    rw [hT, conjTranspose_mul, h2.eq, conjTranspose_nonsing_inv, h1.eq, Matrix.mul_assoc]

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem spectral_parts_of_diag {n : Type} [Fintype n] [DecidableEq n] (Y J U : Matrix n n ℂ)
    (μ : n → ℝ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (hY : Y = U * diagonal (fun j => (μ j : ℂ)) * Uᴴ) (hJ : J * Y = -(Y * J)) :
    ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  classical
  set φ : (ℝ → ℝ) → Matrix n n ℂ := fun f => U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ
    with hφ
  have hcongr : ∀ f g : ℝ → ℝ, (∀ x, f x = g x) → φ f = φ g := by
    intro f g h
    rw [show f = g from funext h]
  have hmul : ∀ f g : ℝ → ℝ, φ f * φ g = φ (fun x => f x * g x) := by
    intro f g
    simp only [hφ]
    calc U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ *
          (U * diagonal (fun j => ((g (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * (Uᴴ * U) *
          diagonal (fun j => ((g (μ j) : ℝ) : ℂ))) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, Matrix.mul_one, diagonal_mul_diagonal]
        simp only [Complex.ofReal_mul]
  have hsmul : ∀ (c : ℝ) (f : ℝ → ℝ), (c : ℂ) • φ f = φ (fun x => c * f x) := by
    intro c f
    simp only [hφ]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  have hherm : ∀ f : ℝ → ℝ, (φ f).IsHermitian := by
    intro f
    simp only [hφ]
    apply isHermitian_mul_mul_conjTranspose
    rw [isHermitian_diagonal_iff]
    intro j
    exact Complex.conj_ofReal _
  have hid : Y = φ (fun x => x) := hY
  set K := Uᴴ * J * U with hK
  have hJK : J = U * K * Uᴴ := by
    rw [hK]
    calc J = (U * Uᴴ) * J * (U * Uᴴ) := by rw [h2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKD : K * diagonal (fun j => (μ j : ℂ)) = -(diagonal (fun j => (μ j : ℂ)) * K) := by
    have e := congrArg (fun M => Uᴴ * M * U) hJ
    simp only [hY] at e
    have a1 : Uᴴ * (J * (U * diagonal (fun j => (μ j : ℂ)) * Uᴴ)) * U
        = K * diagonal (fun j => (μ j : ℂ)) * (Uᴴ * U) := by
      simp only [hK, Matrix.mul_assoc]
    have a2 : Uᴴ * (-(U * diagonal (fun j => (μ j : ℂ)) * Uᴴ * J)) * U
        = -((Uᴴ * U) * diagonal (fun j => (μ j : ℂ)) * K) := by
      simp only [hK, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    rw [a1, a2, h1, Matrix.mul_one, Matrix.one_mul] at e
    exact e
  have hkey : ∀ f : ℝ → ℝ, J * φ f = φ (fun x => f (-x)) * J := by
    intro f
    have hK2 : K * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))
        = diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * K := by
      ext i j
      have e := congrFun (congrFun hKD i) j
      simp only [mul_diagonal, diagonal_mul, Matrix.neg_apply] at e ⊢
      by_cases h0 : K i j = 0
      · simp [h0]
      · have : (μ j : ℂ) = -(μ i : ℂ) := by
          apply mul_left_cancel₀ h0
          rw [e]; ring
        have h3 : μ j = -μ i := by exact_mod_cast this
        rw [h3, mul_comm]
    simp only [hφ]
    rw [hJK]
    calc U * K * Uᴴ * (U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (K * (Uᴴ * U) * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * (Uᴴ * U) * K) * Uᴴ := by
          rw [h1, Matrix.mul_one, Matrix.mul_one, hK2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hs1 : ∀ x : ℝ, x * Real.sign x = |x| := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  have hs2 : ∀ x : ℝ, |x| * Real.sign x = x := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  refine ⟨Finset.univ.image (fun j => |μ j|),
    fun ν => φ (fun x => if |x| = ν then Real.sign x else 0),
    fun ν => φ (fun x => if |x| = ν then 1 else 0), ?_, ?_, ?_⟩
  · simp only [hsmul]
    simp only [hφ]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hY]
    congr 2
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq]
      rw [Finset.sum_eq_single |μ i|]
      · simp only [if_true, hs2]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_image_of_mem (fun j => |μ j|) (Finset.mem_univ i)) h
    · simp [diagonal_apply_ne _ hij]
  · intro ν
    clear hY hK hKD hJK hφ
    clear_value φ
    beta_reduce
    refine ⟨hherm _, hherm _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [mul_comm, hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, one_mul]
      · simp
    · have : ∀ f : ℝ → ℝ, -φ f = φ (fun x => -f x) := by
        intro f
        have := hsmul (-1) f
        simpa using this
      rw [hkey, ← Matrix.neg_mul, this]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
      split_ifs with h
      · exact Real.sign_neg
      · simp
    · rw [hkey]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
  · intro ν ν'
    clear hY hK hKD hJK hφ hkey hs1 hs2 hherm hsmul hid
    clear_value φ
    beta_reduce
    exact (hmul _ _).trans ((hcongr _ _ fun x => mul_comm _ _).trans (hmul _ _).symm)

theorem hermitian_spectral_parts_anticommute :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian →
      J * Y = -(Y * J) →
      ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  intro n _ _ Y J hY hJ
  refine spectral_parts_of_diag Y J (hY.eigenvectorUnitary : Matrix n n ℂ) hY.eigenvalues
    ?_ ?_ ?_ hJ
  · exact hY.eigenvectorUnitary.2.1
  · exact hY.eigenvectorUnitary.2.2
  · exact hY.spectral_theorem

end GlobalTheory
end

section

namespace GlobalTheory


open Algebra in
theorem isAlgebraic_of_subring_isAlgebraic {L : Type} [Field L] [Algebra ℂ L]
    (S : Subalgebra ℂ L) (B : Subring L) (z : L)
    (hB : ∀ b ∈ B, IsAlgebraic S b) (hz : IsAlgebraic B z) : IsAlgebraic S z := by
  set T := adjoin ℂ ((S : Set L) ∪ (B : Set L)) with hT
  have hBT : ∀ b ∈ B, b ∈ T := fun b hb => subset_adjoin (Or.inr hb)
  let f : B →+* T :=
    { toFun := fun b => ⟨b.1, hBT b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra B T := f.toAlgebra
  have : IsScalarTower B T L := .of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap B T) := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hzT : IsAlgebraic T z := hz.extendScalars hinj
  have hSle : S ≤ adjoin ℂ (S : Set L) := subset_adjoin
  have key : IsAlgebraic (adjoin ℂ (S : Set L)) z := by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℂ) (s := (S : Set L) ∪ (B : Set L)) ?_ hzT
    intro x hx
    rcases hx.1 with h | h
    · exact absurd h hx.2
    · exact (hB x h).tower_top_of_subalgebra_le hSle
  rwa [Algebra.adjoin_eq] at key

end GlobalTheory
end
