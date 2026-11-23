module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

section

open scoped ComplexOrder
open Matrix

namespace GlobalTheory

theorem radical_elt_moving_dual_to_majorant (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  have hθJ : θᴴ * J = J * θ := by
    have := hQ.isHermitian.eq
    rwa [conjTranspose_mul, hJ] at this
  have hYX : Y₂ᴴ * J * X₂ = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hinj : Function.Injective X₂.mulVec := by
    intro a b hab
    have := congrArg (fun v => (Y₂ᴴ * J).mulVec v) hab
    simpa [Matrix.mulVec_mulVec, hYX] using this
  have hP : (X₂ᴴ * (J * θ) * X₂).PosDef := hQ.conjTranspose_mul_mul_same hinj
  obtain ⟨P, hPdef⟩ : ∃ P, P = X₂ᴴ * (J * θ) * X₂ := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPiH : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.isHermitian.eq]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = θ * X₂ * P⁻¹ := ⟨_, rfl⟩
  have hXY' : X₂ᴴ * J * Y' = 1 := by
    rw [← hPPi, hY', hPdef]; simp only [Matrix.mul_assoc]
  have hY'Y' : Y'ᴴ * J * Y' = 0 := by
    have h1 : ∀ B : Matrix (Fin n) (Fin p) ℂ, θᴴ * (J * (θ * B)) = J * B := by
      intro B
      rw [← Matrix.mul_assoc, hθJ, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθ, Matrix.one_mul]
    have h2 : X₂ᴴ * (J * (X₂ * P⁻¹)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
    rw [hY']
    simp only [conjTranspose_mul, hPiH, Matrix.mul_assoc, h1, h2, Matrix.mul_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Y' - Y₂ := ⟨_, rfl⟩
  have hXD : X₂ᴴ * J * D = 0 := by rw [hD, Matrix.mul_sub, hXY', hXY, sub_self]
  have hDX : Dᴴ * J * X₂ = 0 := by
    have := congrArg conjTranspose hXD
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hkey : Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D = 0 := by
    rw [hD]
    simp only [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hY'Y' hYY ⊢
    rw [hY'Y', hYY]
    abel

  have tXX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have tXD : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (D * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXD, Matrix.zero_mul]
  have tDX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), Dᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have tXY : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (Y₂ * B)) = B := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hXX' : X₂ᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hXX]
  have hXD' : X₂ᴴ * (J * D) = 0 := by rw [← Matrix.mul_assoc, hXD]
  have hDX' : Dᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hDX]
  have hXY'' : X₂ᴴ * (J * Y₂) = 1 := by rw [← Matrix.mul_assoc, hXY]
  obtain ⟨E, hE⟩ : ∃ E, E = Dᴴ * J * Y₂ := ⟨_, rfl⟩
  have hE' : Dᴴ * (J * Y₂) = E := by rw [hE, Matrix.mul_assoc]
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = 1 + (D * X₂ᴴ * J - X₂ * Dᴴ * J + X₂ * E * X₂ᴴ * J) := ⟨_, rfl⟩
  have huJ : uᴴ * J * u = J := by
    have hexp : uᴴ * J * u = J + J * X₂ * (Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D) * X₂ᴴ * J := by
      rw [hu, hE]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_one,
        conjTranspose_conjTranspose, hJ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, tXX, tXD, tDX,
        hXX', hXD', hDX', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]
      abel
    rw [hexp, hkey]; simp
  have huX : u * X₂ = X₂ := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXX', hDX',
      Matrix.mul_zero, add_zero, sub_zero]
  have huY : u * Y₂ = Y' := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXY'',
      Matrix.mul_one, hE']
    rw [hD]; abel
  have hdetJ : J.det ≠ 0 := by
    intro h0
    have := hQ.det_pos
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hudet : IsUnit u.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetJ ?_
    have := congrArg Matrix.det huJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have huU : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr hudet
  refine ⟨huU.unit, ?_, ?_, ?_, ?_⟩
  · simpa using huJ
  · simpa using huX
  · intro v hv
    have hv' : X₂ᴴ *ᵥ (J *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec]; exact hv
    refine ⟨-(Dᴴ *ᵥ (J *ᵥ v)), ?_⟩
    simp only [IsUnit.unit_spec, hu, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero, Matrix.mulVec_neg]
    abel
  · simp only [IsUnit.unit_spec, huY, hY', Matrix.mul_assoc, hPiP, Matrix.mul_one]

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  haveI : Nontrivial Y := ⟨⟨u, 0, hu⟩⟩
  set S : Y →ₗ[ℂ] Y := T ∘ₗ LinearMap.adjoint T with hS
  have hsym : S.IsSymmetric := by
    intro a b
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, LinearMap.adjoint_inner_left]
  have hq : ∀ y : Y, RCLike.re ⟪S y, y⟫_ℂ = ‖LinearMap.adjoint T y‖ ^ 2 := by
    intro y
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, inner_self_eq_norm_sq]
  have hev : ∀ μ : ℝ, Module.End.HasEigenvalue S (μ : ℂ) → m ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    by_contra hlt
    have hlt : μ < m := not_le.mp hlt
    have hSv : S v = (μ : ℂ) • v := hv.apply_eq_smul
    have hle : ∀ k, P k ≤ (ℂ ∙ v)ᗮ := by
      intro k y hy
      obtain ⟨l, hml, hly⟩ := hl k
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 := hsym v y
      have h2 : S y = (l : ℂ) • y := hly y hy
      rw [hSv, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h3 : ((μ : ℂ) - (l : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have : μ = l := by exact_mod_cast h
        linarith
      have h4 : ((μ : ℂ) - (l : ℂ)) * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left h3
    have hv' : v ∈ (ℂ ∙ v)ᗮ := by
      have : (⊤ : Submodule ℂ Y) ≤ (ℂ ∙ v)ᗮ := hP ▸ iSup_le hle
      exact this Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hv'
    exact hv.2 hv'
  have h1 := hev _ hsym.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (Set.range fun x : { x : Y // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫_ℂ / ‖(x : Y)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [hq]
    positivity
  have h2 := h1.trans (ciInf_le hb ⟨u, hu⟩)
  simp only [hq] at h2
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  rwa [le_div_iff₀ hpos] at h2

theorem mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos

end GlobalTheory
end

section

open MeasureTheory Matrix

namespace GlobalTheory

theorem typeFunction_unip_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (e : ι ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → K) → GL ι K)
    (hu : ∀ X, (u X : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X Y : Fin a → Fin b → K) : u (Y + X) = u X * u Y := by
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.of_add_of]

theorem typeFunction_constantTerm_eq_zero :
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro K _ _ _ _ _ _ ι _ _ J hJo hJc χ hχ hnt f hf1 hf0
  have hR : ∀ g j (hj : j ∈ J), f (g * j) = f g * (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hg hj), hf1 g hg]
      have : (⟨g * j, J.mul_mem hg hj⟩ : J) = ⟨g, hg⟩ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_right hj).1 h)), zero_mul]
  have hL : ∀ g j (hj : j ∈ J), f (j * g) = (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * f g := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hj hg), hf1 g hg]
      have : (⟨j * g, J.mul_mem hj hg⟩ : J) = ⟨j, hj⟩ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_left hj).1 h)), mul_zero]
  have hRk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (g * y) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hR g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, mul_one] at this
    exact this
  have hLk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (y * g) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hL g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, one_mul] at this
    exact this
  have hNo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)),
      hNo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hRk _ hx g
      rwa [mul_inv_cancel_left] at this
  · exact HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => hf0 g hg)
  · intro x hx y hy g
    rw [hRk y hy, hLk x hx]
  · intro a b e ha hb μ hμ u hu g h
    obtain ⟨Y, hY, hne⟩ := hnt a b e ha hb u hu h
    have key : ∀ X, f (g * (h⁻¹ * u (Y + X) * h)) =
        f (g * (h⁻¹ * u X * h)) * (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) := by
      intro X
      rw [← hR _ _ hY, typeFunction_unip_add e u hu]
      congr 1
      group
    have h1 := integral_add_left_eq_self (μ := μ) (fun X => f (g * (h⁻¹ * u X * h))) Y
    simp only [key] at h1
    rw [integral_mul_const] at h1
    have hc : (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro hc
      exact hne (inv_eq_one.1 (Units.val_eq_one.1 hc))
    by_contra hI
    exact hc (mul_left_cancel₀ hI (h1.trans (mul_one _).symm))

end GlobalTheory
end

section

open MeasureTheory

theorem GlobalTheory.prod_rpow_decay_isBigO_cocompact : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  intro ι _ g b hb hg
  classical
  choose C hC using hg
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    have h := hC i 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  refine Asymptotics.IsBigO.of_bound ((∏ i, C i) * n ^ b) ?_
  have hev : ∀ᶠ v : EuclideanSpace ℝ ι in Filter.cocompact _, 0 < ‖v‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hev] with v hv
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : v = 0 := Subsingleton.elim _ _
    simp [this] at hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnorm : ‖v‖ ≤ n * |v i₀| := by
    have h2 : ‖v‖ ^ 2 ≤ (n * |v i₀|) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v.ofLp i‖ ^ 2 ≤ ∑ _i : ι, |v i₀| ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hi₀ i (Finset.mem_univ _)) 2
        _ = n * |v i₀| ^ 2 := by simp [hn]
        _ ≤ (n * |v i₀|) ^ 2 := by
              rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hnpos : 0 < n := by linarith
  have hpos : 0 < ‖v‖ / n := by positivity
  have hle : ‖v‖ / n ≤ 1 + |v i₀| := by
    rw [div_le_iff₀ hnpos]; nlinarith [abs_nonneg (v i₀)]
  have hw : (1 + |v i₀|) ^ (-b) ≤ n ^ b * ‖v‖ ^ (-b) := by
    calc (1 + |v i₀|) ^ (-b) ≤ (‖v‖ / n) ^ (-b) := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = n ^ b * ‖v‖ ^ (-b) := by
        rw [Real.div_rpow (norm_nonneg _) hnpos.le, Real.rpow_neg hnpos.le, div_inv_eq_mul, mul_comm]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖ ≤ ∏ i ∈ Finset.univ.erase i₀, C i :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (hC i (v i)).trans
      (mul_le_of_le_one_right (hC0 i)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (v i)]) (by linarith))))
  have h0 : ‖g i₀ (v i₀)‖ ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) :=
    (hC i₀ _).trans (mul_le_mul_of_nonneg_left hw (hC0 i₀))
  have hsplitg := Finset.mul_prod_erase Finset.univ (fun i => ‖g i (v i)‖) (Finset.mem_univ i₀)
  have hsplitC := Finset.mul_prod_erase Finset.univ C (Finset.mem_univ i₀)
  rw [norm_prod, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hsplitg, ← hsplitC]
  calc ‖g i₀ (v i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖
      ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) * ∏ i ∈ Finset.univ.erase i₀, C i :=
        mul_le_mul h0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (mul_nonneg (hC0 i₀) (mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = C i₀ * (∏ i ∈ Finset.univ.erase i₀, C i) * n ^ b * ‖v‖ ^ (-b) := by ring
end

section

open NumberField Matrix

namespace GlobalTheory.SylvesterInertia

theorem re_quad_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (u : Fin n → ℂ) :
    (star u ⬝ᵥ M *ᵥ u).re = ∑ i, hM.eigenvalues i * Complex.normSq
      ((star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, hU] using this
  set y := star U *ᵥ u with hy
  have hu : u = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hU, Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2, one_mulVec]
  have h1 : star u ⬝ᵥ M *ᵥ u = star y ⬝ᵥ (star U * M * U) *ᵥ y := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose, Matrix.mul_assoc]
  rw [h1, hD, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  have e1 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).re = hM.eigenvalues i := by simp
  have e2 : ((RCLike.ofReal (hM.eigenvalues i) : ℂ)).im = 0 := by simp
  simp only [e1, e2]
  ring

theorem finrank_le_card_of_vanish {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (P : Submodule ℂ (Fin n → ℂ))
    (s : Fin n → Prop) [DecidablePred s]
    (h : ∀ u ∈ P, (∀ i, s i → (U *ᵥ u) i = 0) → u = 0) :
    Module.finrank ℂ P ≤ Fintype.card {i // s i} := by
  let f : P →ₗ[ℂ] ({i // s i} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // s i} → Fin n)) ∘ₗ (Matrix.mulVecLin U) ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := h u u.2 (fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      simpa [f, LinearMap.funLeft_apply] using this)
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa using this

end GlobalTheory.SylvesterInertia
end

section

noncomputable section

open Filter Asymptotics

namespace GlobalTheory.BigTop.Fun

theorem exists_log_le_two_rpow {eps : ℝ} (he : 0 < eps) : ∃ x0 : ℝ, ∀ y, x0 ≤ y → Real.log y ≤ 2 * y ^ eps := by
  have hev : ∀ᶠ y in atTop, Real.log y ≤ 2 * y ^ eps := by
    have h := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 2)
    filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
    exact (le_abs_self _).trans hy
  exact eventually_atTop.1 hev

end GlobalTheory.BigTop.Fun

end
end
