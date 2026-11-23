module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.LinearAlgebra.Matrix.Block
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

section

open NumberField

namespace GlobalTheory

open NumberField Matrix in
open Polynomial in
private theorem aeval_mulVec_of_eigenvector {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (μ : K) (x : Fin n → R) (hx : M *ᵥ x = algebraMap K R μ • x)
    (p : K[X]) : (aeval M p) *ᵥ x = algebraMap K R (p.eval μ) • x := by
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ x = algebraMap K R (μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hx, smul_smul, pow_succ',
        map_mul, mul_comm]

  rw [aeval_eq_sum_range, Matrix.sum_mulVec, eval_eq_sum_range, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.smul_mulVec, hpow, map_mul, mul_smul, algebraMap_smul]


open NumberField Matrix in
open Polynomial in
theorem _root_.GlobalTheory.exists_eigen_projector_ringOfIntegers : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K)), Function.Injective emb → ∀ τ : E →+* ℂ, ∃ (m : ℕ) (a : Fin m → 𝓞 E) (κ : Fin m → K), ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap K R (κ k) • ρ (a k)) = algebraMap K R (emb τ (b : E)) • ∑ k, algebraMap K R (κ k) • ρ (a k)) ∧ ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap K R (emb τ (b : E)) • x) → (∑ k, algebraMap K R (κ k) • ρ (a k)).mulVec x = x := by
  intro E K _ _ _ emb hemb τ
  classical
  haveI : CharZero K := ⟨fun a b h => by
    have : (emb τ) (a : E) = (emb τ) (b : E) := by simpa using h
    exact Nat.cast_injective ((emb τ).injective this)⟩
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α0)).exists_integral_multiple
  let θ : 𝓞 E := ⟨y • α0, hyint⟩
  have hθ : (θ : E) = y • α0 := rfl
  have hadj : Algebra.adjoin ℚ {α0} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α0), hα0, IntermediateField.top_toSubalgebra]

  have hsep : ∀ σ σ' : E →+* K, σ θ = σ' θ → σ = σ' := by
    intro σ σ' h
    rw [hθ, map_zsmul, map_zsmul] at h
    have h' : σ α0 = σ' α0 := smul_right_injective K (by exact_mod_cast hy0) h
    have := AlgHom.ext_of_adjoin_eq_top (φ₁ := σ.toRatAlgHom) (φ₂ := σ'.toRatAlgHom) hadj
      (by rintro _ rfl; exact h')
    ext z
    exact congrArg (fun φ : E →ₐ[ℚ] K => φ z) this
  have hpoly : ∀ b : 𝓞 E, ∃ D : ℤ, D ≠ 0 ∧ ∃ h : ℤ[X], (D : 𝓞 E) * b = aeval θ h := by
    intro b
    have hb : (b : E) ∈ Algebra.adjoin ℚ {α0} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨p, hp⟩ := hb
    obtain ⟨c, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X))
    refine ⟨c, nonZeroDivisors.ne_zero hc.1, IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X)), ?_⟩
    have hy' : (y : E) ≠ 0 := by exact_mod_cast hy0
    have hθα : aeval (θ : E) (C ((y : ℚ)⁻¹) * X) = α0 := by
      rw [hθ, zsmul_eq_mul]
      simp only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast]
      field_simp
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply]
    have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
    rw [hθc, ← aeval_map_algebraMap ℚ, hc.2, map_zsmul, aeval_comp, hθα]
    have hp' : aeval α0 p = (b : E) := hp
    rw [hp', zsmul_eq_mul, map_mul, map_intCast]
  have hθint : IsIntegral ℤ (θ : E) := hyint
  have hfmon : (minpoly ℤ (θ : E)).Monic := minpoly.monic hθint
  have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
  have hf0 : aeval θ (minpoly ℤ (θ : E)) = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply, map_zero, hθc]
    exact minpoly.aeval ℤ (θ : E)
  let σ : (E →+* ℂ) → K := fun τ' => emb τ' (θ : E)
  have hσinj : Function.Injective σ := fun τ1 τ2 h => hemb (hsep _ _ h)
  let P : K[X] := ∏ τ' : E →+* ℂ, (X - C (σ τ'))
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hPdeg : P.natDegree = Fintype.card (E →+* ℂ) := by
    simp only [P]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  have hfK : (minpoly ℤ (θ : E)).map (algebraMap ℤ K) = P := by
    refine eq_of_monic_of_dvd_of_natDegree_le hPmon (hfmon.map _) ?_ ?_
    · apply Finset.prod_dvd_of_coprime
      · exact (pairwise_coprime_X_sub_C hσinj).set_pairwise _
      · intro τ' _
        rw [dvd_iff_isRoot, IsRoot, eval_map_algebraMap,
          show σ τ' = (emb τ').toIntAlgHom (θ : E) from rfl, aeval_algHom_apply, minpoly.aeval,
          map_zero]
    · rw [hPdeg, hfmon.natDegree_map, NumberField.Embeddings.card E ℂ,
        ← hfmon.natDegree_map (algebraMap ℤ ℚ),
        ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint]
      exact minpoly.natDegree_le _
  have hPρ : ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ)
      (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), aeval (ρ θ) P = 0 := by
    intro R _ _ n ρ
    rw [← hfK, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply, hf0,
      map_zero]
  let c : K := (∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ'))⁻¹
  let G : K[X] := C c * ∏ τ' ∈ Finset.univ.erase τ, (X - C (σ τ'))
  have hprod_ne : ∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ' h => sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h) (hσinj e).symm
  have hGev : G.eval (σ τ) = 1 := by
    simp only [G, c, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact inv_mul_cancel₀ hprod_ne
  have hXG : (X - C (σ τ)) * G = C c * P := by
    simp only [G, P]
    rw [← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (σ τ')) (Finset.mem_univ τ)]
    ring
  clear_value G c P
  refine ⟨G.natDegree + 1, fun k => θ ^ (k : ℕ), fun k => G.coeff k, ?_⟩
  intro R _ _ n ρ
  have hsum : ∑ k : Fin (G.natDegree + 1), algebraMap K R (G.coeff k) • ρ (θ ^ (k : ℕ)) =
      aeval (ρ θ) G := by
    rw [aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, algebraMap_smul]
  rw [hsum]
  have hsmul : ∀ (k : K) (M : Matrix (Fin n) (Fin n) R),
      algebraMap K (Matrix (Fin n) (Fin n) R) k * M = algebraMap K R k • M := by
    intro k M
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, algebraMap_smul]
  refine ⟨fun b => ?_, fun x hx => ?_⟩
  · obtain ⟨D, hD, h, hh⟩ := hpoly b
    set hK := h.map (algebraMap ℤ K) with hKdef
    set r := hK.eval (σ τ) with hrdef
    have hr : r = (D : K) * emb τ (b : E) := by
      rw [hrdef, hKdef, eval_map_algebraMap,
        show σ τ = ((emb τ).comp (algebraMap (𝓞 E) E)).toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    have hq := (mul_divByMonic_eq_iff_isRoot (p := hK - C r) (a := σ τ)).2
      (by rw [IsRoot, eval_sub, eval_C, hrdef, sub_self])
    have hkey : hK * G = C r * G + C c * ((hK - C r) /ₘ (X - C (σ τ))) * P := by
      calc hK * G = C r * G + ((X - C (σ τ)) * ((hK - C r) /ₘ (X - C (σ τ)))) * G := by
            rw [hq]; ring
        _ = C r * G + ((hK - C r) /ₘ (X - C (σ τ))) * ((X - C (σ τ)) * G) := by ring
        _ = _ := by rw [hXG]; ring
    have hev := congrArg (aeval (ρ θ)) hkey
    rw [map_add (f := _), map_mul, map_mul, map_mul, hPρ R n ρ, mul_zero, add_zero, aeval_C] at hev
    have hρh : aeval (ρ θ) hK = algebraMap K _ (D : K) * ρ b := by
      rw [hKdef, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    rw [hρh, hr, map_mul, mul_assoc, mul_assoc] at hev
    have hu : IsUnit (algebraMap K (Matrix (Fin n) (Fin n) R) (D : K)) :=
      (IsUnit.mk0 _ (by exact_mod_cast hD)).map _
    rw [hu.mul_left_cancel hev, hsmul]
  · rw [aeval_mulVec_of_eigenvector (ρ θ) (σ τ) x (hx θ) G, hGev, map_one, one_smul]

end GlobalTheory
end

section

namespace GlobalTheory.UnitriangularLowerMulEq

open Matrix

theorem eq_of_unitriangular_of_eq_lower_mul {S : Type} [inst : CommRing S] {n : ℕ}
    (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), j < i → A i j = (0 : S)) (hA1 : ∀ (i : Fin n), A i i = (1 : S))
    (hA' : ∀ (i j : Fin n), j < i → A' i j = (0 : S)) (hA'1 : ∀ (i : Fin n), A' i i = (1 : S))
    (hL : ∀ (i j : Fin n), i < j → L i j = (0 : S)) (h : A' = L * A) : A' = A := by
  classical
  have hAb : A.BlockTriangular id := fun i j hji => hA i j hji
  have hA'b : A'.BlockTriangular id := fun i j hji => hA' i j hji
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAb]
    simp [hA1]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hLeq : L = A' * A⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have : Invertible A := A.invertibleOfIsUnitDet hu
  have hLb : L.BlockTriangular id := hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)
  have hoff : ∀ i j, i ≠ j → L i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji
  have hdiag : ∀ i, L i i = 1 := by
    intro i
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul])
      (by simp), hA1, mul_one, hA'1] at hii
    exact hii.symm
  have hL1 : L = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  rw [h, hL1, Matrix.one_mul]

end GlobalTheory.UnitriangularLowerMulEq
end

section

namespace GlobalTheory

open Matrix

theorem eq_cols_mul_inv_minor_mul_rows {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by
  have hu : IsUnit (π.submatrix ι κ).det := isUnit_iff_ne_zero.mpr hd
  have hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hA : π.submatrix ι κ
      = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hrA : (π.submatrix ι κ).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin := by
    rw [hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hr : π.rank ≤ (π.submatrix id κ).rank := by
    rw [hπ]
    calc r = (π.submatrix ι κ).rank := hrA.symm
      _ ≤ (π.submatrix id κ).rank := by
        conv_lhs => rw [hA]
        exact Matrix.rank_mul_le_right _ _
  have heq := Submodule.eq_of_le_of_finrank_le hle (by simpa only [Matrix.finrank_range_mulVecLin] using hr)
  have hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j := by
    intro j
    have : (fun i => π i j) ∈ LinearMap.range π.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp⟩
    rw [← heq] at this
    exact this
  choose c hc using hcol
  set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX
  have h1 : π = π.submatrix id κ * X := by
    ext i j
    have := congrFun (hc j) i
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have h2 : π.submatrix ι id = π.submatrix ι κ * X := by
    ext i j
    have := congrFun (congrFun h1 (ι i)) j
    simpa [Matrix.mul_apply] using this
  rw [h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  exact h1

theorem exists_cols_det_ne_zero_of_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by
  have hu : IsUnit (R * u).det := isUnit_iff_ne_zero.mpr hd
  have hrA : (R * u).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hrR : R.rank = r := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height R
    · calc r = (R * u).rank := hrA.symm
        _ ≤ R.rank := Matrix.rank_mul_le_left _ _
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω R.col
  haveI : Fintype K := Fintype.ofInjective a ha
  have hcard : Fintype.card K = r := by
    rw [← finrank_span_eq_card hli, hspan, Matrix.finrank_span_range_col, hrR]
  let e : Fin r ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit] at h3
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)

theorem rank_minor_factorisation :
    ∀ (Ω : Type) [Field Ω] (n r : ℕ) (π : Matrix (Fin n) (Fin n) Ω), π.rank = r → ∀ ι : Fin r → Fin n, (∀ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 → π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id) ∧ ∀ u : Matrix (Fin n) (Fin r) Ω, π * u = u → (u.submatrix ι id).det ≠ 0 → ∃ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 := by
  intro Ω _ n r π hπ ι
  refine ⟨fun κ hd => eq_cols_mul_inv_minor_mul_rows π hπ ι κ hd, fun u hu hd => ?_⟩
  have h : π.submatrix ι id * u = u.submatrix ι id := by
    ext i j
    have := congrFun (congrFun hu (ι i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := exists_cols_det_ne_zero_of_mul (π.submatrix ι id) u (h ▸ hd)
  exact ⟨κ, hκ⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_mul_pow_mem_of_fg {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (A B : Subalgebra O Ω) (hA : A.FG)
    (hB : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    ∃ d ∈ B, d ≠ 0 ∧ ∀ a ∈ A, ∃ n : ℕ, a * d ^ n ∈ B := by
  classical
  obtain ⟨s, hs⟩ := hA
  have hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hB x
    exact ⟨b, hb, hb0, by rw [hx]; exact ha⟩
  choose den hdenB hden0 hdenmul using hden
  have hD : ∏ x ∈ s, den x ∈ B := Subalgebra.prod_mem B (fun x _ => hdenB x)
  refine ⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>

    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]
    exact mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) =
        x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m +
          y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : x * y * (∏ z ∈ s, den z) ^ (n + m) =
        (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial


open Polynomial in
theorem _root_.GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint

end GlobalTheory
end
