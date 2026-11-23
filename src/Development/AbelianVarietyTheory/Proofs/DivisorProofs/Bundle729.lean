module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle687
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle696
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
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
public import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem ecoef_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (μ : Emb F → ℕ) (n : ℕ), 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (ecoef N a x μ n) = ecoef N a (m * x) (fun j ↦ μ (π.symm j)) n := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x N g m π μ n hN hco hg0 hlev hζ hemb
  obtain ⟨h0, hint, hsupp, -⟩ := hco
  have hmap : ∀ {ι : Sort _} (f : ι → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hmapP : ∀ {p : Prop} (f : p → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'

  have hprod : ∀ ξ : F, g (∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) = ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    rw [map_prod]
    simp only [map_pow, hemb]
    exact Equiv.prod_comp π (fun j ↦ ((j ξ : ℝ) : ℂ) ^ μ (π.symm j)) |>.symm ▸ by
      simp only [Equiv.symm_apply_apply]

  have hchar : ∀ ξ : F, ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → g (eTr (ξ * x)) = eTr (ξ * ((m : F) * x)) := by
    intro ξ hξ
    obtain ⟨r, hr⟩ := (GlobalTheory.T.splitLattice_level_trace_denominator F N 𝔞 𝔟 x ξ hlev hξ).2
    have ht : Algebra.trace ℚ F (ξ * x) = (r : ℚ) / N := by
      rw [eq_div_iff hNq, mul_comm]; exact hr
    have hsm : ξ * ((m : F) * x) = (m : ℚ) • (ξ * x) := by
      rw [Algebra.smul_def, map_intCast]; ring
    have ht' : Algebra.trace ℚ F (ξ * ((m : F) * x)) = (m : ℚ) * ((r : ℚ) / N) := by
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ht]
    have e1 : eTr (ξ * x) = Complex.exp ((2 * Real.pi * Complex.I) / N) ^ r := by
      rw [eTr, ht, ← Complex.exp_int_mul]; congr 1; push_cast; ring
    rw [e1, map_zpow₀, hζ, ← Complex.exp_int_mul, eTr, ht']
    congr 1; push_cast; ring
  have key : ∀ ξ : F, g (a ξ * eTr (ξ * x) * ∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) =
      a ξ * eTr (ξ * ((m : F) * x)) * ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    by_cases ha : a ξ = 0
    · simp [ha]
    have hga : g (a ξ) = a ξ := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; rw [h0]; exact hg0
      · obtain ⟨z, hz⟩ := hint ξ hξ0; rw [hz, map_intCast]
    have hmem : ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; exact Submodule.zero_mem _
      · exact (hsupp ξ hξ0 ha).1
    rw [map_mul, map_mul, hga, hchar ξ hmem, hprod]
  unfold ecoef
  rw [hmap]
  refine finsum_congr fun ξ ↦ ?_
  rw [hmapP]
  refine finsum_congr fun _ ↦ ?_
  exact key ξ

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := GlobalTheory.T.laguerreSignedBinomCoeff_mul k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinValue_linear_change : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, coord b a x i = lam i * coord b' a' (T x) i) → gval k L b a = (∏ i, lam i)⁻¹ ^ k * gval k L' b' a' := by
  first | exact @GlobalTheory.HilbFam.gval_linear_change | exact GlobalTheory.HilbFam.gval_linear_change | (intros; apply GlobalTheory.HilbFam.gval_linear_change <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.JetModular

def rowEquiv (F : Type) [Field F] (γ : SL(2, ℤ)) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  LinearEquiv.ofLinear
    (Matrix.vecMulLinear ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (Matrix.vecMulLinear (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma iterD_const_mul {I : Type} [Fintype I] [DecidableEq I] (u : List I)
    (h : (I → ℂ) → ℂ) (A : ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z ↦ A * h z) z =
      A * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u h z := by
  simpa using _root_.GlobalTheory.HilbFam.iterD_const_mul_reindex I I (Equiv.refl I) u h A z

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma mem_iff_sl2_equiv_mem_mulMat (F : Type) [Field F] [NumberField F] (L : _root_.GlobalTheory.HilbFam.Lat F)
    (γ : SL(2, ℤ)) (x : Fin 2 → F) :
    x ∈ L ↔ _root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x ∈ _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [(_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ).injective (a₁ := y) (a₂ := x) hxy] at hy

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma embeddingCoord_sl2_smul_lemma_3 (F : Type) [Field F] [NumberField F] (γ : SL(2, ℤ)) (τ : ℍ)
    (c t : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Fin 2 → F) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord (fun i ↦ ((γ • τ : ℍ) : ℂ) + z i * (c * ((γ • τ : ℍ) : ℂ) + t)) (fun i ↦ 1 + z i * c) x i =
      (fun _ ↦ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))⁻¹) i *
      _root_.GlobalTheory.HilbFam.coord
        (fun i ↦ (τ : ℂ) + z i * ((c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) * τ + t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2))
        (fun i ↦ 1 + z i * (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)))
        (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x) i := by
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [_root_.GlobalTheory.HilbFam.coord, _root_.GlobalTheory.HilbFam.JetModular.rowEquiv, LinearEquiv.ofLinear_apply,
    Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add,
    map_mul, map_intCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    specialLinearGroup_apply, coe_mk, eq_intCast]
  set j := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj_def
  have hji : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  rw [div_eq_mul_inv]
  linear_combination (-(((i (x 0) : ℝ) : ℂ) * z i * t + ((i (x 1) : ℝ) : ℂ) * (1 + z i * c))) * hji -
    ((i (x 0) : ℝ) : ℂ) * z i * t * j * j⁻¹ * hdet

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma card_realEmbeddings_eq_finrank (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun φ : F →+* ℝ ↦ Complex.ofRealHom.comp φ) ⟨?_, ?_⟩
  · intro φ ψ h
    ext x
    simpa using congrArg (fun f : F →+* ℂ ↦ f x) h
  · intro ψ
    have hψ : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    exact ⟨hψ.embedding, by ext x; simp [hψ.coe_embedding_apply]⟩


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HilbFam.JetModular.jet_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (c t : ℂ), Even k → _root_.GlobalTheory.HilbFam.jet k L κ ((γ • τ : ℍ) : ℂ) c t = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ (k * Module.finrank ℚ F) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ τ (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) (t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2) := by
  intro F _ _ _ k L κ γ τ c t hk
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← iterD_const_mul]
  congr 1
  funext z
  rw [_root_.GlobalTheory.HilbFam.gval_linear_change F k L (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ) _ _ _ _ (fun _ ↦ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)⁻¹) hk
    (mem_iff_sl2_equiv_mem_mulMat F L γ) (fun _ ↦ inv_ne_zero hj)
    (fun x i ↦ embeddingCoord_sl2_smul_lemma_3 F γ τ c t z x i)]
  rw [Finset.prod_const, Finset.card_univ, card_realEmbeddings_eq_finrank]
  simp only [inv_pow, inv_inv, ← pow_mul, mul_comm (Module.finrank ℚ F) k]
  ring

end GlobalTheory.HilbFam.JetModular
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  first | exact @GlobalTheory.SchwartzDecay.decay_of_mem_schA | exact GlobalTheory.SchwartzDecay.decay_of_mem_schA | (intros; apply GlobalTheory.SchwartzDecay.decay_of_mem_schA <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Classical


theorem _root_.GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type} [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  first | exact @GlobalTheory.SchwartzMajorant.exists_summable_majorant | exact GlobalTheory.SchwartzMajorant.exists_summable_majorant | (intros; apply GlobalTheory.SchwartzMajorant.exists_summable_majorant <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_twoSided_haar | exact GlobalTheory.KSp.map_twoSided_haar | (intros; apply GlobalTheory.KSp.map_twoSided_haar <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_admissibleForm_adelicThetaSum : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ], ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | exact GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | (intros; apply GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]


include fr hc in
theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]


include fr hc in
theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add (f := _), back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]

    simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
      Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end

section

open GlobalTheory.WeilM

theorem _root_.GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  first | exact @GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | exact GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | (intros; apply GlobalTheory.RankStrata.exists_fullRank_sub_mem_span <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  first | (exact @GlobalTheory.EtC.acyclic_of_isTensor) | (exact GlobalTheory.EtC.acyclic_of_isTensor) | (intros; apply GlobalTheory.EtC.acyclic_of_isTensor  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  first | (exact @GlobalTheory.EtC.twist_mul_map) | (exact GlobalTheory.EtC.twist_mul_map) | (intros; apply GlobalTheory.EtC.twist_mul_map  <;> assumption)
end
