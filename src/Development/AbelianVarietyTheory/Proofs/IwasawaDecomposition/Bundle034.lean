module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Normed.Field.Instances
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section


theorem _root_.GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges : ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible → ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}, f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) → GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  first | exact @GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | exact GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | (intros; apply GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs : ∀ (p q : ℕ), cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  first | exact @GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | exact GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | (intros; apply GlobalTheory.CayleyBlock.cayOp_pow_eq_sum <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem hasDerivAt_line_dH {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by
  have e : (fun t : ℝ => ρ (t • v) f) = fun t : ℝ => ρ (s • v) (ρ ((t - s) • v) f) := by
    funext t
    rw [h.2.1, ← add_smul]
    simp [h0]
  have h1 : HasDerivAt (fun t : ℝ => ρ ((t - s) • v) f) (dH ρ v f) s := by
    have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) f) (dH ρ v f) (s - s) := by
      rw [sub_self]; exact hasDerivAt_dH v hf
    exact h2.comp_sub_const s s
  rw [e]
  exact ((ρ (s • v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1

theorem dH_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (F : Y → B), (∀ y, Sm ρ (F y)) → Integrable F ν → Sm ρ (∫ y, F y ∂ν) → ∀ v, Integrable (fun y => dH ρ v (F y)) ν → dH ρ v (∫ y, F y ∂ν) = ∫ y, dH ρ v (F y) ∂ν := by
  intro V _ _ B _ _ _ om ρ h0 h Y _ ν F hF hFi hS v hd
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) y => ρ (t • v) (F y)) (F' := fun (t : ℝ) y => ρ (t • v) (dH ρ v (F y)))
    (bound := fun y => ‖dH ρ v (F y)‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => ((ρ (t • v)).integrable_comp hFi).aestronglyMeasurable)
    ((ρ _).integrable_comp hFi) ((ρ _).integrable_comp hd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y t _ => (h.2.2.1 _ _).le) hd.norm
    (Filter.Eventually.of_forall fun y t _ => hasDerivAt_line_dH om h0 h v (hF y) t)).2
  simp only [zero_smul, h.1, ContinuousLinearMap.integral_comp_comm _ hFi] at key
  exact (hasDerivAt_dH v hS).unique key

end GlobalTheory.Mem.Lift
end

section

open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Lift

theorem IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by
  obtain ⟨hx, hd, hc⟩ := h
  have e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l') := by
    noncomm_ring
  have e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l) := by
    noncomm_ring
  rw [e1, e2, hc, hc, hx k' k, hd l' l]
  split_ifs <;> simp

theorem glRel_of_isCCR (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]

end GlobalTheory.Mem.Lift
end

section

noncomputable section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

namespace GlobalTheory.CompactHowe.PolyTensor

open MvPolynomial

variable {ι σ : Type} [Fintype ι]

def prodRename [DecidableEq ι] :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    fun i => (rename (Prod.mk i) : MvPolynomial σ ℂ →ₐ[ℂ] _).toLinearMap

theorem prodRename_apply [DecidableEq ι] (P : ι → MvPolynomial σ ℂ) :
    prodRename P = ∏ i, rename (Prod.mk i) (P i) := by
  simp [prodRename]

theorem sum_mapDomain_apply (a : ι → σ →₀ ℕ) (j : ι) (s : σ) :
    (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) (j, s) = a j s := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Prod.fst ht)
  · simp

theorem prod_rename_monomial (a : ι → σ →₀ ℕ) :
    (∏ i, rename (Prod.mk i) (monomial (a i) (1 : ℂ)) : MvPolynomial (ι × σ) ℂ)
      = monomial (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

def res (α : ι × σ →₀ ℕ) (i : ι) : σ →₀ ℕ :=
  Finsupp.comapDomain (Prod.mk i) α (Prod.mk_right_injective i).injOn

theorem res_sum (a : ι → σ →₀ ℕ) : res (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) = a := by
  funext j
  ext s
  exact sum_mapDomain_apply a j s

theorem sum_res (α : ι × σ →₀ ℕ) : ∑ i, Finsupp.mapDomain (Prod.mk i) (res α i) = α := by
  ext ⟨j, s⟩
  exact sum_mapDomain_apply (res α) j s

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial (ι × σ) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials (ι × σ) ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ι → MvPolynomial σ ℂ) :
    tens I (∏ i, rename (Prod.mk i) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  have key : (tens I).compMultilinearMap prodRename
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun _ => basisMonomials σ ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, prodRename_apply, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply]
    rw [prod_rename_monomial]
    have := (basisMonomials (ι × σ) ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1))
      (∑ i, Finsupp.mapDomain (Prod.mk i) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [prodRename_apply] using this

omit [Fintype ι] in
theorem tprod_ne_zero [Finite ι] (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) :
    PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

omit [Fintype ι] in
theorem substF_rename {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (i : ι) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    substF h g (rename (Prod.mk i) P) = rename (Prod.mk i) (subst2 (h i) (g i) P) := by
  have key : (substF h g).comp (rename (Prod.mk i)) = (rename (Prod.mk i)).comp (subst2 (h i) (g i)) := by
    refine algHom_ext fun p => ?_

    simp only [AlgHom.comp_apply, rename_X, substF_X, subst2_X, map_sum, map_mul, rename_C]
  exact congrArg (fun f => f P) key

theorem exists_tensor : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  intro ι _ N n A B _ _ _ _ I hI
  classical
  refine ⟨tens I, ?_, ?_⟩
  · have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
      intro i
      by_contra hc
      push Not at hc
      exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
    choose P v hPv using hex
    intro h0
    have h1 := tens_prod I P
    rw [h0] at h1
    have h2 := congrArg (fun f => f (PiTensorProduct.tprod ℂ v)) h1
    simp only [LinearMap.zero_apply, PiTensorProduct.map_tprod] at h2
    exact tprod_ne_zero _ hPv h2.symm
  · intro c h g a b hab
    have key : ∀ Q : ι → MvPolynomial (Fin N × Fin n) ℂ,
        (tens I ((∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i)))) ∘ₗ PiTensorProduct.map a
          = PiTensorProduct.map b ∘ₗ tens I (∏ i, rename (Prod.mk i) (Q i)) := by
      intro Q
      have e : (∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i))
          = ∏ i, rename (Prod.mk i) (c i • subst2 (h i) (g i) (Q i)) := by
        simp only [map_prod, substF_rename, map_smul, Finset.prod_smul]
      rw [e, tens_prod, tens_prod, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      exact LinearMap.ext fun v => hab i (Q i) v
    intro P x
    induction P using MvPolynomial.induction_on' with
    | monomial α r =>
      have e : (monomial α r : MvPolynomial (ι × Fin N × Fin n) ℂ)
          = r • ∏ i, rename (Prod.mk i) (monomial (res α i) (1 : ℂ)) := by
        rw [prod_rename_monomial, sum_res, smul_monomial, smul_eq_mul, mul_one]
      have := congrArg (fun f => f x) (key fun i => monomial (res α i) 1)
      simp only [LinearMap.comp_apply] at this
      rw [e, map_smul (substF h g), smul_comm, map_smul (tens I), LinearMap.smul_apply, this, map_smul (tens I),
        LinearMap.smul_apply, map_smul]
    | add p q hp hq =>
      rw [map_add (f := _), smul_add, map_add (f := _), LinearMap.add_apply, hp, hq, map_add (tens I),
        LinearMap.add_apply, map_add]

end GlobalTheory.CompactHowe.PolyTensor

end
end

section

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.CompactHowe.Minors

variable {N n : ℕ}

def IsBorelVec (hn : n ≤ N) (ν : Fin N → ℕ) (Δ : MvPolynomial (Fin N × Fin n) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, j < i → h i j = 0) → (∀ i j, j < i → g i j = 0) →
      subst2 h g Δ = ((∏ b, h b b ^ ν b) * ∏ a, g a a ^ ν (Fin.castLE hn a)) • Δ

theorem isBorelVec_one (hn : n ≤ N) : IsBorelVec hn (fun _ => 0) 1 :=
  ⟨one_ne_zero, fun h g _ _ => by simp⟩

theorem IsBorelVec.mul {hn : n ≤ N} {ν μ : Fin N → ℕ} {Δ Γ : MvPolynomial (Fin N × Fin n) ℂ}
    (h1 : IsBorelVec hn ν Δ) (h2 : IsBorelVec hn μ Γ) : IsBorelVec hn (fun b => ν b + μ b) (Δ * Γ) := by
  refine ⟨mul_ne_zero h1.1 h2.1, fun h g hh hg => ?_⟩
  rw [map_mul, h1.2 h g hh hg, h2.2 h g hh hg, smul_mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

theorem not_range_castLE {k m : ℕ} (hk : k ≤ m) (i : Fin m) (hi : i ∉ Set.range (Fin.castLE hk)) : k ≤ (i : ℕ) := by
  by_contra hc
  exact hi ⟨⟨i, by omega⟩, Fin.ext rfl⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hk : k ≤ m) (f : Fin m → M)
    (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) : ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hk i) :=
  (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ f
    (fun i hi => hf i (not_range_castLE hk i hi)) fun _ => rfl).symm

theorem prod_pow_ite {k m : ℕ} (hk : k ≤ m) (c : Fin m → ℂ) :
    ∏ i, c i ^ (if (i : ℕ) < k then 1 else 0) = ∏ i : Fin k, c (Fin.castLE hk i) :=
  (Fintype.prod_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun i hi => by rw [if_neg (not_lt.2 (not_range_castLE hk i hi)), pow_zero])
    fun i => by simp).symm

def block (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N × Fin n) ℂ) :=
  Matrix.of fun i j => X (Fin.castLE (hk.trans hn) i, Fin.castLE hk j)

theorem det_block_ne_zero (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : (block hn hk).det ≠ 0 := by
  intro h0
  have h1 := (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).map_det (block hn hk)
  have h2 : (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).mapMatrix (block hn hk) = 1 := by
    ext i j
    simp [block, Matrix.one_apply, Fin.ext_iff]
  rw [h2, h0] at h1
  simp at h1

theorem det_lead {k m : ℕ} (hk : k ≤ m) (g : Matrix (Fin m) (Fin m) ℂ) (hg : ∀ i j, j < i → g i j = 0) :
    (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = ∏ i : Fin k, g (Fin.castLE hk i) (Fin.castLE hk i) := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hg _ _ hij

theorem isBorelVec_det (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) :
    IsBorelVec hn (fun b => if (b : ℕ) < k then 1 else 0) (block hn hk).det := by
  refine ⟨det_block_ne_zero hn hk, fun h g hh hg => ?_⟩
  have key : (subst2 h g).mapMatrix (block hn hk) =
      ((C : ℂ →+* _).mapMatrix (h.submatrix (Fin.castLE (hk.trans hn)) (Fin.castLE (hk.trans hn))))ᵀ * block hn hk *
        (C : ℂ →+* _).mapMatrix (g.submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
    ext1 i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, block, Matrix.of_apply, subst2_X, Matrix.mul_apply,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.submatrix_apply, Finset.sum_mul]
    rw [sum_castLE (hk.trans hn), Finset.sum_comm]
    · rw [sum_castLE hk]
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul]; ring
      · intro l hl
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [hg l _ (by rw [Fin.lt_def]; have := j.2; simp only [Fin.val_castLE]; omega)]
        simp
    · intro l hl
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [hh l _ (by rw [Fin.lt_def]; have := i.2; simp only [Fin.val_castLE]; omega)]
      simp
  rw [AlgHom.map_det, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det,
    det_lead _ _ hh, det_lead _ _ hg, prod_pow_ite (hk.trans hn) (fun b => h b b)]
  simp only [Fin.val_castLE]
  rw [prod_pow_ite hk (fun b => g b b), smul_eq_C_mul, map_mul]
  ring

theorem exists_isBorelVec (hn : n ≤ N) (M : ℕ) : ∀ ν : Fin N → ℕ, (∀ b, ν b ≤ M) → Antitone ν →
    (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ, IsBorelVec hn ν Δ := by
  classical
  induction M with
  | zero =>
    intro ν hM _ _
    obtain rfl : ν = fun _ => 0 := funext fun b => Nat.le_zero.1 (hM b)
    exact ⟨1, isBorelVec_one hn⟩
  | succ M ih =>
    intro ν hM ha h0
    obtain ⟨Γ, hΓ⟩ := ih (fun b => ν b - 1) (fun b => by have := hM b; omega)
      (fun a b hab => Nat.sub_le_sub_right (ha hab) 1) (fun b hb => by simp [h0 b hb])
    have hex : ∃ k : ℕ, ∀ b : Fin N, k ≤ (b : ℕ) → ν b = 0 := ⟨n, h0⟩
    have hk : Nat.find hex ≤ n := Nat.find_min' hex h0
    refine ⟨(block hn hk).det * Γ, ?_⟩
    have := (isBorelVec_det hn hk).mul hΓ
    convert this using 2 with b
    split_ifs with hb
    · have h1 := Nat.find_min hex hb
      push Not at h1
      obtain ⟨c, hc, hc0⟩ := h1
      have : ν c ≤ ν b := ha (Fin.le_def.2 hc)
      omega
    · have := Nat.find_spec hex b (not_lt.1 hb)
      omega

theorem exists_highestWeight (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (ha : Antitone ν)
    (h0 : ∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) :
    ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧
      (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧
      ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ =
        ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  obtain ⟨Δ, h1, h2⟩ := exists_isBorelVec hn (∑ b, ν b) ν
    (fun b => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)) ha h0
  refine ⟨Δ, h1, fun h g hh hg => ?_, fun d e => ?_⟩
  · rw [h2 h g hh.2 hg.2]
    simp [hh.1, hg.1]
  · rw [h2 _ _ (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne') (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne')]
    simp

end GlobalTheory.CompactHowe.Minors

end
end

section

namespace GlobalTheory.RingHomOfIsIntegral

theorem exists_ringHom_of_isIntegral (R : Type) [CommRing R] [CharZero R] [Algebra.IsIntegral ℤ R]
    (l : ℕ) [hl : Fact (Nat.Prime l)] : Nonempty (R →+* AlgebraicClosure (ZMod l)) := by
  have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
  have hlp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R)
    (Ideal.span {(l : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [hinj (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  have := hP
  have hl0 : ((l : ℕ) : R ⧸ P) = 0 := by
    have h1 : (l : ℤ) ∈ P.comap (algebraMap ℤ R) := by
      change (l : ℤ) ∈ Ideal.under ℤ P
      rw [hPc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1
  have hchar : CharP (R ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  let : Algebra (ZMod l) (R ⧸ P) := ZMod.algebra _ l
  have : Algebra.IsIntegral (ZMod l) (R ⧸ P) := ⟨fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ) r).map (Ideal.Quotient.mkₐ ℤ P)).tower_top⟩
  exact ⟨(IsAlgClosed.lift (R := ZMod l) (S := R ⧸ P)
    (M := AlgebraicClosure (ZMod l))).toRingHom.comp (Ideal.Quotient.mk P)⟩

theorem nonempty_ringHom : ∀ (l : ℕ) [Fact (Nat.Prime l)],
    Nonempty (↥(integralClosure ℤ ℂ) →+* Formalism.CyclotomicNorms.Fbar l) := by
  intro l _
  exact exists_ringHom_of_isIntegral (integralClosure ℤ ℂ) l

end GlobalTheory.RingHomOfIsIntegral
end

section

open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ)
    (Φ : MvPolynomial (T × Fin N × Fin N) ℂ_[p]),
    ((fun y => (∏ τ, (y τ).det ^ k τ) * polFun Φ y) ∈ WeylLatticeDuality.DelW p T N (fun τ r => ν τ r + k τ) ↔
      polFun Φ ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | exact GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | (intros; apply GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff <;> assumption)
end
