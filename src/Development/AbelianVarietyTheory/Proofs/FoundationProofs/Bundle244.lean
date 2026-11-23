module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle180
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle179
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNonzeroThetaOfFiniteLevelAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.InnerProductSpace.Dual
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_eq_of_smul_mk_eq_zero {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (s : integralClosure (O0 p) Ω) (ω : Ω)
    (h : s • (Submodule.Quotient.mk ω : Frac p Ω) = 0) :
    ∃ t : integralClosure (O0 p) Ω, (t : Ω) = (s : Ω) * ω := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simpa [Algebra.smul_def] using ht⟩

theorem dlog_indep_pow_three : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n →
    ∀ x y zi qi : (integralClosure (O0 p) Ω), zS T n * zi = 1 → qS T n * qi = 1 →
    (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) +
      (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = 0 →
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * x = (p : (integralClosure (O0 p) Ω)) ^ (n - 1) * t) ∧
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * y = (p : (integralClosure (O0 p) Ω)) ^ n * t) := by
  intro p _ Ω _ _ hp2 hclo T n hn x y zi qi hz hq hrel
  have hpΩ : (p : Ω) ≠ 0 := by
    haveI := GlobalTheory.K5.Basic.charZero_of_isClo hclo
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrel' : ∑ i, (![x * zi, y * qi] : Fin 2 → integralClosure (O0 p) Ω) i •
      KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)
        ((![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i) = 0 := by
    simpa [Fin.sum_univ_two] using hrel
  obtain ⟨F, hF⟩ := GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra (O0 p) (integralClosure (O0 p) Ω) 2 _ _ hrel'
  obtain ⟨C, tr, m, a, b, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T F
  have hzT : zS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hqT : qS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  have hyC : ∀ i, (![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i ∈ C := by
    intro i; fin_cases i
    · exact htr.le hzT
    · exact htr.le hqT
  have hzΩ : T.ζ n * (zi : Ω) = 1 := by
    have := congrArg Subtype.val hz; simpa [zS] using this
  have hqΩ : T.qq n * (qi : Ω) = 1 := by
    have := congrArg Subtype.val hq; simpa [qS] using this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  constructor
  · obtain ⟨Dz, hDz, hDzv⟩ := GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dz hDz
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDzv (k + 1)).1, (hDzv (k + 1)).2, smul_zero, smul_zero,
      add_zero, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-((x : Ω) * (p : Ω) ^ (k + 1))) * hzΩ
  · obtain ⟨Dq, hDq, hDqv⟩ := GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dq hDq
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDqv (k + 1)).1, (hDqv (k + 1)).2, smul_zero, smul_zero,
      zero_add, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-(y : Ω)) * hqΩ

end GlobalTheory.AlmostEt
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisPer

theorem per_val {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (n : ℤ) :
    a n = a (((n : ZMod N).val : ℕ) : ℤ) := by
  have hp : Function.Periodic a (N : ℤ) := ha
  rw [ZMod.val_intCast]
  have := hp.int_mul (n / N) (n % N)
  simp only [Int.cast_id] at this
  rw [← this]
  congr 1
  have := Int.mul_ediv_add_emod n N
  linarith [mul_comm (N : ℤ) (n / N)]

theorem sum_range_zmod {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ y ∈ Finset.range N, g (y : ZMod N) = ∑ z : ZMod N, g z := by
  refine Finset.sum_bij' (fun y _ => (y : ZMod N)) (fun z _ => z.val) (by simp)
    (fun z _ => by simpa using ZMod.val_lt z) (fun y hy => ZMod.val_cast_of_lt (Finset.mem_range.1 hy))
    (fun z _ => ZMod.natCast_zmod_val z) (fun _ _ => rfl)

def invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (y : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y))

theorem hat_invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) :
    hat (invF (N := N) a) d = a d := by
  unfold hat
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have e1 : ∀ y : ℕ, cexp (2 * π * Complex.I * (y * d) / N) = ZMod.stdAddChar ((y : ZMod N) * (d : ZMod N)) := by
    intro y
    have := ZMod.stdAddChar_coe (N := N) ((y : ℤ) * d)
    push_cast at this
    rw [← this]
  simp_rw [e1]
  rw [sum_range_zmod (fun z => invF a z * ZMod.stdAddChar (z * (d : ZMod N)))]
  unfold invF
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ x y : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (y * (d : ZMod N))
      = a (x.val : ℤ) * ZMod.stdAddChar (y * ((d : ZMod N) - x)) := by
    intro x y
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp_rw [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (d : ZMod N) (fun x => a (x.val : ℤ) * (N : ℂ))]
  simp only [Finset.mem_univ, if_true]
  rw [← per_val a ha d]
  field_simp

theorem invF_twist {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) (c : ℂ)
    (hd : IsCoprime d (N : ℤ)) (hmul : ∀ x, a (x * d) = c * a x) (y : ZMod N) :
    invF (N := N) a y = c * invF (N := N) a (y * (d : ZMod N)) := by
  obtain ⟨u, v, huv⟩ := hd
  have hu : (u : ZMod N) * (d : ZMod N) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) huv
    simpa using this
  let U : (ZMod N)ˣ := ⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact hu, hu⟩
  unfold invF
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ x : ZMod N, c * ((N : ℂ)⁻¹ * (a (x.val : ℤ) * ZMod.stdAddChar (-(x * (y * (d : ZMod N))))))
      = (N : ℂ)⁻¹ * (a ((x * (d : ZMod N)).val : ℤ) * ZMod.stdAddChar (-((x * (d : ZMod N)) * y))) := by
    intro x
    have h1 : a ((x * (d : ZMod N)).val : ℤ) = c * a (x.val : ℤ) := by
      rw [← hmul, per_val a ha ((x.val : ℤ) * d)]
      congr 3
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h2 : -(x * (y * (d : ZMod N))) = -((x * (d : ZMod N)) * y) := by ring
    rw [h2]; ring
  exact (Fintype.sum_equiv (Units.mulRight U) _ _ e).symm

end GlobalTheory.EisPer

end

open GlobalTheory.EisPer in
theorem GlobalTheory.eis_periodic_weights : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  intro j L₁ L₂ a b χ₁ χ₂ hj hL₁ hL₂ ha0 ha hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hhat : hat (invF (N := L₁) a) = a := funext (hat_invF a ha)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq j L₁ L₂ b χ₁ χ₂ (invF (N := L₁) a) hj hL₁ hL₂
    (by rw [hhat]; exact ha0) hb
    (fun d hd => ⟨fun y => invF_twist a ha d (χ₁ d)
      (by
        have : IsCoprime d ((L₁ : ℤ) * (L₂ : ℤ)) := by exact_mod_cast hd
        exact this.of_mul_right_left) (hχ d hd).1 y, (hχ d hd).2⟩) hpar
  exact ⟨c, by rw [hhat] at hc; exact hc⟩
end

section

open GlobalTheory.DualWeyl MvPolynomial NumberField MeasureTheory
open scoped Matrix ComplexConjugate InnerProductSpace

namespace GlobalTheory.DualWeyl.Repro

variable {N : ℕ} {la : Fin N → ℕ}

theorem exists_repr (la : Fin N → ℕ) :
    ∃ k : nabla la ℂ, ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1 := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  refine ⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm
    (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩
  rw [← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

theorem form_rhoU_repr {k : nabla la ℂ} (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1)
    (u : UN N) (f : nabla la ℂ) :
    form la f.1 (rhoU la u⁻¹ k : Pol N ℂ) = evalAt u.1ᵀ f.1 := by
  rw [← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]

theorem normSq_repr (hla : Antitone la) {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) : normSq la k.1 = 1 := by
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  have h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1 := by
    intro g
    let u : UN N := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
    rw [← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he, inner_toSpace, form_rhoU_repr hk]
    rfl
  have h2 : ∑ i, normSq la (e i).1 = dim la := by
    simp only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]
    simp [dim_eq_card]
  have h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1 := by
    conv_lhs => simp only [normSq]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]
    simp only [h1]
    simp
  have hd : (dim la : ℝ) ≠ 0 := by exact_mod_cast (dim_pos hla).ne'
  exact mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])

theorem rowAct_diagonal_repr {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) (t : Fin N → ℂ) (ht : ∀ a, ‖t a‖ = 1) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) k.1 = (∏ a, t a ^ la a) • k.1 := by
  have hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [Complex.mul_conj', ht]
  let u : UN N := ⟨_, hu⟩
  have hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t) := by
    change (star (Matrix.diagonal t))ᵀ = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]
  have h : rhoU la u k = (∏ a, t a ^ la a) • k := by
    apply (toSpace la).injective
    refine ext_inner_right ℂ fun v => ?_
    obtain ⟨f, rfl⟩ := (toSpace la).surjective v
    rw [inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right,
      hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct,
      colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]
    simp [diagChar]
  have h' := congrArg Subtype.val h
  rwa [rhoU_apply, coe_rho, Matrix.diagonal_transpose] at h'

theorem isWeightedHomogeneous_of_torus {f : Pol N ℂ}
    (h : ∀ t : Fin N → ℂ, (∀ a, ‖t a‖ = 1) →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) f = (∏ a, t a ^ la a) • f) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la := by
  classical
  intro m hm
  funext a
  rw [Formalism.GradedWeylDivisibility.ldrow_weight_rowW]
  have hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0 := by omega
  have hz := Complex.isPrimitiveRoot_exp _ hn
  have hz1 := hz.norm'_eq_one hn
  generalize Complex.exp _ = z at hz hz1
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) (h (Function.update 1 a z) fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hz1
    · simp [Function.update_of_ne hb])
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a := by
    intro d
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [h3, h3] at h2
  exact hz.pow_inj (by omega) (by omega) h2

theorem extremal_reproducing : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la →
    (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  intro N la hla
  obtain ⟨k, hk⟩ := exists_repr la
  have h1 := normSq_repr hla hk
  have h2 : evalAt 1 k.1 = 1 := by rw [← hk, form_self, h1, Complex.ofReal_one]
  have h3 := GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))
  rw [h2, one_smul] at h3
  rw [← h3]
  exact ⟨fun f hf => hk ⟨f, hf⟩, h1⟩

end GlobalTheory.DualWeyl.Repro
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.GeoLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

def ggens (T : Tower p Ω) (N : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x} ∪ T.qq '' Set.Iic N

theorem ggens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : ggens T m ⊆ ggens T n := by
  unfold ggens
  gcongr

theorem fixes_ggens (T : Tower p Ω) (N : ℕ) (g : Gal p Ω)
    (hg : g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N)) :
    ∀ a ∈ ggens T N, g a = a := by
  have hgeo : ∀ x : Ω, IsAlgZp p x → g x = x := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq N) = T.qq N := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · exact hgeo a ha
  · have hi' : i + (N - i) = N := Nat.add_sub_cancel' hi
    rw [GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h y = y) :
    ∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y := by
  haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, ggens T n)
  have hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a := fun a ha => f.commutes ⟨a, hmemL a ha⟩
      have hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
        refine Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩),
          Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
        · exact hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)
        · exact hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ ggens T (S.sup m) := fun t ht =>
    ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.GeoLevel

theorem GlobalTheory.K5.geo_invariants_from_finite_level :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt (p := p) x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (g x) x) →
  ∃ y : Ω, IsInt (p := p) y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong (p := p) k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi : ∀ (g : Gal p Ω) (z : Ω), IsInt (p := p) z → IsInt (p := p) (g z) := fun g z hz =>
    hz.map (g : Ω →ₐ[O0 p] Ω)
  refine ⟨∑ g ∈ E, g (y₀ * x), ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun g _ => hgi g _ (hy₀.mul hx)
  · exact GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
      (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  · have hz : ∀ g ∈ E, ∃ z : Ω, IsInt (p := p) z ∧ g x - x = (p : Ω) ^ k * z :=
      fun g hg => hfix g (hEH g hg)
    choose! z hzi hzx using hz
    refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
    · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
    · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_mul]
      linear_combination (-(g y₀)) * hzx g hg
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_nonzero_theta_of_finite_level_average : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), A.FG → (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → x ∈ A) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) → ∀ F : VC D N N' → ℂ, Differentiable ℂ F → F ≠ 0 → ∀ n : ℕ, 0 < n → (∀ x ∈ A, U D T (n • x) F = F) → ∃ P, IsTr D T A F P ∧ P ∈ ThSp D T A ∧ P ≠ 0 := by
  first | exact @GlobalTheory.GalTheta.exists_theta_of_level | exact GlobalTheory.GalTheta.exists_theta_of_level | (intros; apply GlobalTheory.GalTheta.exists_theta_of_level <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

theorem _root_.GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings : ∀ (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  first | exact @GlobalTheory.TwoSidedDet.det_mulV | exact GlobalTheory.TwoSidedDet.det_mulV | (intros; apply GlobalTheory.TwoSidedDet.det_mulV <;> assumption)
end
