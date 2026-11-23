module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle200
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerModularUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle203
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  first | exact @GlobalTheory.EisM.sturm_coef_zero | exact GlobalTheory.EisM.sturm_coef_zero | (intros; apply GlobalTheory.EisM.sturm_coef_zero <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧ (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧ ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  first | exact @GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | exact GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | (intros; apply GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  first | exact @GlobalTheory.EisM.cuspForm_of_CF | exact GlobalTheory.EisM.cuspForm_of_CF | (intros; apply GlobalTheory.EisM.cuspForm_of_CF <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.eichlerShimura_kummer_modularUnit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime] (M n : ℕ) (f : X.Kˣ), 0 < M → l ∣ M → f ∈ X.Un (l ^ n) → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∃ g : X.Kˣ, (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.KZ.ESFun.eichler_shimura_kummer | exact GlobalTheory.KZ.ESFun.eichler_shimura_kummer | (intros; apply GlobalTheory.KZ.ESFun.eichler_shimura_kummer <;> assumption)
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.KernLoc

theorem kern_of (SPAN : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) (ORTH : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt (p := p) (c j)) : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq k N w o hw hwH ho hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hζalg : IsAlgZp p (T.ζ N) := by
    refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos N) 1, ?_⟩
    simp [(T.prim N).pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g (T.ζ N) = T.ζ N := fun g hg => hg (T.ζ N) hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) (T.qq N) = T.ζ N ^ i * T.qq N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, hfixζ _ (Subgroup.pow_mem _ hτ i)]
      ring
  have hτi : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i

  have hτN : (τ ^ (p ^ N)) w = w := by
    apply hwH
    refine ⟨hτi _, ?_⟩
    show (τ ^ (p ^ N)) (T.qq N) = T.qq N
    rw [hτpow, (T.prim N).pow_eq_one, one_mul]

  obtain ⟨z, hz, hze⟩ := hc
  have hzH : ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z := by
    intro g hg
    have hg1 : g ∈ Ggeo p Ω := hg.1
    have hg2 : g (T.qq N) = T.qq N := hg.2
    have hconj : τ⁻¹ * g * τ ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) := by
      refine ⟨(Ggeo p Ω).mul_mem ((Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem hτ) hg1) hτ, ?_⟩
      show (τ⁻¹ * g * τ) (T.qq N) = T.qq N
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq, map_mul, hfixζ g hg1, hg2, ← hτq,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hgτw : g (τ w) = τ w := by
      have := hwH _ hconj
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      have h2 := congrArg τ this
      rwa [← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
    have e := congrArg g hze
    rw [map_sub, map_sub, hgτw, hwH g hg, ho g hg1, map_mul, map_pow, map_natCast, hze] at e
    exact (mul_left_cancel₀ (pow_ne_zero k hp0) e).symm
  obtain ⟨c, hcfix, hzc⟩ := SPAN p Ω hΩ T τ hτ hτq N z hzH

  have hsumz : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) z = (p : Ω) ^ N * c 0 := by
    have h1 : ∀ i j : ℕ, (τ ^ i) (c j * T.qq N ^ j) = c j * T.qq N ^ j * (T.ζ N ^ j) ^ i := by
      intro i j
      rw [map_mul, map_pow, hcfix j _ (hτi i), hτpow]
      ring
    rw [hzc]

    simp_rw [map_sum, h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro j hj hj0
      have hj' := Finset.mem_range.1 hj
      have hne : T.ζ N ^ j ≠ 1 := (T.prim N).pow_ne_one_of_pos_of_lt hj0 hj'
      rw [geom_sum_eq hne, ← pow_mul, mul_comm j, pow_mul, (T.prim N).pow_eq_one, one_pow, sub_self,
        zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (pow_pos (Fact.out : p.Prime).pos N)) h
  have hsumL : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) (τ w - w - o) = -((p : Ω) ^ N * o) := by
    have h1 : ∀ i : ℕ, (τ ^ i) (τ w - w - o) = (τ ^ (i + 1)) w - (τ ^ i) w - o := by
      intro i
      rw [map_sub, map_sub, pow_succ, AlgEquiv.mul_apply, ho _ (hτi i)]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (τ ^ i) w), hτN, pow_zero,
      AlgEquiv.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have key : -((p : Ω) ^ N * o) = (p : Ω) ^ k * ((p : Ω) ^ N * c 0) := by
    rw [← hsumL, ← hsumz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hze, map_mul, map_pow, map_natCast]
  have hc0 : IsInt (p := p) (c 0) := ORTH p Ω hΩ T N c hcfix (hzc ▸ hz) 0 (pow_pos (Fact.out : p.Prime).pos N)
  refine ⟨-c 0, hc0.neg, ?_⟩
  have hpN : (p : Ω) ^ N ≠ 0 := pow_ne_zero N hp0
  apply mul_left_cancel₀ hpN
  linear_combination -key

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 :=
  kern_of GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion

end GlobalTheory.K5.KernLoc
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
    IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
      ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.OrthDecomp.orth | exact GlobalTheory.K5.OrthDecomp.orth | (intros; apply GlobalTheory.K5.OrthDecomp.orth <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  first | exact @GlobalTheory.K5.NotPow.q_not_pow | exact GlobalTheory.K5.NotPow.q_not_pow | (intros; apply GlobalTheory.K5.NotPow.q_not_pow <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.goodTupleProjector_isProj_central : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m : ℕ) (ι : Type) [Fintype ι] (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), (∀ v, IsSeries (τ v)) → IsProj (eGood τ ch) ∧ ∀ a, conv (eGood τ ch) a = conv a (eGood τ ch) := by
  first | exact @GlobalTheory.BadShare.eGood_isProj_central | exact GlobalTheory.BadShare.eGood_isProj_central | (intros; apply GlobalTheory.BadShare.eGood_isProj_central <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.series_representation_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  first | exact @GlobalTheory.BadShare.series_weight_lower_bound | exact GlobalTheory.BadShare.series_weight_lower_bound | (intros; apply GlobalTheory.BadShare.series_weight_lower_bound <;> assumption)
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.StabGal
theorem klm_sl_gal_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l M : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (d : ℤ) (γ γ'' : SL(2, ℤ)), 0 < M → IsPrimitiveRoot ζ M → s ζ = ζ ^ d → ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → ∀ y ∈ X.Lev l M, X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) = X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y) := by
  intro Ω _ _ ε X l M _ s ζ d γ γ'' hM hζ hsd hcong y hy
  refine Submodule.span_induction (p := fun y _ => X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) =
      X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨f, hf, rfl⟩
    have hr := X.recip M (f : X.K) hM hf ζ hζ s d hsd γ'' γ hcong
    simp only [Tower.klm, LinearMap.baseChange_tmul]
    congr 1
    apply Additive.toMul.injective
    apply Units.ext
    simp [hr]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro a x _ hx; simp [hx]

theorem galB_mem_Pol : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω), (∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.galB l s b ∈ X.Pol l w := by
  intro Ω _ _ ε X l w _ s hA b hb
  obtain ⟨c, hcA, hc⟩ := hb
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => Submodule.smul_mem _ _ (hA _ (hcA i)), fun u => ?_⟩
  show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
  rw [hc]

  simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem eval_Pol_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ n : ℕ, ∃ y : Fin (w + 1) → X.Kl l, ∀ x : Fin 2 → ℤ_[l], ∃ Y ∈ Submodule.span ℤ_[l] (Set.range y), AdicCompletion.eval (idl l) (X.Kl l) n (b x) = Submodule.Quotient.mk Y := by
  intro Ω _ _ ε X l w _ b hb n
  obtain ⟨c, _, hc⟩ := hb
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  refine ⟨y, fun x => ⟨∑ i : Fin (w + 1), (x 0 ^ (i : ℕ) * x 1 ^ (w - (i : ℕ))) • y i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩⟩

  rw [hc, map_sum]
  simp only [map_smul]
  change _ = Submodule.mkQ _ _

  rw [map_sum]
  simp only [map_smul, Submodule.mkQ_apply, hy]

theorem eval_Pol_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) → AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by
  intro Ω _ _ ε X l w _ b hb n u v huv
  obtain ⟨c, _, hc⟩ := hb

  rw [← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  have hmem : (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ)) - v 0 ^ (i : ℕ) * v 1 ^ (w - (i : ℕ))) ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow,
      map_pow, map_pow, map_pow, huv 0, huv 1, sub_self]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hmem Submodule.mem_top

theorem twist_congr : ∀ (l n M : ℕ) [Fact l.Prime], l ^ n ∣ M → ∀ (γ γ'' : SL(2, ℤ)) (d : ℤ) (χ : ℤ_[l]), ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → (d : ZMod (l ^ n)) = PadicInt.toZModPow n χ → ∀ (u : Fin 2 → ℤ_[l]) (i : Fin 2), PadicInt.toZModPow n ((![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] : Fin 2 → ℤ_[l]) i) = PadicInt.toZModPow n ((mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i) := by
  intro l n M _ hlnM γ γ'' d χ hc hd u i
  obtain ⟨h00, h01, h10, h11⟩ := hc
  have cast : ∀ k : ℤ, ZMod.castHom hlnM (ZMod (l ^ n)) (k : ZMod M) = (k : ZMod (l ^ n)) := fun k => map_intCast _ k
  have e00 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h00
  have e01 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h01
  have e10 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h10
  have e11 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h11
  simp only [map_mul, cast] at e00 e01 e10 e11
  simp only [en] at e00 e01 e10 e11
  rw [hd] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dite_eq_left h]
  ext i j
  simp [ofSL]

theorem inv_galB {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s b := by
  obtain ⟨hpol, hinv⟩ := hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := eval_Pol_rep X l w b hpol n
  obtain ⟨M, hM, hdiv, hlev⟩ := GlobalTheory.T.exists_common_level_span_multiple X l (N * l * l ^ n) y
    (Nat.mul_pos (Nat.mul_pos hN (Nat.Prime.pos Fact.out)) (pow_pos (Nat.Prime.pos Fact.out) n))
  have hNM : N ∣ M := Dvd.dvd.trans ⟨l * l ^ n, by ring⟩ hdiv
  have hlM : l ∣ M := Dvd.dvd.trans ⟨N * l ^ n, by ring⟩ hdiv
  have hlnM : l ^ n ∣ M := Dvd.dvd.trans ⟨N * l, by ring⟩ hdiv
  obtain ⟨γ'', hγ'', ζ, hζ, d, hsd, hcong, hdχ⟩ := GlobalTheory.T.exists_conj_level_elem_exponent_shimura (Ω := Ω) N l n M hM hNM hlM hlnM s γ hγ
  have hspan : Submodule.span ℤ_[l] (Set.range y) ≤ X.Lev l M :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hlev i)
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := ![u 0, χ * u 1] with hv
  have h1 := eval_Pol_congr X l w b hpol n _ _ (twist_congr l n M hlnM γ γ'' d χ hcong hdχ u)
  obtain ⟨Y, hY, hYe⟩ := hy (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v)
  have hinv' : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) b v) =
      AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by rw [hinv γ'' hγ'']
  have hc := klm_sl_gal_comm X l M s ζ d γ γ'' hM hζ hsd hcong Y (hspan hY)
  show (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s) (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))).val n =
    (X.kmap l (X.gal s) (b v)).val n
  rw [toGQ_SL]
  change (X.klm l (X.sl (ofSL γ)).toRingEquiv).reduceModIdeal ((idl l)^n)
      ((X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b _))) =
    (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b v))
  rw [h1, hYe, ← hinv']
  change _ = (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n)
    ((X.klm l (X.sl (toGQ (γ'' : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv).reduceModIdeal ((idl l)^n)
      (AdicCompletion.eval (idl l) (X.Kl l) n (b (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v))))
  rw [toGQ_SL, hYe]
  simp only [LinearMap.reduceModIdeal_apply]
  rw [hc]

theorem galB_mem_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  intro Ω _ _ _ ε X hε hj N l w _ _ hN _ _ s b hb
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X hε hj l).2 s
  have hN0 : 0 < N := by omega
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨galB_mem_Pol X l w s hA c hc.1, fun γ hγ => inv_galB X N l w hN0 s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

end GlobalTheory.KZ.StabGal
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_highestWeight_vector_of_KStable : ∀ (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V), FiniteDimensional ℂ W → KStable M.act W → W ≠ ⊥ → ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  first | exact @GlobalTheory.ExistsHW.exists_highestWeight | exact GlobalTheory.ExistsHW.exists_highestWeight | (intros; apply GlobalTheory.ExistsHW.exists_highestWeight <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  first | exact @GlobalTheory.ExtremalGen.exists_generated | exact GlobalTheory.ExtremalGen.exists_generated | (intros; apply GlobalTheory.ExtremalGen.exists_generated <;> assumption)
end
