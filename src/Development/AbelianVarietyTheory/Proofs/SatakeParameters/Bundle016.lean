module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import ReciprocityTheory.Automorphisms.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.HkFin

theorem exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨a, ha0, ha, -⟩ := PI.FinOrdValD.WA.weakApprox (insert w S)
    (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E))
    (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ))))
    (fun v _ => by
      by_cases h : v = w
      · subst h; simp only [Function.update_self]
        exact mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero
      · simp only [Function.update_of_ne h]; exact exp_ne_zero)
  refine ⟨a, ha0, ?_, fun v hv hvw => ?_⟩
  · have h := ha w (Finset.mem_insert_self w S)
    simp only [Function.update_self] at h
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 =
        (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv]; rfl
    rw [e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_comm] at h
    exact (mul_inv_lt_of_lt_mul₀ h).le
  · have h := ha v (Finset.mem_insert_of_mem hv)
    simp only [Function.update_of_ne hvw] at h
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h.le

end GlobalTheory.HkFin
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.norm_tensorProduct_map_id_right : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  first | exact @GlobalTheory.norm_tensorProduct_map_left | exact GlobalTheory.norm_tensorProduct_map_left | (intros; apply GlobalTheory.norm_tensorProduct_map_left <;> assumption)
end

section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem tensor_exists_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_eq_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _)] at h0 h1
  exact ⟨h0, h1⟩

theorem mem_ALint_of_supported_at_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L),
    Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 →
    ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) →
    Valued.v (s.proj (L := L) z) ≤ 1 →
    Valued.v (s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 →
    z ∈ ReciprocityTheory.Aut.ALint L := by
  intro L _ _ _ s e he hc z hz hp hq
  have hne : (e : L) ≠ IsCMField.complexConj L (e : L) := by
    intro h
    rw [← h, he] at hc
    exact lt_irrefl _ hc
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = (e : L) := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0 := by
    intro w hw
    have h := hz w hw
    rw [hAB] at h
    apply tensor_decomp_eq_zero b
    rw [hb0, hb1]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have h1 : s.proj (L := L) z = A s.v + s.i (e : L) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]
  have hBv : Valued.v (B s.v) ≤ 1 := by
    have hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v =
        s.proj (L := L) z - s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    have hv := congrArg Valued.v hm
    rw [map_mul, hu, one_mul] at hv
    rw [hv]
    exact Valuation.map_sub_le _ hp hq
  have hAv : Valued.v (A s.v) ≤ 1 := by
    have hm : A s.v = s.proj (L := L) z - s.i (e : L) * B s.v := by rw [h1]; ring
    rw [hm]
    refine Valuation.map_sub_le _ hp ?_
    rw [map_mul, he, one_mul]
    exact hBv
  have hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hAv
    · rw [(hoff w hw).1]; exact zero_mem _
  have hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hBv
    · rw [(hoff w hw).2]; exact zero_mem _
  have hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) =
      ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) *
        ((1 : L) ⊗ₜ[maximalRealSubfield L] B) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hAB, hsplit]
  refine Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩))
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SplitSep

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L

theorem exists_near (v : HeightOneSpectrum (𝓞 L⁺))
    (f : v.adicCompletion L⁺ → v.adicCompletion L⁺) (hf : Continuous f)
    (y₀ : v.adicCompletion L⁺) (hy₀ : Valued.v (f y₀) < 1) :
    ∃ a : L⁺, Valued.v (f (algebraMap L⁺ (v.adicCompletion L⁺) a)) < 1 := by
  have hU : IsOpen {z : v.adicCompletion L⁺ | Valued.v (f z) < 1} := by
    have h := (Valued.isOpen_ball (v.adicCompletion L⁺) 1).preimage hf
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L⁺) (K := L⁺) v).exists_mem_open
    hU ⟨y₀, hy₀⟩
  exact ⟨k, hk⟩


variable (L) in
theorem exists_sep (s : ReciprocityTheory.Aut.SplitPlace L) :
    ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
      Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ := ⟨_, rfl⟩
  have hcδ : cc δ = -δ := by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)
  obtain ⟨t, ht_def⟩ : ∃ t : s.v.adicCompletion L⁺, t = s.i δ := ⟨_, rfl⟩
  have ht : t ≠ 0 := by rw [ht_def]; exact (_root_.map_ne_zero s.i).mpr hδ0
  have h2 : (2 : s.v.adicCompletion L⁺) ≠ 0 := by
    have e : (2 : s.v.adicCompletion L⁺) = algebraMap L⁺ _ 2 := by rw [map_ofNat]
    rw [e]
    exact (_root_.map_ne_zero _).mpr two_ne_zero
  have h2half : (2 : s.v.adicCompletion L⁺)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  obtain ⟨a, ha⟩ := exists_near s.v (fun z => z - 2⁻¹) (by fun_prop) (2⁻¹) (by simp)
  have h0 : t⁻¹ * 2⁻¹ * t - 2⁻¹ = 0 := by
    rw [mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht, mul_one, sub_self]
  obtain ⟨b, hb⟩ := exists_near s.v (fun z => z * t - 2⁻¹)
    (by fun_prop) (t⁻¹ * 2⁻¹)
    (by simp only [h0, map_zero]; exact zero_lt_one)
  obtain ⟨x, hx⟩ : ∃ x : L, x = algebraMap L⁺ L a + algebraMap L⁺ L b * δ := ⟨_, rfl⟩
  have hix : s.i x = algebraMap L⁺ (s.v.adicCompletion L⁺) a +
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hx, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hcx : cc x = algebraMap L⁺ L a - algebraMap L⁺ L b * δ := by
    rw [hx, map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcδ]; ring
  have hicx : s.i (cc x) = algebraMap L⁺ (s.v.adicCompletion L⁺) a -
      algebraMap L⁺ (s.v.adicCompletion L⁺) b * t := by
    rw [hcx, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes, ht_def]
  have hx1 : Valued.v (s.i x) = 1 := by
    have e : s.i x - 1 = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) +
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hix]; linear_combination h2half
    refine (Valued.v.map_eq_of_sub_lt ?_).trans (map_one _)
    rw [map_one, e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  have hcx1 : Valued.v (s.i (cc x)) < 1 := by
    have e : s.i (cc x) = (algebraMap L⁺ (s.v.adicCompletion L⁺) a - 2⁻¹) -
        (algebraMap L⁺ (s.v.adicCompletion L⁺) b * t - 2⁻¹) := by
      rw [hicx]; ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hb)
  have hT : cc (x + cc x) = x + cc x := by
    rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm]
  have hN : cc (x * cc x) = x * cc x := by
    rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  let T : L⁺ := ⟨x + cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hT⟩
  let N : L⁺ := ⟨x * cc x, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hN⟩
  have hTL : algebraMap L⁺ L T = x + cc x := rfl
  have hNL : algebraMap L⁺ L N = x * cc x := rfl
  have hvT : s.v.valuation L⁺ T ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hTL, map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le hx1.le hcx1.le)
  have hvN : s.v.valuation L⁺ N ≤ 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap s.v, ← s.i.commutes, hNL, map_mul,
      Valuation.map_mul, hx1, one_mul]
    exact hcx1.le
  obtain ⟨n₁, d₁, hd₁⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v T hvT
  obtain ⟨n₂, d₂, hd₂⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer s.v N hvN
  obtain ⟨m, hm_def⟩ : ∃ m : 𝓞 L⁺, m = (d₁ : 𝓞 L⁺) * d₂ := ⟨_, rfl⟩
  have hm : m ∉ s.v.asIdeal := by rw [hm_def]; exact (d₁ * d₂).2
  obtain ⟨mK, hmK⟩ : ∃ mK : L⁺, mK = algebraMap (𝓞 L⁺) L⁺ m := ⟨_, rfl⟩
  have hp' : algebraMap (𝓞 L⁺) L⁺ (n₁ * d₂) = mK * T := by
    rw [map_mul, ← hd₁, hmK, hm_def, map_mul]; ring
  have hq' : algebraMap (𝓞 L⁺) L⁺ (n₂ * d₁ ^ 2 * d₂) = mK ^ 2 * N := by
    rw [map_mul, map_mul, map_pow, ← hd₂, hmK, hm_def, map_mul]; ring
  have hp : algebraMap (𝓞 L⁺) L (n₁ * d₂) = algebraMap L⁺ L mK * (x + cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hp', map_mul, hTL]
  have hq : algebraMap (𝓞 L⁺) L (n₂ * d₁ ^ 2 * d₂) = (algebraMap L⁺ L mK) ^ 2 * (x * cc x) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 L⁺) L⁺ L, hq', map_mul, map_pow, hNL]
  obtain ⟨y, hy_def⟩ : ∃ y : L, y = algebraMap L⁺ L mK * x := ⟨_, rfl⟩
  have hyA : IsIntegral (𝓞 L⁺) y := by
    refine ⟨X ^ 2 - C (n₁ * (d₂ : 𝓞 L⁺)) * X + C (n₂ * (d₁ : 𝓞 L⁺) ^ 2 * d₂), by monicity!, ?_⟩
    rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_X_pow, hp, hq, hy_def]
    ring
  have hy : IsIntegral ℤ y := isIntegral_trans y hyA
  have hvm : Valued.v (algebraMap L⁺ (s.v.adicCompletion L⁺) mK) = 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap s.v, hmK]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem s.v).mpr hm
  refine ⟨⟨y, hy⟩, ?_, ?_⟩
  · show Valued.v (s.i y) = 1
    rw [hy_def, map_mul, s.i.commutes, Valuation.map_mul, hvm, hx1, one_mul]
  · show Valued.v (s.i (cc y)) < 1
    rw [hy_def, map_mul, AlgEquiv.commutes, map_mul, s.i.commutes, Valuation.map_mul, hvm, one_mul]
    exact hcx1

end GlobalTheory.SplitSep
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
end
