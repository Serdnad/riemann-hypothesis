module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory.MonicRootsProduct

theorem exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by
  classical
  have hc : p.roots.toList.length = p.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  refine ⟨fun j => p.roots.toList[(j : ℕ)]'(by rw [hc]; exact j.2), ?_⟩
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    IsAlgClosed.card_roots_eq_natDegree
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem] at hprod
  exact (Fintype.prod_equiv (finCongr hc.symm) _ _ (fun j => rfl)).trans hprod

theorem exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩

end GlobalTheory.MonicRootsProduct
end

section

open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise

namespace GlobalTheory


open Pointwise in
theorem integrableOn_fundamentalDomain_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  intro G _ _ _ _ _ Γ _ K hK hcov μ hμ 𝓕 h𝓕 f hf hinv
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ g, ‖f g‖ ≤ C := by
    intro g
    obtain ⟨γ, hγ, hγg⟩ := hcov g
    rw [← hinv γ hγ g]
    exact hC _ hγg
  have hcover : 𝓕 ⊆ ⋃ γ : Γ, (γ • K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    refine Set.mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hγx
  have hle : μ 𝓕 ≤ μ K :=
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, (γ • K ∩ 𝓕)) := measure_mono hcover
      _ ≤ ∑' γ : Γ, μ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ K := (h𝓕.measure_eq_tsum K).symm
  exact Measure.integrableOn_of_bounded (hle.trans_lt hK.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) (ae_of_all _ hbound)

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory

theorem exists_isAddHaarMeasure_isAddFundamentalDomain_preimage :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H), Continuous e → Continuous e.symm → ∀ (Γ : AddSubgroup G) (Λ : AddSubgroup H), (∀ x, e x ∈ Λ ↔ x ∈ Γ) → ∀ (μ : Measure H) (𝓕 : Set H), μ.IsAddHaarMeasure → IsAddFundamentalDomain Λ 𝓕 μ → ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧ ∀ φ : H → ℝ, ∫ w in e ⁻¹' 𝓕, φ (e w) ∂ν = ∫ w in 𝓕, φ w ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ e he hes Γ Λ hΓ μ 𝓕 hμ h𝓕
  let m : G ≃ᵐ H :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  refine ⟨μ.map e.symm, AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he), ?_, ?_⟩
  · let f : Λ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro φ
    exact hmp.setIntegral_preimage_emb m.measurableEmbedding φ 𝓕

end GlobalTheory
end

section

namespace GlobalTheory

theorem bddAbove_of_spanning_periods (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by
  classical
  let P : AddSubgroup R :=
    { carrier := {p | ∀ x, g (x + p) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [← this]; simp }
  have hP : Submodule.span ℝ (P : Set R) = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro s hs
    obtain ⟨N, hN, h⟩ := hper s hs
    have h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R) := Submodule.subset_span h
    have h2 := Submodule.smul_mem _ ((N : ℝ)⁻¹) h1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at h2
  obtain ⟨t, htP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set R)
  have hfin : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b : Module.Basis t ℝ R := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hP])
  have hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (i : R) := by simp [b]
    rw [this]
    exact htP i.2
  have hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hfl : ((ZSpan.floor b x : R)) ∈ P := hb (ZSpan.floor b x).2
  have hx : g x = g (ZSpan.fract b x) := by
    have := hfl (ZSpan.fract b x)
    rw [← this, ZSpan.fract_apply]; simp
  rw [hx]
  apply hC
  exact ⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem exp_neg_mul_sqrt_div_pow_le (a : ℝ) (D : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) /
      (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  refine ⟨Real.exp a * ((D + 1).factorial : ℝ) / a ^ (D + 1), fun m => ?_⟩
  set s : ℝ := (m : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by rw [hs]; have := m.cast_nonneg (α := ℝ); linarith
  have hs0 : 0 < s := by linarith
  set x : ℝ := s ^ (-(1 / 2 : ℝ)) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hs0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hx2 : x ^ 2 * s = 1 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hmx : (m : ℝ) * x = x⁻¹ - x := by
    have : (m : ℝ) = s - 1 := by rw [hs]; ring
    rw [this]; field_simp; nlinarith [hx2]
  set n := D + 1 with hn
  have hK : 0 < Real.exp a * (n.factorial : ℝ) / a ^ n := by positivity

  have hpow := Real.pow_div_factorial_le_exp (a / x) (by positivity) n
  have hexp : Real.exp (-(a * m * x)) * Real.exp (a / x) ≤ Real.exp a := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : a * m * x = a * (x⁻¹ - x) := by rw [mul_assoc, hmx]
    rw [this, div_eq_mul_inv]
    nlinarith
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have h1 : Real.exp (-(a * m * x)) * ((a / x) ^ n / n.factorial) ≤ Real.exp a :=
    le_trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hexp
  have h2 : Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_pow, div_div, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    have e : Real.exp a * (n.factorial : ℝ) / a ^ n * x * x ^ D
        = Real.exp a * (x ^ n * n.factorial) / a ^ n := by
      rw [hn, pow_succ]; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [h1]

  have hxs : x ≤ Real.sqrt x := by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  calc Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := h2
    _ ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hxs hK.le

end GlobalTheory
end

section

namespace GlobalTheory.PolynomialCoeffEq

open Module

theorem coeff_eq {R : Type} [AddCommGroup R] [Module ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) {n : ℕ} (v : Basis (Fin n) ℝ R)
    (hv : ∀ i j, i ≠ j → g (v i) (v j) = 0) (x : R) (k : Fin n) :
    g x (v k) = v.repr x k * g (v k) (v k) := by
  conv_lhs => rw [← v.sum_repr x]

  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · intro i _ hik
    rw [hv i k hik, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem main : ∀ {R : Type} [inst : AddCommGroup R] [inst_1 : Module ℝ R] [FiniteDimensional ℝ R] (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ (u v : R), ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) v = ((g : R → R →ₗ[ℝ] ℝ) v : R → ℝ) u) → (∀ (u : R), u ≠ (0 : R) → (0 : ℝ) < ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) u) → ∃ (n : ℕ) (e : Fin n → R), ∀ (x : R), ∑ k : Fin n, ((g : R → R →ₗ[ℝ] ℝ) x : R → ℝ) (e k) • e k = x := by
  intro R _ _ _ g hsym hpos
  have h2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g) ⟨hsym⟩
  have hv' : ∀ i j, i ≠ j → g (v i) (v j) = 0 := LinearMap.BilinForm.iIsOrtho_def.mp hv
  have hpos' : ∀ k, 0 < g (v k) (v k) := fun k => hpos _ (v.ne_zero k)
  refine ⟨_, fun k => (Real.sqrt (g (v k) (v k)))⁻¹ • v k, fun x => ?_⟩
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, coeff_eq g v hv' x k, smul_smul]
  congr 1
  have hs := Real.mul_self_sqrt (hpos' k).le
  have he : (Real.sqrt (g (v k) (v k)))⁻¹ * (v.repr x k * g (v k) (v k)) *
      (Real.sqrt (g (v k) (v k)))⁻¹ =
      v.repr x k * (g (v k) (v k) * (Real.sqrt (g (v k) (v k)) * Real.sqrt (g (v k) (v k)))⁻¹) := by
    ring
  rw [he, hs, mul_inv_cancel₀ (hpos' k).ne', mul_one]

end GlobalTheory.PolynomialCoeffEq
end

section

namespace GlobalTheory.NatMulMemRingOfIntegers

theorem exists_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (r : NumberField.RingOfIntegers E), (r : E) = (k : E) * e := by
  have h0 : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have halg : IsAlgebraic ℤ e := (IsAlgebraic.of_finite ℚ e).restrictScalars ℤ
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with hy | hy
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨(y : E) * e, (mem_integralClosure_iff ℤ E).mpr hint⟩, ?_⟩
    show (y : E) * e = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_natCast]
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨-((y : E) * e), (mem_integralClosure_iff ℤ E).mpr hint.neg⟩, ?_⟩
    show -((y : E) * e) = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_neg, Int.cast_natCast]
    ring

end GlobalTheory.NatMulMemRingOfIntegers
end

section

namespace GlobalTheory.AdicNormZpowEstimates

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

theorem norm_eq_zpow (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F)
    (hy : y ≠ 0) : ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := by simpa using hy
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  exact ⟨_, by push_cast; rfl⟩

theorem one_lt_norm (v : HeightOneSpectrum (RingOfIntegers F)) :
    (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem norm_le_of_lt (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F) (m : ℤ)
    (h : ‖y‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (m + 1)) :
    ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  have h1 := one_lt_norm v
  by_cases hy : y = 0
  · rw [hy, norm_zero]
    positivity
  · obtain ⟨k, hk⟩ := norm_eq_zpow v y hy
    rw [hk] at h ⊢
    rw [zpow_lt_zpow_iff_right₀ h1] at h
    exact zpow_le_zpow_right₀ h1.le (by omega)

theorem natCast_eq (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    (n : v.adicCompletion F)
      = FinitePlace.embedding v (algebraMap (RingOfIntegers F) F (n : RingOfIntegers F)) := by
  rw [map_natCast, map_natCast]

theorem norm_natCast_le (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  rw [natCast_eq]
  exact FinitePlace.norm_le_one F v _

theorem norm_absNorm_le (v : HeightOneSpectrum (RingOfIntegers F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖
      ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have := norm_le_of_lt v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) (-1) (by
    rw [natCast_eq, neg_add_cancel, zpow_zero, FinitePlace.norm_lt_one_iff_mem]
    exact Ideal.absNorm_mem _)
  simpa using this

theorem exists_denominator {F : Type} [Field F] [NumberField F]
    (H : HeightOneSpectrum (RingOfIntegers F) → NNReal) (h1 : ∀ v, (1 : NNReal) ≤ H v)
    (hfin : Set.Finite (Function.mulSupport H)) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F),
        ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ (1 : ℝ) := by
  classical
  have hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), ∃ n : ℕ,
      (Ideal.absNorm v.asIdeal : ℝ) ^ n ≤ H v ∧ (H v : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (n + 1) :=
    fun v => exists_nat_pow_near (by exact_mod_cast h1 v) (one_lt_norm v)
  choose n hle hlt using hn
  refine ⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_, ?_⟩
  · refine Finset.prod_pos fun v _ => pow_pos ?_ _
    exact lt_trans Nat.one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  · rw [finprod_eq_prod_of_mulSupport_subset H (s := hfin.toFinset) (by simp), Nat.cast_prod]
    refine Finset.prod_le_prod' fun v _ => ?_
    have := hle v
    exact_mod_cast this
  · intro v y hy
    have hy' : ‖y‖ ≤ (H v : ℝ) := by exact_mod_cast hy
    rw [norm_mul]
    by_cases hv : v ∈ hfin.toFinset
    · have hq := one_lt_norm v
      have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans one_pos hq
      have h2 : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n v := by
        have := norm_le_of_lt v y (n v) (by
          have := lt_of_le_of_lt hy' (hlt v)
          exact_mod_cast this)
        simpa using this
      rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      have h3 : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ n v
          ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_absNorm_le v) _
      calc _ ≤ (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v * 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ n v :=
            mul_le_mul (mul_le_mul h3 (norm_natCast_le v _) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [mul_one, ← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
    · have h2 : H v = 1 := by simpa using hv
      rw [h2] at hy'
      exact mul_le_one₀ (norm_natCast_le v _) (norm_nonneg _) (by simpa using hy')

end GlobalTheory.AdicNormZpowEstimates
end
