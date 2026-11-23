module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle002
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.UnitPointLiftBall
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finCore_holds : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖AddMonoidAlgebra.coeff p μ‖ ∧
        AddMonoidAlgebra.coeff p μ ≠ 0 ∧ ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖AddMonoidAlgebra.coeff p ν‖) hne
    have hc : AddMonoidAlgebra.coeff p μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : AddMonoidAlgebra.coeff p ν = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖AddMonoidAlgebra.coeff p μ‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p ν‖
          ≤ ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p μ‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = AddMonoidAlgebra.coeff p μ *
        MvPolynomial.eval x (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push Not at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

lemma unzero_toAdd_eq_log (y : WithZero (Multiplicative ℤ)) (hy : y ≠ 0) :
    (WithZero.unzero hy).toAdd = WithZero.log y := by
  induction y using WithZero.recZeroCoe with
  | zero => exact absurd rfl hy
  | coe a => rfl

lemma norm_emb_eq (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordAt v x)) := by
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h1 : Valued.v (FinitePlace.embedding v x) = v.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [FinitePlace.norm_def, h1, WithZeroMulInt.toNNReal_neg_apply _ hv, ordAt, neg_neg]
  push_cast
  rfl

lemma one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma log_norm_emb (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((ordAt v x : ℝ) * logN v) := by
  rw [norm_emb_eq v hx, Real.log_zpow, logN]
  push_cast
  ring

lemma finite_mulSupport_emb {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖).Finite := by
  have h : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  refine (h.image FinitePlace.maximalIdeal).subset ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [Function.mem_mulSupport, FinitePlace.mk_apply] using hv

lemma support_ordAt_sub {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v) ⊆
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖ := by
  intro v hv
  rw [Function.mem_support] at hv
  rw [Function.mem_mulSupport]
  intro h
  apply hv
  have h2 := log_norm_emb v hx
  rw [h, Real.log_one] at h2
  linarith

lemma finite_ordAt {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite :=
  (finite_mulSupport_emb hx).subset (support_ordAt_sub hx)

lemma finsum_ordAt {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ x) := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  have hprod := NumberField.prod_abs_eq_one hx
  have hA : 0 < ∏ w : InfinitePlace K, w x ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 hx) _
  set s := hfin.toFinset with hs
  have hBs : ∏ᶠ w : FinitePlace K, w x = ∏ w ∈ s, w x :=
    finprod_eq_prod_of_mulSupport_subset _ (by simp [s])
  have hB : 0 < ∏ w ∈ s, w x := Finset.prod_pos fun w _ => FinitePlace.pos_iff.2 hx
  rw [hBs] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA.ne' hB.ne', Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx) _).ne'),
    Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hfs : ∑ w ∈ s, Real.log (w x) = ∑ᶠ w : FinitePlace K, Real.log (w x) := by
    rw [finsum_eq_sum_of_support_subset]
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [s, Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    rw [h1, Real.log_one]
  have heq : ∑ᶠ w : FinitePlace K, Real.log (w x) =
      -∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v := by
    rw [← finsum_neg_distrib, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun v => ?_
    have h3 : (FinitePlace.equivHeightOneSpectrum.symm v) x = ‖FinitePlace.embedding v x‖ := by
      rw [← FinitePlace.mk_apply]
      rfl
    rw [h3, log_norm_emb v hx]
  linarith

lemma log_det_le {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · simp [Matrix.det_fin_zero]
  have hpos : 0 < σ m.det := InfinitePlace.pos_iff.2 hdet
  let A : Matrix (Fin ρ) (Fin ρ) ℂ := fun i j => (Real.exp (a i) : ℂ) * σ.embedding (m i j)
  have hAdet : A.det = (∏ i, (Real.exp (a i) : ℂ)) * σ.embedding m.det := by
    have h : A = Matrix.diagonal (fun i => (Real.exp (a i) : ℂ)) * (σ.embedding.mapMatrix m) := by
      ext i j
      simp [A, Matrix.diagonal_mul]
    rw [h, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  have hnormA : ‖A.det‖ = Real.exp (∑ i, a i) * σ m.det := by
    rw [hAdet, norm_mul, norm_prod, InfinitePlace.norm_embedding_eq, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (b j) := by
    intro i j
    by_cases h : m i j = 0
    · simp [A, h, (Real.exp_pos _).le]
    · have hp : 0 < σ (m i j) := InfinitePlace.pos_iff.2 h
      have h2 := harch i j h
      simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        InfinitePlace.norm_embedding_eq]
      calc Real.exp (a i) * σ (m i j) = Real.exp (a i + Real.log (σ (m i j))) := by
            rw [Real.exp_add, Real.exp_log hp]
        _ ≤ Real.exp (b j) := Real.exp_le_exp.2 (by linarith)
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ρ * Real.exp (b j) := by
    intro j
    rw [← Real.sqrt_sq (Real.exp_pos (b j)).le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin ρ, Real.exp (b j) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
      _ = ρ * Real.exp (b j) ^ 2 := by simp
  have hH := ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le A.transpose
  rw [Matrix.det_transpose, hnormA] at hH
  simp only [Matrix.transpose_apply] at hH
  have hprod : ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ ∏ j : Fin ρ, (Real.sqrt ρ * Real.exp (b j)) :=
    Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) fun j _ => hcol j
  have key : Real.exp (∑ i, a i) * σ m.det ≤ Real.sqrt ρ ^ ρ * Real.exp (∑ j, b j) := by
    calc _ ≤ _ := hH
      _ ≤ _ := hprod
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by exact_mod_cast hρ)
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) key
  rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp,
    Real.log_mul (pow_pos hs _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg _)] at h1
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank

open NumberField Module
open scoped TensorProduct

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem rank_quot (M₁ : Submodule R X) (hM₁ : M₁.FG) (N : Submodule F X) :
    Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
        Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
      Module.finrank F ↥(Submodule.span F (M₁ : Set X)) := by
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn

end

section
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

theorem rank_QuotMW (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    Module.finrank (𝓞 K) (QuotMW M W) + Module.finrank K W = Module.finrank K V := by
  have h := rank_quot (F := K) M hM W
  rw [hspan, top_inf_eq, finrank_top] at h
  exact h

theorem span_tmul_one : Submodule.span K₁ (Set.range fun v : V => (1 : K₁) ⊗ₜ[K] v) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
    have : a ⊗ₜ[K] v = a • ((1 : K₁) ⊗ₜ[K] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem tmul_mem_span {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K₁ r]
    exact Submodule.smul_mem _ _ ha

theorem quot_finrank (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤) :
    finrank K₁ ((K₁ ⊗[K] V) ⧸
      Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) =
      finrank (𝓞 K) (QuotMW M W) := by
  have hρ := rank_QuotMW M hM hspan W
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have hP : finrank K₁ P ≤ finrank K W := by
    let B := Module.finBasis K W
    have hle : P ≤ Submodule.span K₁ (Set.range fun k => (1 : K₁) ⊗ₜ[K] ((B k : W) : V)) := by
      rw [hPdef, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      apply tmul_mem_span
      have h1 : (⟨a, ha⟩ : W) ∈ Submodule.span K (Set.range B) := by
        rw [B.span_eq]; trivial
      have h2 := Submodule.apply_mem_span_image_of_mem_span W.subtype h1
      rw [← Set.range_comp] at h2
      exact h2
    calc finrank K₁ P ≤ _ := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (finrank K W)) := finrank_range_le_card _
      _ = finrank K W := Fintype.card_fin _
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hU : finrank K₁ (K₁ ⊗[K] V) = finrank K V := Module.finrank_baseChange
  have hQ := Submodule.finrank_quotient_add_finrank P
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hle : finrank K₁ ((K₁ ⊗[K] V) ⧸ P) ≤ finrank (𝓞 K) (QuotMW M W) := by
    have h1 : finrank K₁ (Submodule.span K₁ (Set.range f)) ≤
        Fintype.card (Fin (finrank (𝓞 K) (QuotMW M W))) := finrank_range_le_card f
    rw [top_le_iff.mp hfspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  omega

theorem detCT_ne_zero (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) :
    detCT c θ ≠ 0 := by
  have hq := quot_finrank (K₁ := K₁) M hM hspan W θ hθ
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hli : LinearIndependent K₁ f :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hfspan (by rw [Fintype.card_fin, hq])
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hx : ∑ j, a j • e j ∈ P := by
    rw [← hc]
    intro i
    have h1 := congrFun ha i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1

    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc _ = ∑ j, c i (e j) * a j := Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := h1
  have h2 : ∑ j, a j • f j = 0 := by

    simp only [f, ← map_smul, ← map_sum]
    exact (Submodule.Quotient.mk_eq_zero P).mpr hx
  exact ha0 (funext (Fintype.linearIndependent_iff.mp hli a h2))

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
end
