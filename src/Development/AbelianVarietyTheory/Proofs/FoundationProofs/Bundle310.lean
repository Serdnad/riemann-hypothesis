module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle001

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.ThetaCovIndex

open GlobalTheory.ThetaInter Module

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]


omit [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in
theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ W) {L₁ L₂ : AddSubgroup W}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem exists_basis_finrank {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ W)) ℝ W, (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology A.toIntSubmodule := hA
  have : IsZLattice ℝ A.toIntSubmodule := ⟨hsp⟩
  let b₀ := Module.finBasisOfFinrankEq ℤ A.toIntSubmodule (ZLattice.rank ℝ A.toIntSubmodule)
  refine ⟨b₀.ofZLatticeBasis ℝ A.toIntSubmodule, ?_⟩
  rw [Basis.ofZLatticeBasis_span]
  rfl

theorem relIndex_map {A B : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (f : W ≃ₗ[ℝ] W) (hB : B ≤ A)
    (hf : B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ≤ A) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ B, m • x = f y) :
    B.relIndex A ≠ 0 ∧ ((B.map (f : W →ₗ[ℝ] W).toAddMonoidHom).relIndex A : ℝ) =
      B.relIndex A * |LinearMap.det (f : W →ₗ[ℝ] W)| := by
  have hBd : DiscreteTopology B := DiscreteTopology.of_subset hA hB
  have hBs : Submodule.span ℝ (B : Set W) = ⊤ := by
    have h1 : (Submodule.span ℝ (B : Set W)).map (f : W →ₗ[ℝ] W) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      intro x hxA
      obtain ⟨y, hy, e⟩ := hx x hxA
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      refine ⟨(m : ℝ)⁻¹ • y, Submodule.smul_mem _ _ (Submodule.subset_span hy), ?_⟩
      simp only [LinearEquiv.coe_coe, map_smul]
      rw [← e, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := (h1.ge (Submodule.mem_top (x := f x)))
    exact f.injective e ▸ hy
  obtain ⟨a, ha⟩ := exists_basis_finrank hA hsp
  obtain ⟨b, hb⟩ := exists_basis_finrank hBd hBs
  have hb₁ : (Submodule.span ℤ (Set.range (b.map f))).toAddSubgroup =
      B.map (f : W →ₗ[ℝ] W).toAddMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have : f x ∈ B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ↔ x ∈ B :=
      AddSubgroup.mem_map_iff_mem (f := (f : W →ₗ[ℝ] W).toAddMonoidHom) f.injective
    rw [this, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  have e1 := relIndex_eq_abs_det b a hb ha hB
  generalize B.map (f : W →ₗ[ℝ] W).toAddMonoidHom = C at hf hb₁ ⊢
  have e2 := relIndex_eq_abs_det (b.map f) a hb₁ ha hf
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at e1
    exact IsUnit.ne_zero (a.isUnit_det b) e1
  · rw [e2, e1, ← abs_mul, mul_comm, ← a.det_comp (f : W →ₗ[ℝ] W) b, Basis.coe_map]
    rfl

end General

theorem relIndex_image_one_sub_complexLinearEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {A A₁ : AddSubgroup W} (t₁ : DiscreteTopology A) (s₁ : Submodule.span ℝ (A : Set W) = ⊤)
    (u : W ≃ₗ[ℂ] W) (hA : ∀ x, x ∈ A ↔ u x ∈ A₁)
    (hdet : LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W)) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) :
    A₁.relIndex A ≠ 0 ∧
      (((A.map (LinearMap.id - (u.symm : W →ₗ[ℂ] W)).toAddMonoidHom).relIndex A : ℕ) : ℝ) =
        (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W))‖ ^ 2 := by
  set g : W →ₗ[ℂ] W := LinearMap.id - (u.symm : W →ₗ[ℂ] W) with hg
  have hgy : ∀ y, g y = y - u.symm y := fun y => rfl
  let f : W ≃ₗ[ℝ] W := (LinearMap.equivOfDetNeZero g hdet).restrictScalars ℝ
  have hfg : (f : W →ₗ[ℝ] W) = g.restrictScalars ℝ := by
    ext1 y; simp [f]
  have hfy : ∀ y, f y = y - u.symm y := fun y => congrArg (fun φ => φ y) hfg
  have hA' : ∀ y, u.symm y ∈ A ↔ y ∈ A₁ := fun y => by rw [hA, u.apply_symm_apply]
  have hinf : (A₁ ⊓ A).map (f : W →ₗ[ℝ] W).toAddMonoidHom = A.map g.toAddMonoidHom ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy₁, hy⟩, rfl⟩
      refine ⟨⟨y, hy, (hfy y).symm⟩, ?_⟩
      change f y ∈ A
      rw [hfy]
      exact A.sub_mem hy ((hA' y).2 hy₁)
    · rintro ⟨⟨y, hy, rfl⟩, h2⟩
      refine ⟨y, ⟨(hA' y).1 ?_, hy⟩, hfy y⟩
      have h3 : y - u.symm y ∈ A := h2
      simpa using A.sub_mem hy h3
  have key := relIndex_map (B := A₁ ⊓ A) t₁ s₁ f inf_le_right (hinf.le.trans inf_le_right) hm
    fun x hxA => by
      obtain ⟨y, hy, hy', e⟩ := hx x hxA
      exact ⟨y, ⟨(hA' y).1 hy', hy⟩, e.trans (hfy y).symm⟩
  rw [hinf, AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hfg,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity)] at key
  exact key

theorem relIndex_one_sub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → A₁.relIndex A ≠ 0 ∧ ((((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A : ℕ) : ℝ)) = (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ ^ 2 := by
  intro D cc δ hc N N' A A₁ h₁ _ u _ hA hdet ⟨m, hm, hx⟩
  obtain ⟨f₁, s₁, d₁, -⟩ := klat_facts hc h₁
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  exact relIndex_image_one_sub_complexLinearEquiv t₁ s₁ u hA hdet hm hx

end GlobalTheory.ThetaCovIndex
end

section

open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)

namespace GlobalTheory

namespace RootClassCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_herm_iff {n : ℕ} (x y : Fin n → E) :
    IsIntegral ℤ (herm 1 y x) ↔ IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i) := by
  rw [DualFamily.herm_one_eq]
  simp only [cc, mul_comm]

theorem mul_conjTranspose_eq_one {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, herm 1 (γ.mulVec x) (γ.mulVec y) = herm 1 x y) :
    γ * (γ.map (IsCMField.complexConj E)).transpose = 1 := by
  rw [mul_eq_one_comm]
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [DualFamily.herm_one_eq, DualFamily.herm_one_eq] at this
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, cc] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm, Matrix.one_apply]
  rw [this]
  simp [Pi.single_apply, eq_comm]

omit [IsCMField E] in
theorem rdE_eq : rdE E = |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := rfl

omit [IsCMField E] in
theorem one_le_rootDiscr : 1 ≤ |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
  refine Real.one_le_rpow ?_ (by positivity)
  exact_mod_cast Int.one_le_abs (discr_ne_zero E)

theorem exists_bounded_basis {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hint : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm 1 x y)) → x ∈ L) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ L) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤
        4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2 := by
  obtain ⟨v, hv, hli, -, hle⟩ := exists_short_vectors L hfg hint hdual
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by
    simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  have h3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
    norm_num
  refine ⟨fun i => v (e i), fun i => hv _, hs2.comp e e.injective, fun σ i k => ?_⟩
  refine (SelfDualClasses.norm_herm_le σ _ _ _ (hle _ σ) (hle _ σ)).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, h3]
  ring

theorem bound_le (f n : ℕ) {r : ℝ} (hf : 0 < f) (hr : 1 ≤ r) :
    (1 + 2 * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) *
      (n * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) ≤
      (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2)) ^ (3 * (2 * f) * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := ((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 with hp
  have hp' : p = 4 * (f : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 := by rw [hp]; push_cast; ring
  have hB : 4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2 = f * p := by rw [hp']; ring
  have h1 : (f : ℝ) ^ 2 * n ≤ p := by
    rw [hp']
    have h2 : (n : ℝ) ≤ n ^ 4 := le_self_pow₀ hn' (by norm_num)
    have h3 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    calc (f : ℝ) ^ 2 * n = 1 * (f : ℝ) ^ 2 * n * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have h4 : 1 ≤ (f : ℝ) ^ 2 * n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hn'
  have h5 : 1 ≤ p := h4.trans h1
  have h6 : 1 ≤ f * p := one_le_mul_of_one_le_of_one_le hf' h5
  rw [hB, ← mul_pow, mul_assoc 3, pow_mul _ 3]
  gcongr
  calc (1 + 2 * (f * p)) * (n * (f * p)) ≤ (3 * (f * p)) * (n * (f * p)) := by
        gcongr; linarith
    _ = 3 * ((f : ℝ) ^ 2 * n) * p ^ 2 := by ring
    _ ≤ 27 * p * p ^ 2 := by gcongr; norm_num
    _ = _ := by ring

end RootClassCount


open RootClassCount in
theorem exists_finset_selfDual_classes_rootDiscr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
  intro E _ _ _ n
  obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
    (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine ⟨R, h3.trans ?_, fun L hfg _ hsd => ?_⟩
  · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
    rw [← ShortVectors.finrank_eq] at h
    rw [rdE_eq, ← ShortVectors.finrank_eq]
    exact h
  · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
      simp only [isIntegral_herm_iff]; exact hsd y⟩
    exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩

end GlobalTheory
end
