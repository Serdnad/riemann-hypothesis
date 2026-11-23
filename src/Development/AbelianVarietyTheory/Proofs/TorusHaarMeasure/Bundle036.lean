module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle012
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.HeightSubmodular

theorem gram_det_re_nonneg {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq ι]
    (N : Matrix m ι ℂ) : 0 ≤ (Nᴴ * N).det.re := by
  have h : (0 : ℂ) ≤ (Nᴴ * N).det := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem div_mul_div_le {p q p' q' : ℝ} {i j i' j' : ℕ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p * q ≤ p' * q') (hi : i' ≠ 0) (hj : j' ≠ 0) (hij : i' * j' ≤ i * j) :
    p / i * (q / j) ≤ p' / i' * (q' / j') := by
  have hnum : 0 ≤ p' * q' := (mul_nonneg hp hq).trans h
  have hden : (0 : ℝ) < (i' : ℝ) * j' :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast Nat.pos_of_ne_zero hj)
  rw [div_mul_div_comm, div_mul_div_comm]
  rcases Nat.eq_zero_or_pos (i * j) with h0 | h0
  · have hz : (i : ℝ) * j = 0 := by exact_mod_cast h0
    rw [hz, div_zero]
    exact div_nonneg hnum hden.le
  · exact div_le_div₀ hnum h hden (by exact_mod_cast hij)

theorem height_submodular : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W₁ W₂, d x (W₁ ⊓ W₂) * d x (W₁ ⊔ W₂) ≤ d x W₁ * d x W₂) := by
  intro r X d hd x hx W₁ W₂
  obtain ⟨a, b, c, w, hli, hmem, h0, h1, h2, h3⟩ :=
    GlobalTheory.LatBasisAdapted.exists_basis_adapted_mem r X W₁ W₂
  have hsub : ∀ {κ : Type} (f : κ → Fin a ⊕ Fin b ⊕ Fin c) (τ : X.Ψ),
      (mat x τ)⁻¹ * (Matrix.of fun k l => τ.1 ((w ∘ f) l k)) =
        ((mat x τ)⁻¹ * Matrix.of fun k l => τ.1 (w l k)).submatrix id f := by
    intro κ f τ
    ext k l
    simp [Matrix.mul_apply]
  have key := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    hd x hx κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have hI := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    GlobalTheory.SpanIndex.relIndex_span_ne_zero r X κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have i1 : Function.Injective (Sum.map id Sum.inl : Fin a ⊕ Fin b → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have i2 : Function.Injective (Sum.map id Sum.inr : Fin a ⊕ Fin c → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩
  rw [← h0, ← h3, ← h1, ← h2, key _ Sum.inl_injective, key _ i1, key _ i2,
    hd x hx _ w hli hmem]
  apply div_mul_div_le
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro τ _
      exact mul_nonneg (gram_det_re_nonneg _) (gram_det_re_nonneg _)
    · intro τ _
      simp only [hsub]
      exact (GlobalTheory.T.gramDet_inequalities_closed_forms).1 (Fin r) (Fin a) (Fin b) (Fin c) _
  · exact hI _ i1
  · exact hI _ i2
  · exact (GlobalTheory.T.relIndex_integralSpan_supermultiplicative) r X (Fin a) (Fin b) (Fin c) w hli hmem

end GlobalTheory.HeightSubmodular
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.HeightStep.height_update : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (d : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  classical
  intro r X d hd x hx τ0 W
  obtain ⟨w, hli, hmem, hspan⟩ := _root_.GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, -, hdet⟩ := _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hli
  set N : X.Ψ → Matrix (Fin r) (Fin (Module.finrank E W)) ℂ :=
    fun τ => Matrix.of fun k a => τ.1 (w a k) with hN
  set M := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0)⁻¹ * N τ0 with hM
  have hA : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0).det := isUnit_iff_ne_zero.mpr (hx τ0)
  have hminor : (Matrix.of fun k a => N τ0 (e k) a).det ≠ 0 := by
    have hmap : (Matrix.of fun k a => N τ0 (e k) a) =
        τ0.1.mapMatrix (Matrix.of fun k a => w a (e k)) := by
      ext k a
      rfl
    rw [hmap, ← RingHom.map_det]
    exact (map_ne_zero τ0.1).mpr hdet
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    rw [← sub_eq_zero]
    have h0 : M *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have h1 : N τ0 *ᵥ (u - v) = 0 := by
      have : N τ0 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * M := by
        rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
      rw [this, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hminor
    funext k
    have := congrFun h1 (e k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hpos : 0 < ((Mᴴ * M).det.re) := by
    have := (Matrix.PosDef.conjTranspose_mul_self M hinj).det_pos
    exact (Complex.pos_iff.mp this).1
  refine ⟨M, hpos, fun a ha => ?_⟩
  set x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := @Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _)
    x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ) with hx'
  have haU : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hupd : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ = if τ = τ0 then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ else _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := by
    intro τ
    by_cases h : τ = τ0
    · subst h
      rw [if_pos rfl, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _
    · rw [if_neg h, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _
  have hx'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det ≠ 0 := by
    intro τ
    rw [hupd]
    split_ifs
    · rw [Matrix.det_mul]
      exact mul_ne_zero (hx τ0) (Matrix.isUnit_nonsing_inv_det a haU).ne_zero
    · exact hx τ
  set F : X.Ψ → ℝ := fun τ => (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)).det.re with hF
  have h1 := hd x' hx'det _ w hli hmem
  have h2 := hd x hx _ w hli hmem
  rw [hspan] at h1 h2
  rw [h1, h2]
  have hprod' : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      (((a * M)ᴴ * (a * M)).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Function.update_apply, hupd]
    split_ifs with h
    · subst h
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a haU, Matrix.mul_assoc]
    · rfl
  have hprod : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      ((Mᴴ * M).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0), Function.update_eq_self]
  rw [hprod', hprod]
  have hne : (Mᴴ * M).det.re ≠ 0 := hpos.ne'
  field_simp

end GlobalTheory.HeightStep
end
