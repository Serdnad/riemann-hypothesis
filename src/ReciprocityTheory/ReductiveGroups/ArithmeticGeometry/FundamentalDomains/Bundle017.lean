module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle015

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering

open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cover_OE (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
  set f : ℝ := (Fintype.card (CP E) : ℝ) with hf_def
  have hf : 0 < f := Nat.cast_pos.mpr card_complexPlaces_pos
  set D := dE E with hD_def
  have hD : 0 < D := dE_pos
  set t := D ^ (1 / f) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hD _
  have htinv : D ^ (-(1 / f)) = t⁻¹ := Real.rpow_neg hD.le _
  set lam := Real.sqrt (4 * f * t⁻¹) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = 4 * f * t⁻¹ := Real.sq_sqrt (by positivity)
  have hmin : ∀ x ∈ span ℤ (Set.range (bd E)), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have hnorm := norm_bd_ge x hx hx0
    rw [← hf_def, ← hD_def, htinv] at hnorm
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hnorm
  obtain ⟨x, hx, hxb⟩ := BabaiCovering.cover (bas E) (bd E) inner_bas_bd lam hlam hmin Z
  obtain ⟨α, rfl⟩ := mem_span_bas hx
  refine ⟨α, ?_⟩
  have hn : (finrank ℝ (VS E) : ℝ) = 2 * f := by
    rw [finrank_VS, (card_CP (E := E)).2]
    push_cast
    ring
  have hfdeg : (fdeg E : ℝ) = f := by rw [← (card_CP (E := E)).1]
  have hrd : rdE E ^ 2 = t := by
    rw [rdE, ← hD_def, (card_CP (E := E)).2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    rw [← hf_def]
    field_simp
  rw [hn] at hxb
  have hbound : (2 * f) / 4 * ((2 * f) ^ 2 / lam) ^ 2 = 2 * f ^ 4 * t := by
    rw [div_pow, hlam2]
    field_simp
    ring
  rw [hbound] at hxb
  have hB : 0 ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num : (2 : ℕ) ≠ 0)]
  calc ‖Z - iota E (α : E)‖ ^ 2 ≤ 2 * f ^ 4 * t := hxb
    _ ≤ 4 * f ^ 4 * t := by nlinarith [pow_pos hf 4]
    _ = (2 * (fdeg E : ℝ) ^ 2 * rdE E) ^ 2 := by
        rw [mul_pow, mul_pow, hrd, hfdeg]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def pform (X : Data E r) : ReciprocityTheory.MultiplicativeHeights.HermForm E r where
  c := (IsCMField.complexConj E).toAlgHom.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := X.Gmᵀ
  G_herm a b := X.Gm_herm b a

lemma pform_h (X : Data E r) (x y : Fin r → E) : (pform X).h x y = herm X.Gm y x := by
  change ∑ a, ∑ b, cc (x a) * X.Gm b a * y b = ∑ a, ∑ b, y a * X.Gm a b * cc (x b)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma isLattice (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsLattice X.L' := by
  refine ⟨X.L'_fg, ?_⟩
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have hmem : (X.NA : E) • x ∈ Submodule.span E (X.L' : Set (Fin r → E)) :=
    Submodule.subset_span (X.NA_sub x hx)
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have hx' := Submodule.smul_mem _ ((X.NA : E)⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hNA, one_smul] at hx'
lemma selfDual (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsSelfDual (pform X.toData) X.L' := by
  have key : ∀ x y, (pform X.toData).h x y = cc (herm X.Gm x y) := fun x y => by
    rw [pform_h, ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm X.Gm_herm]
  have toI : ∀ z : E, IsIntegral ℤ z → ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have ofI : ∀ z : E, ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z → IsIntegral ℤ z := by
    rintro z ⟨o, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe o
  have ccI : ∀ z : E, IsIntegral ℤ z → IsIntegral ℤ (cc z) := fun z hz =>
    hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  refine ⟨fun x hx y hy => ?_, fun x hx => X.L'_dual x fun y hy => ?_⟩
  · rw [key]
    exact toI _ (ccI _ (X.L'_int x hx y hy))
  · have h1 := hx y hy
    rw [key] at h1
    have h2 := ccI _ (ofI _ h1)
    simpa [cc, IsCMField.complexConj_apply_apply] using h2

private lemma sum_inv_mulVec_smul_col_of_det_ne_zero (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (w : Fin r → ℂ) :
    ∑ k, (M⁻¹ *ᵥ w) k • col M k = w := by
  have h2 : M *ᵥ (M⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  conv_rhs => rw [← h2]
  funext i
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

private lemma hermC_col_mat_of_isOrtho (X : Data E r) {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (k l : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) k) (col (mat x τ) l) =
      if k = l then (if (k : ℕ) < X.p0 then (1 : ℂ) else -1) else 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply (X := X) ho τ k l]
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : (k : ℕ) < X.p0
    · simp [hk, sgn]
    · simp [hk, sgn]
  · simp [hkl]

lemma maj_ortho (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (v : Fin r → ℂ) : X.maj x τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x τ)⁻¹ *ᵥ v) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  set c := (mat x τ)⁻¹ *ᵥ v with hc
  have hv : v = ∑ k, c k • col (mat x τ) k := (sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet v).symm
  have hcol : ∀ a, col (mat x τ) a = ∑ l, (Pi.single a 1 : Fin r → ℂ) l • col (mat x τ) l := by
    intro a
    simp [Pi.single_apply]
  have hpair : ∀ a : Fin r, hermC τ.1 X.Gm v (col (mat x τ) a) = ReciprocityTheory.MultiplicativeHeights.sgn X.p0 a * c a := by
    intro a
    rw [hv, hcol a, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.single_apply, apply_ite]
  have hgp : X.gramPos x τ = 1 := by
    unfold Data.gramPos
    rw [ho τ]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, sgn, a.isLt]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab, Fin.castLE_inj]
  have hpos : X.posPart x τ v = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 := by
    unfold Data.posPart
    rw [hgp, inv_one]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hpair]
    simp [ReciprocityTheory.MultiplicativeHeights.sgn]
  have hself : (hermC τ.1 X.Gm v v).re = ∑ k : Fin r, (if (k : ℕ) < X.p0 then (1 : ℝ) else -1) * ‖c k‖ ^ 2 := by
    rw [hv, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Complex.re_sum, ReciprocityTheory.MultiplicativeHeights.sgn]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
    have hre : (((‖c k‖ : ℝ) : ℂ) ^ 2).re = ‖c k‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    split_ifs <;> simp [hre]
  unfold Data.maj
  rw [hpos, hself]
  unfold ReciprocityTheory.MultiplicativeHeights.normSq
  have hsplit : ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then ‖c k‖ ^ 2 else 0 :=
    Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _
      (fun k hk => by
        rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩)
      (fun a => by simp [a.isLt])
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma herm_coord (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → E) : τ.1 (herm X.Gm u v) = ReciprocityTheory.MultiplicativeHeights.jForm X.p0
      ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  have h1 : τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, hermC, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
  calc τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := h1
    _ = hermC τ.1 X.Gm (∑ k, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) k • col (mat x τ) k)
          (∑ l, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) l • col (mat x τ) l) := by
        rw [sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet, sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet]
    _ = _ := ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf _ _

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex Filter Topology

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem d4l4_c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  show 0 < 2 * ‖τ.1 X.ξ0‖
  exact mul_pos two_pos (norm_pos_iff.mpr h)

open Classical in
theorem d4l4_diff_flow {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℂ) (τ0 : X.Ψ) :
    Differentiable ℂ (fun z : ℂ => X.flowV e (Function.update s τ0 z) x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hu : Differentiable ℂ (fun z : ℂ => Function.update s τ0 z τ) := by
    by_cases h : τ = τ0
    · subst h
      simpa using differentiable_id
    · simpa [Function.update_of_ne h] using differentiable_const (s τ)
  intro z
  simp only [Data.flowV, Matrix.mul_apply, Data.flowMatV, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact hu z

theorem holomorphic_periodicity_extension : HolomorphicPeriodicityExtension (E := E) := by
  classical
  intro r X e he G hG m x hx hreal s hs
  have hdom : ∀ s' : X.Ψ → ℂ, X.flowV e s' x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s' τ).im / X.ttV e x τ :=
    fun s' => (flowDomainCriterion_holds (E := E) r X e he x hx s').1
  set H : (X.Ψ → ℂ) → ℂ := fun s' =>
    G (X.flowV e s' x) - cexp (4 * Real.pi * I * ∑ τ, m τ * s' τ) * G x with hH

  suffices key : ∀ A : Finset X.Ψ, ∀ s' : X.Ψ → ℂ, (∀ τ ∉ A, (s' τ).im = 0) →
      X.flowV e s' x ∈ X.dom → H s' = 0 by
    exact sub_eq_zero.mp (key Finset.univ s (fun τ h => absurd (Finset.mem_univ τ) h) hs)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro s' hs' _
    have hre : ∀ τ, (((s' τ).re : ℝ) : ℂ) = s' τ := fun τ =>
      Complex.ext (by simp) (by simp [hs' τ (by simp)])
    have h0 := hreal (fun τ => (s' τ).re)
    simp only [hre] at h0
    simp only [hH, h0, sub_self]
  | insert τ0 A hτ0 ih =>
    intro s' hs' hdom'
    have hcond := (hdom s').mp hdom'
    set V : Set ℂ := {z | 0 < 1 + z.im / X.ttV e x τ0} with hVdef
    have hVo : IsOpen V := isOpen_lt continuous_const (by fun_prop)
    have hVc : Convex ℝ V := by
      intro z hz w hw a b ha hb hab
      simp only [hVdef, Set.mem_setOf_eq] at hz hw ⊢
      have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
      have h1 : 1 + (a * z.im + b * w.im) / X.ttV e x τ0 =
          a * (1 + z.im / X.ttV e x τ0) + b * (1 + w.im / X.ttV e x τ0) := by
        linear_combination (-1 : ℝ) * hab
      rw [him, h1]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hz) (mul_nonneg hb hw.le)
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using hw
    have hreal0 : ∀ y : ℝ, (y : ℂ) ∈ V := by intro y; simp [hVdef]
    have hmaps : ∀ z ∈ V, X.flowV e (Function.update s' τ0 z) x ∈ X.dom := by
      intro z hz
      rw [hdom]
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa [hVdef] using hz
      · simpa [Function.update_of_ne h] using hcond τ
    have hu : ∀ τ, Differentiable ℂ (fun z : ℂ => Function.update s' τ0 z τ) := by
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa using differentiable_id
      · simpa [Function.update_of_ne h] using differentiable_const (s' τ)
    have hdiff : DifferentiableOn ℂ (fun z => H (Function.update s' τ0 z)) V := by
      have h1 : DifferentiableOn ℂ (fun z => G (X.flowV e (Function.update s' τ0 z) x)) V :=
        hG.comp (d4l4_diff_flow X e x s' τ0).differentiableOn (fun z hz => hmaps z hz)
      have hsum : Differentiable ℂ (fun z : ℂ => ∑ τ, m τ * Function.update s' τ0 z τ) := by
        intro z
        exact DifferentiableAt.fun_sum fun τ _ => ((hu τ) z).const_mul (m τ)
      have h2 : Differentiable ℂ (fun z : ℂ =>
          cexp (4 * Real.pi * I * ∑ τ, m τ * Function.update s' τ0 z τ) * G x) :=
        ((hsum.const_mul (4 * Real.pi * I)).cexp).mul_const (G x)
      exact h1.sub h2.differentiableOn
    have han : AnalyticOnNhd ℂ (fun z => H (Function.update s' τ0 z)) V :=
      hdiff.analyticOnNhd hVo

    have hzero_real : ∀ y : ℝ, H (Function.update s' τ0 (y : ℂ)) = 0 := by
      intro y
      apply ih
      · intro τ hτ
        by_cases h : τ = τ0
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact hs' τ (by simp [h, hτ])
      · exact hmaps _ (hreal0 y)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H (Function.update s' τ0 z) = 0 := by
      have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        have h3 := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) (fun y hy => by simpa using hy)
        rwa [Complex.ofReal_zero] at h3
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero_real))
    have h0V : (0 : ℂ) ∈ V := by simp [hVdef]
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hVc.isPreconnected h0V hfreq
    have h4 := hEq (hcond τ0)
    simpa using h4

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

lemma dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)

lemma quad_AtA {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]

lemma posDef_of_bound {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    change x i ≠ 0 at hi
    have : 0 < ‖x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end
