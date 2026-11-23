module

import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorGroup
public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace CompactEntryBounds

open Matrix NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  apply GlobalTheory.FlagMahler.hermC_expand <;> assumption

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  rw [hermC_expand X τ γ u w]
  have h1 := hermC_expand X τ 1 u w
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  rw [h1]
  simp only [hγ, Matrix.one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y := by
  have hc : ∀ a, col (γ.map τ * Y) a = (γ.map τ) *ᵥ col Y a := fun a => by
    funext k
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [gram, Matrix.of_apply, hc, hermC_stab X hγ τ]

theorem inv_lact (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ Data.emb τ v =
      Y⁻¹ *ᵥ Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  have hinv : ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ =
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ) (map_one τ)]
  rw [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  exact (RingHom.map_mulVec τ _ v a).symm

private theorem gram_eq_transpose_mul_map_mul_fundamental_domains (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm Y = Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, Complex.star_def]
  exact Finset.sum_comm

theorem entry_bound {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  apply GlobalTheory.FlagMahler.entry_bound <;> assumption

theorem comp_le_Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y p := by
  unfold QuadraticLatticeForms.Qy
  have hc : ∀ τ' : X.Ψ, 0 ≤ X.c τ' := fun τ' => by unfold Data.c; positivity
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun a => ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) (fun a _ => by positivity)
          (Finset.mem_univ b)) (hc τ)
    _ ≤ _ := Finset.single_le_sum
          (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
          (fun τ' _ => mul_nonneg (hc τ') (by positivity)) (Finset.mem_univ τ)

theorem comb_bound (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) {ι : Type} [Fintype ι]
    (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have hcpos : 0 < X.c τ := by
    unfold Data.c
    have := (map_ne_zero τ.1).2 X.ξ0_ne
    positivity
  have hemb : Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • Data.emb τ.1 (f i) := by
    funext a

    simp [Data.emb, map_sum, Finset.sum_apply, Rat.smul_def, map_mul, map_ratCast]
  have hlin : ((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b =
      ∑ i, (q i : ℂ) * ((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b := by
    rw [hemb, Matrix.mulVec_sum, Finset.sum_apply]
    simp [Matrix.mulVec_smul]
  rw [hlin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hcpos]
    linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ - 1)]

def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}

theorem cont_gram' (τ : X.Ψ) : Continuous fun w : Frame X.Ψ r => gram τ.1 X.Gm (mat w τ) := by
  apply continuous_matrix
  intro a b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

theorem Kset_compact (R : ℝ) : IsCompact (Kset X R) := by
  have hcl : IsClosed (Kset X R) := by
    have : Kset X R = ⋂ τ : X.Ψ, ({w : Frame X.Ψ r | gram τ.1 X.Gm (mat w τ) =
        diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
        ⋂ a, ⋂ c, {w : Frame X.Ψ r | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [Kset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => (isClosed_eq (cont_gram' X τ) continuous_const).inter
      (isClosed_iInter fun a => isClosed_iInter fun c => isClosed_le (by fun_prop) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := max R 0)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun c =>
        ((hw τ).2 a c).trans (le_max_left _ _)

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det hg
  rw [gram_eq_transpose_mul_map_mul_fundamental_domains, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
    zero_mul, Matrix.det_diagonal] at h
  refine absurd h.symm (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  rw [ne_eq, Complex.ofReal_eq_zero]
  unfold sgn
  split_ifs <;> norm_num

theorem Kset_sub (R : ℝ) : Kset X R ⊆ X.dom := by
  intro w hw
  refine (X.mem_dom_iff w).2 fun τ => ?_
  have hg := (hw τ).1
  refine ⟨det_ne_of_gram X hg, fun i => ?_⟩
  have hd : dmin X.Gm w τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    rw [dmin, hg, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    exact Finset.prod_ne_zero_iff.2 fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.2 hne

end CompactEntryBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace RankOneBoostIsometries

open MajorantConjugateTransfer FlowMatrixMajorants

variable {r : ℕ} (X : Data E r) (τ : X.Ψ)

noncomputable def rk (p w : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i a => p i * ∑ b, τ.1 (X.Gm a b) * conj (w b)

theorem rk_mulVec (p w v : Fin r → ℂ) :
    Matrix.mulVec (rk X τ p w) v = hermC τ.1 X.Gm v w • p := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rk, Matrix.of_apply, hermC, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

noncomputable def boost (e f : Fin r → ℂ) (m σ : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (((σ - 1) / m : ℝ) : ℂ) • rk X τ e f + (((σ⁻¹ - 1) / m : ℝ) : ℂ) • rk X τ f e

theorem boost_mulVec (e f : Fin r → ℂ) (m σ : ℝ) (v : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) v =
      v + ((((σ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v f) • e +
        ((((σ⁻¹ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • f := by
  simp only [boost, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
    smul_smul]

section plane

variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)

include hm hee hff hef hfe

theorem boost_comp {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) (Matrix.mulVec (boost X τ e f m σ⁻¹) w) = w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, hee, hff, hef, hfe, inv_inv]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem boost_isom {σ : ℝ} (hσ : 0 < σ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (boost X τ e f m σ) u) (Matrix.mulVec (boost X τ e f m σ) v) =
      hermC τ.1 X.Gm u v := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hee, hff, hef, hfe, map_mul, Complex.conj_ofReal]
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v e, ← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v f]
  push_cast
  field_simp
  ring

end plane

end RankOneBoostIsometries

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem fourier_coefficients_of_vector_group (hL1 : UnipotentVectorGroup (E := E)) : FourierCoefficientProperties (E := E) := by
  intro r X u g hiso hg la G hGd hB hper χ
  classical
  obtain ⟨hadd, hH⟩ := hL1 r X u hiso
  have hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b) := fun b hb => (hH b hb).1
  have hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := fun b hb => (hH b hb).2.2.2.1
  have hex : ∃ ω, X.IsLZBasis g ω := FixedPointImaginarySpan.exists_basis X g hg
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = hex.choose := ⟨_, rfl⟩
  have hω : X.IsLZBasis g ω := hωdef ▸ hex.choose_spec
  have hfz : ∀ ψ x, X.fz u g ψ G x =
      if IsHermFam ψ ∧ X.IsFreqZ g ψ then Ich X u ω G ψ x else 0 := by
    intro ψ x
    unfold Data.fz
    rw [dite_eq_left hex, ← hωdef]
    rfl
  have hsum : ∀ x ∈ X.dom, Summable (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g ψ G x‖) →
      HasSum (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) (G x) := by
    intro x hx hs
    have hωh := herm_ω hω
    have hli := hω.2.2
    obtain ⟨c, hc⟩ : ∃ c : (Fin (4 * Fintype.card X.Ψ) → ℤ) → X.Ψ → Fin 2 → Fin 2 → ℂ,
        c = fun m => chiOf ω hωh hli rfl fun j => (m j : ℝ) := ⟨_, rfl⟩
    have hcm : ∀ m, c m = chiOf ω hωh hli rfl fun j => (m j : ℝ) := fun m => by rw [hc]
    have hc_inj : Function.Injective c := by
      intro m m' h
      rw [hcm, hcm] at h
      have h' := chiOf_inj ω hωh hli rfl h
      funext j
      exact_mod_cast congrFun h' j
    have hcfreq : ∀ m, IsHermFam (c m) ∧ X.IsFreqZ g (c m) := by
      intro m
      refine ⟨by rw [hcm]; exact chiOf_herm ω hωh hli rfl _, ?_⟩
      intro b hb
      obtain ⟨n, hn, -⟩ := hω.2.1 b hb
      refine ⟨∑ j, n j * m j, ?_⟩
      have hb' : b = ∑ j, ((n j : ℝ) : ℂ) • ω j := by
        rw [hn]
        simp only [Complex.ofReal_intCast]
      show 2 * pr (c m) b = _
      rw [hb', pr_sum, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp : 2 * pr (c m) (ω j) = (m j : ℝ) := by
        rw [hcm]
        exact chiOf_pair ω hωh hli rfl _ j
      calc 2 * ((n j : ℝ) * pr (c m) (ω j)) = (n j : ℝ) * (2 * pr (c m) (ω j)) := by ring
        _ = (n j : ℝ) * (m j : ℝ) := by rw [hp]
    obtain ⟨D, hD⟩ := I2.DimB.descend (fun t => G (X.Zb u (Bv ω t) x))
      (psi_cont hω hdomH hGd hx) (fun n t => psi_per hω hadd hdomH hper hx n t)
    have hcoef : ∀ m, X.fz u g (c m) G x = UnitAddTorus.mFourierCoeff D m := by
      intro m
      rw [hfz, if_pos (hcfreq m)]
      refine Ich_coeff (fun j => ?_) D hD
      show 2 * pr (c m) (ω j) = (m j : ℝ)
      rw [hcm]
      exact chiOf_pair ω hωh hli rfl _ j
    have hsupp : ∀ ψ ∉ Set.range c, X.fz u g ψ G x = 0 := by
      intro ψ hψ
      rw [hfz]
      split_ifs with h
      · exfalso
        apply hψ
        choose k hk using fun j => h.2 (ω j) (hω.1 j)
        refine ⟨k, ?_⟩
        rw [hcm]
        exact (chiOf_eq ω hωh hli rfl h.1 (m := fun j => (k j : ℝ)) hk).symm
      · rfl
    have hsm : Summable (UnitAddTorus.mFourierCoeff D) := by
      refine Summable.of_norm ((hs.comp_injective hc_inj).congr fun m => ?_)
      simp only [Function.comp, hcoef]
    have hG0 : D (I2.DimB.tproj 0) = G x := by
      rw [hD, Bv_zero, Zb_zero]
    have hF := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsm (I2.DimB.tproj 0)
    rw [hG0] at hF
    have hF' : HasSum (UnitAddTorus.mFourierCoeff D) (G x) := by
      simpa [I2.DimB.mF_tproj] using hF
    rw [← hc_inj.hasSum_iff hsupp]
    have hcomp : (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) ∘ c =
        UnitAddTorus.mFourierCoeff D := funext fun m => hcoef m
    rw [hcomp]
    exact hF'
  by_cases hχ : IsHermFam χ ∧ X.IsFreqZ g χ
  · have hfe : X.fz u g χ G = Ich X u ω G χ := funext fun x => by rw [hfz, if_pos hχ]
    have hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k := fun j => hχ.2 (ω j) (hω.1 j)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact Ich_diff hω hdomH hGd χ
    · intro x hx b hb
      rw [hfe]
      exact Ich_rmul la hB hω hdomH χ hx hb
    · intro b hb x hx
      rw [hfe]
      exact Ich_Zb hω hadd hdomH hGd hper hfreq hb hx
    · intro x hx M hM
      rw [pnorm_eq, hfe]
      exact Ich_bound hω hunit la χ x hM
  · have hfe : X.fz u g χ G = fun _ => 0 := funext fun x => by rw [hfz, if_neg hχ]
    have hh0 : IsHermFam (0 : X.Ψ → Fin 2 → Fin 2 → ℂ) := by
      have h := th_herm (0 : X.Ψ → Fin 2 → Fin 2 → ℝ)
      rwa [th_zero] at h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact differentiableOn_const 0
    · intro x hx b hb
      rw [hfe]
      simp
    · intro b hb x hx
      rw [hfe]
      simp
    · intro x hx M hM
      have h0 := hM 0 hh0
      rw [Zb_zero, pnorm_eq] at h0
      rw [pnorm_eq, hfe]
      simp only [norm_zero, zero_mul]
      exact (mul_nonneg (norm_nonneg _) (fac_nonneg X la x)).trans h0

theorem fourier_coefficients_holds : FourierCoefficientProperties (E := E) :=
  fourier_coefficients_of_vector_group unipotent_vector_group

end ReciprocityTheory.ChartRestriction.G.FD
end
