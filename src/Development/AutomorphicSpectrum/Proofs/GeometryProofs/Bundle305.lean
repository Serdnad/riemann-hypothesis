module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle208
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle301
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle213
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle254
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle296
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle255
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle277
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle077
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle303
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

theorem exists_pull_form {g g' : ℕ} (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm : Matrix (Fin g') (Fin g') ℂ) (hH : Hm.IsHermitian) :
    ∃ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian ∧ (∀ x y, x ⬝ᵥ Hb *ᵥ star y = ℓ x ⬝ᵥ Hm *ᵥ star (ℓ y)) ∧
      ∀ y, ℓ y = 0 → Hb *ᵥ star y = 0 := by
  set Lm := LinearMap.toMatrix' ℓ with hLm
  have h1 : ∀ x, Lm *ᵥ x = ℓ x := fun x => LinearMap.toMatrix'_mulVec ℓ x
  have h2 : ∀ y, (Lm.map star) *ᵥ star y = star (ℓ y) := fun y => by
    rw [← h1]
    ext i
    simp [Matrix.mulVec, dotProduct]
  have h3 : ∀ y, (Lmᵀ * Hm * Lm.map star) *ᵥ star y = Lmᵀ *ᵥ (Hm *ᵥ star (ℓ y)) := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨Lmᵀ * Hm * Lm.map star, ?_, fun x y => ?_, fun y hy => ?_⟩
  · have e1 : (Lm.map star)ᴴ = Lmᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Lmᵀ)ᴴ = Lm.map star := by ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, hH.eq, Matrix.mul_assoc]
  · rw [h3, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h1]
  · rw [h3, hy]
    simp

theorem eq_of_forall_exp {d e : ℝ} (h : ∀ N : ℕ, 0 < N →
    Complex.exp (-(2 * Real.pi * Complex.I) * (d : ℂ) / N) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / N)) :
    d = e := by
  obtain ⟨N, hN⟩ := exists_nat_gt |d - e|
  have hN0 : 0 < N + 1 := Nat.succ_pos N
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h (N + 1) hN0)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have h1 : ((d - e : ℝ) : ℂ) = (((-k * (N + 1 : ℕ) : ℤ) : ℝ) : ℂ) := by
    push_cast
    field_simp at hk
    push_cast at hk
    linear_combination -hk
  have h2 : d - e = ((-k * (N + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    simpa [sub_eq_zero] using h2
  have h3 : (N + 1 : ℝ) ≤ |d - e| := by
    rw [h2]
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast this
    push_cast
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    nlinarith [abs_nonneg (k : ℝ), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

theorem eq_zero_of_im_lattice {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) (p : Fin g → ℂ)
    (h : ∀ q ∈ Λ, (p ⬝ᵥ Hm *ᵥ star q).im = 0) : p = 0 := by
  have key : ∀ w : Fin g → ℂ, (p ⬝ᵥ Hm *ᵥ star w).im = 0 := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hfull]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => simp [star_add, Matrix.mulVec_add, dotProduct_add, hx, hy]
    | smul c x _ hx =>
      have e : star (c • x) = (c : ℂ) • star x := by
        ext i; simp
      rw [e, Matrix.mulVec_smul, dotProduct_smul]
      simp [hx]
  by_contra hp
  have h1 := hpos p hp
  have h2 := key (Complex.I • p)
  have e : star (Complex.I • p) = (-Complex.I) • star p := by
    ext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem abPart_principal_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ z)) ≫ (C.M.pt (Pi.single i 1)).left)) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₀, Λ, _, L, e, hρ0, hρ1, hlink⟩ := GlobalTheory.T.exists_log_period_family E H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₁, Cb, h1, h2, hL⟩ := GlobalTheory.T.log_period_limit n a C.g Λ L
  have hol : Flat.IsHolPts (Metric.ball 0 ρ₀) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  have hprin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB := by
    intro z hz P
    obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := GlobalTheory.T.exists_dvr_through_disc_point E H D l Xo σ n a C z hz
    have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
      rintro _ rfl P
      obtain ⟨m', -⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ tV C.t _ mV ℂ (spMap r) P
      exact GlobalTheory.T.polarized_abelian_part_principal E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
    refine key _ ?_ P
    rw [← hrf]
    show Spec.map (CommRingCat.ofHom (r.comp f)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ρ₀ * ρ₁, Real.pi * Cb, mul_pos hρ0 h1, by nlinarith, ?_⟩
  intro z hz
  obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, z = (ρ₀ : ℂ) • z' := by
    refine ⟨(ρ₀⁻¹ : ℂ) • z, ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      rw [inv_mul_lt_iff₀ hρ0]
      exact hz
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ0.ne'), one_smul]
  have hz1 : z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball h2 hz'
  have hb : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₀ := by
    rw [mem_ball_zero_iff] at hz1 ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    nlinarith
  have hb1 : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball hρ1 hb
  obtain ⟨ws, W, per, hws, hlim, hper, hfour, -, hsix⟩ := hL z' hz'
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.T.family_exp_log_cover_bound E H C.R C.t C.g n a C.M C.ψ ρ₀ e Λ L hρ0 hρ1 hol hlink z' hz1 ws W per hws hlim hper hfour
  intro P
  have hP := hprin _ hb1 P
  refine ⟨hP, ?_⟩
  intro Mz hMz x v c hv hc
  obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', rfl⟩ := hc
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
  have e1 : a' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v v' a' hv hv' ha'
  have e2 : b' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v w' b' hv hw' hb'
  obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
  obtain ⟨Hb, hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
  have hE : ∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = ((L.E x x' : ℤ) : ℝ) := by
    intro x x'
    rw [hH2]
    refine eq_of_forall_exp fun N hN => ?_
    have hw := hC N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N))) x x' hN rfl
    have := GlobalTheory.T.hol_unif_period_matrix_middle E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ (per x) (per x') hN
      (hA x) (hA x') hw
    rw [Units.val_mk0] at this
    have c : (((L.E x x' : ℤ) : ℝ) : ℂ) = ((L.E x x' : ℤ) : ℂ) := by push_cast; rfl
    rw [c]
    exact this.symm
  have hrad : ∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0 := by
    intro x hx
    refine hH3 _ (eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_)
    obtain ⟨y, hy, rfl⟩ := honto q hq
    obtain ⟨x', rfl⟩ := hB y hy
    rw [← hH2, hE, hx]
    simp
  subst e1 e2
  have hbd := (hsix Hb hH1 hE hrad x).2.1
  rw [hH2] at hbd
  have e3 : ((Real.pi : ℂ) * (ℓ x ⬝ᵥ Hm.mulVec (star (ℓ x)))).re = Real.pi * (ℓ x ⬝ᵥ Hm *ᵥ star (ℓ x)).re := by simp
  rw [e3, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hbd Real.pi_pos.le

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem one_le_logSize_lb {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : 1 ≤ logSize a z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logSize_smul_le_lb {n : ℕ} (a : ℕ) (c : ℂ) (hc : c ≠ 0) (z : Fin n → ℂ)
    (hz : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    logSize a (c • z) ≤ (1 + n * |Real.log ‖c‖|) * logSize a z := by
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖(c • z) i‖| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), (|Real.log ‖c‖| + |Real.log ‖z i‖|) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : z i ≠ 0 := hz i (Finset.mem_filter.mp hi).2
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hi')]
    exact abs_add_le _ _
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Finset.univ.filter (fun i : Fin n => i.val < a)).card : ℝ) ≤ n := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i : Fin n => i.val < a)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 : 0 ≤ |Real.log ‖c‖| := abs_nonneg _
  have h4 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h5 := mul_le_mul_of_nonneg_right h2 h3
  have h6 : 0 ≤ (n : ℝ) * |Real.log ‖c‖| * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    by positivity
  unfold logSize
  nlinarith

theorem hermForm_rows_lb {m g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (F : Matrix (Fin m) (Fin g) ℂ) (i j : Fin m) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (F i) (F j) = (F * Hm * F.conjTranspose) i j := by
  rw [Matrix.mul_assoc]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Pi.star_apply]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem hodgeGram_det_log_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∀ (m : ℕ) (u : Fin m → Fin C.g → C.R), LinearIndependent ℂ (fun i b => C.ψ 0 (u i b)) → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a ρ, ∀ v, C.IsVal z u v → (∃ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ) ∧ ∀ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ → ‖Γ.det‖ ≤ K ∧ 1 ≤ K * logSize a z ^ N * ‖Γ.det‖ := by
  intro E _ _ _ H D l Xo σ n a C h1 h2 m u hu
  obtain ⟨ρ, Λ, _, L, hρ, hρ1, hR⟩ := GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem E H D l Xo σ n a C h1 h2
  let F : (Fin n → ℂ) → Matrix (Fin m) (Fin C.g) ℂ := fun z => Matrix.of fun i b => C.ψ ((ρ : ℂ) • z) (u i b)
  have hFc : ContinuousAt F 0 := by
    refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun b => ?_
    have hd : DifferentiableOn ℂ (fun z => C.ψ z (u i b)) (Metric.ball 0 1) := C.hol.2 (u i b)
    have hc : ContinuousAt (fun z => C.ψ z (u i b)) ((ρ : ℂ) • (0 : Fin n → ℂ)) := by
      rw [smul_zero]
      exact hd.continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
    exact ContinuousAt.comp (f := fun z : Fin n → ℂ => (ρ : ℂ) • z) hc (continuous_const_smul _).continuousAt
  have hFr : (F 0).rank = m := by
    have : LinearIndependent ℂ (F 0).row := by
      have e : (F 0).row = fun i b => C.ψ 0 (u i b) := by
        funext i b
        simp [F, Matrix.row]
      rw [e]; exact hu
    simpa using this.rank_matrix
  obtain ⟨ρ', K, N, hρ', hρ'1, hB⟩ := GlobalTheory.CompanionTheory.Ar.Flat.logPeriods_subframe_det_bounds n a C.g Λ L m F hFc hFr
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set c : ℝ := 1 + n * |Real.log ‖(ρ : ℂ)⁻¹‖| with hcdef
  have hc1 : 1 ≤ c := le_add_of_nonneg_right (by positivity)
  refine ⟨ρ * ρ', K * Real.pi ^ m * c ^ N, N, mul_pos hρ hρ', mul_le_one₀ hρ1 hρ'.le hρ'1, ?_⟩
  intro z hz v hv
  obtain ⟨hz1, hz2⟩ := hz
  have hw1 : (ρ : ℂ)⁻¹ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    rw [mem_ball_zero_iff] at hz1 ⊢
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_lt_iff₀ hρ]
    exact hz1
  have hw2 : ∀ i : Fin n, i.val < a → ((ρ : ℂ)⁻¹ • z) i ≠ 0 := fun i hi =>
    mul_ne_zero (inv_ne_zero hρc) (hz2 i hi)
  have hwz : (ρ : ℂ) • (ρ : ℂ)⁻¹ • z = z := smul_inv_smul₀ hρc z
  have hRz := hR ((ρ : ℂ)⁻¹ • z) ⟨Metric.ball_subset_ball hρ'1 hw1, hw2⟩
  rw [hwz] at hRz
  obtain ⟨hB1, hB2⟩ := hB _ hw1 hw2
  have hG : ∀ Γ, IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ ↔
      Γ = (Real.pi : ℂ) • (F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose) := by
    intro Γ
    rw [hRz m u v Γ hv, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, ← hermForm_rows_lb]
    simp only [F, hwz]
    rfl
  refine ⟨⟨_, (hG _).mpr rfl⟩, fun Γ hΓ => ?_⟩
  rw [(hG Γ).mp hΓ, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hS := logSize_smul_le_lb a _ (inv_ne_zero hρc) z hz2
  rw [← hcdef] at hS
  change 1 ≤ K * logSize a ((ρ : ℂ)⁻¹ • z) ^ N * _ at hB2
  have hd0 := norm_nonneg (F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose).det
  generalize ‖(F ((ρ : ℂ)⁻¹ • z) * L.H ((ρ : ℂ)⁻¹ • z) * (F ((ρ : ℂ)⁻¹ • z)).conjTranspose).det‖ = d at hB1 hB2 hd0 ⊢
  have hs0 := one_le_logSize_lb a ((ρ : ℂ)⁻¹ • z)
  have hs1 := one_le_logSize_lb a z
  have hp : 1 ≤ Real.pi ^ m := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hcN : 1 ≤ c ^ N := one_le_pow₀ hc1
  have hpow : logSize a ((ρ : ℂ)⁻¹ • z) ^ N ≤ c ^ N * logSize a z ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hS N
  have hK : 0 ≤ K := hd0.trans hB1
  have hp0 : 0 ≤ Real.pi ^ m := by positivity
  constructor
  · calc Real.pi ^ m * d ≤ K * Real.pi ^ m * 1 := by nlinarith
      _ ≤ _ := by gcongr
  · calc 1 ≤ K * logSize a ((ρ : ℂ)⁻¹ • z) ^ N * d := hB2
      _ ≤ K * (c ^ N * logSize a z ^ N) * d := by gcongr
      _ = K * 1 * c ^ N * logSize a z ^ N * (1 * d) := by ring
      _ ≤ _ := by gcongr

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.comp_laws_model_root_bound : GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ R : ℝ, HodgeLe Or u (gauge Rd u * Rd.φ (evC h Z f)) R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe | exact GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.low_height_of_given : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTLow Xo c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.htLow | exact GlobalTheory.CompanionTheory.Ar.Plug.htLow | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.htLow <;> assumption)
end
