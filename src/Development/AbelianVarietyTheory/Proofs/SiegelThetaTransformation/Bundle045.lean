module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.ThetaHol

theorem exists_corner {κ ι : Type} [Fintype κ] [Fintype ι] (τ : Matrix ι ι ℂ) (S : ℝ)
    (x : Matrix κ ι ℚ) : ∃ s : κ → ι → Bool, ∀ ζ : κ → ι → ℂ, ‖ζ‖ ≤ S →
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ ≤
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ fun i => (if s k i then -S else S : ℝ) * I)))‖ := by
  refine ⟨fun k i => decide (0 ≤ x k i), fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum, Complex.add_im,
    Complex.mul_im, dotProduct, qv, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one,
    Complex.re_ofNat, Complex.im_ofNat, decide_eq_true_eq]
  refine mul_le_mul_of_nonneg_left (neg_le_neg (Finset.sum_le_sum fun k _ => ?_)) Real.pi_pos.le
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
  have h1 : |(ζ k i).im| ≤ S := (Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm (ζ k) i).trans ((norm_le_pi_norm ζ k).trans hζ))
  have h2 := abs_le.mp h1
  split_ifs with h
  · have : (0 : ℝ) ≤ (x k i : ℝ) := by exact_mod_cast h
    nlinarith
  · have : (x k i : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    nlinarith

theorem differentiable_thS {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) :
    Differentiable ℂ (thS φ τ) := by
  intro ζ₀
  let F : Matrix κ ι ℚ → (κ → ι → ℂ) → ℂ := fun x ζ => φ x *
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  let S : ℝ := ‖ζ₀‖ + 2
  let cor : (κ → ι → Bool) → κ → ι → ℂ := fun s k i => ((if s k i then -S else S : ℝ) : ℂ) * I
  choose s hs using fun x : Matrix κ ι ℚ => exists_corner τ S x
  have hFd : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [F, dotProduct]
    fun_prop
  have hbd : ∀ x, ∀ z : κ → ι → ℂ, ‖z‖ ≤ S → ‖F x z‖ ≤ ‖F x (cor (s x))‖ := by
    intro x z hz
    simp only [F, norm_mul]
    exact mul_le_mul_of_nonneg_left (hs x z hz) (norm_nonneg _)
  have hsum : Summable fun x => ‖F x (cor (s x))‖ := by
    have hfin : Summable fun x => ∑ t : κ → ι → Bool, ‖F x (cor t)‖ :=
      summable_sum fun t _ => SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ (cor t)
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hfin
    exact Finset.single_le_sum (f := fun t => ‖F x (cor t)‖) (fun t _ => norm_nonneg _)
      (Finset.mem_univ (s x))
  have hder : ∀ x, ∀ ζ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1),
      ‖fderiv ℂ (F x) ζ‖ ≤ 2 * ‖F x (cor (s x))‖ := by
    intro x ζ hζ
    have h := GlobalTheory.SCV.norm_fderiv_le_of_ball (f := F x) (c := ζ) (r := 1)
      (M := ‖F x (cor (s x))‖) one_pos (hFd x).differentiableOn (fun z hz => hbd x z (by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_ball, dist_zero_right] at hζ
        have := norm_sub_norm_le z ζ
        simp only [S]
        linarith))
    simpa using h
  have h0 : ζ₀ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have key := hasFDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun x ζ _ => (hFd x ζ).hasFDerivAt) hder h0
    (SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ₀).of_norm h0
  exact key.differentiableAt

theorem differentiable_thA {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) {φ : TF n g} (hφ : IsSB φ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Differentiable ℂ (thA X bas idx φ x) := by
  have hτ := UnAct.tauMat_mem idx hs hx
  have hlin : Differentiable ℂ fun z : Fin n → Fin g → ℂ => fun k => hMat X bas idx x *ᵥ z k := by
    refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hth := (differentiable_thS hφ hτ).comp hlin
  have hq : Differentiable ℂ fun z : Fin n → Fin g → ℂ => ∑ k, (hMat X bas idx x *ᵥ z k) ⬝ᵥ
      imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z k) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  unfold thA
  exact ((hq.const_mul _).cexp.const_mul _).mul hth

end GlobalTheory.SW.ThetaHol

namespace GlobalTheory.SW

theorem theta_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn c c' φ hφ P hP
  obtain ⟨m, a, b, t, ht⟩ := (GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries E r X g q0 hr bas idx n hs hn).2 φ hφ
  have hH := Harm.isHarmonic_of_mem_rowHighest hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun x => ∑ j, t j * thFr X hr bas idx n
        (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x) X.dom :=
      DifferentiableOn.fun_sum fun j _ => (differentiableOn_thFr idx hs hr n _ _ hH).const_mul (t j)
    exact hd.congr fun x hx => ht P x hx
  · intro x hx u hu
    have hxu := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hu
    rw [ht P _ hxu, ht P x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [thFr_rmul idx hr _ _ hs hP hx hu]
    ring
  · intro γ hγ x hx
    unfold thP
    rw [(wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hx]
  · intro x hx
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiable (ThetaHol.differentiable_thA idx hs hφ hx) _

end GlobalTheory.SW
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShVac

theorem le_sup_of_coprime {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} {s m : ℕ}
    (h : s.Coprime m) (hB : ∀ y ∈ A, s • y ∈ B) (hC : ∀ y ∈ A, m • y ∈ C) :
    A ≤ (A ⊓ B) ⊔ (A ⊓ C) := by
  intro y hy
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : y = a • s • y + b • m • y := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact AddSubgroup.add_mem_sup
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hB y hy⟩) _)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hC y hy⟩) _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

omit [IsCMField E] in
theorem nsmul_tens {Λ Λ' : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, ∀ u ∈ L, k • vecMulVec v u ∈ tens Λ' L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L' := by
  have : tens Λ L ≤ (tens Λ' L').comap (nsmulAddMonoidHom k) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact h v hv u hu
  exact fun y hy => this hy

omit [IsCMField E] in
theorem nsmul_tens_left {Λ Λ' : Lt E n} {L : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, (k : E) • v ∈ Λ') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨_, h v hv, u, hu, by
    ext i j; simp [vecMulVec_apply, _root_.mul_assoc]⟩

omit [IsCMField E] in
theorem nsmul_tens_right {Λ : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ u ∈ L, (k : 𝓞 E) • u ∈ L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ L' :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨v, hv, _, h u hu, by
    rw [Nat.cast_smul_eq_nsmul]
    ext i j; simp [vecMulVec_apply, mul_left_comm]⟩

omit [IsCMField E] in
theorem relIndex_half {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L).toAddSubgroup.relIndex (L ⊓ L').toAddSubgroup ∧
    ∀ x ∈ L', x ∈ idq P Q L → x ∈ idq P Q L' := by
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have d (x : Fin r → E) : x = a • s • x + m • x := by
    rw [← mul_smul, ← add_smul, e, one_smul]
  constructor
  · refine Lev.relIndex_eq (fun x hx => hx.1) fun x (hx : x ∈ L) => ?_
    rw [d x]
    exact AddSubgroup.add_mem_sup ⟨L.smul_mem _ (L.smul_mem _ hx), L'.smul_mem _ (h x hx)⟩
      ⟨fun b _ => Submodule.smul_mem _ b (Submodule.smul_mem_smul hm hx), L.smul_mem _ hx⟩
  · intro x hx H b hb
    rw [d (b • x)]
    exact add_mem (Submodule.smul_mem _ _ (Lev.smul_map_mem LinearMap.id h (H b hb)))
      (Submodule.smul_mem_smul hm (L'.smul_mem _ hx))


omit [IsCMField E] in
theorem relIndex_shift {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') (h' : ∀ v ∈ L', s • v ∈ L) :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L').toAddSubgroup.relIndex L'.toAddSubgroup := by
  obtain ⟨h1, h2⟩ := relIndex_half (Q := Q) hs h
  obtain ⟨h3, h4⟩ := relIndex_half (Q := Q) hs h'
  rw [h1, h3, inf_comm L' L, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (idq P Q L').toAddSubgroup]
  congr 1
  ext x
  exact and_congr_left fun hx => ⟨h2 x hx.2, h4 x hx.1⟩

theorem eq_sqrt {k t : ℝ} (ht : 0 ≤ t) (h : k * t ^ 2 = 1) : t = √(k⁻¹) ∧ 0 < t := by
  refine ⟨?_, ht.lt_of_ne ?_⟩
  · rw [← eq_inv_of_mul_eq_one_right h, Real.sqrt_sq ht]
  · rintro rfl
    simp at h

theorem smul_eq_unitv {g : ℕ} {u : TF n g} (hu : IsSB u) (h1 : SW.ip u u = 1) {a : ℂ} (ha : 0 < ‖a‖) :
    a • u = ((‖a‖ : ℝ) : ℂ) • unitv (a • u) := by
  rw [unitv, TensVac.ip_smul_left _ hu (TensVac.sb_smul _ hu), TensVac.ip_smul_right _ hu hu, h1, _root_.mul_one,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq ha.le, smul_smul (_ : ℂ) (_ : ℂ)⁻¹,
    mul_inv_cancel₀ (by exact_mod_cast ha.ne'), one_smul]

theorem shift_vac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n M, 0 < s Λ ∧ projA X bas D.w (tens Λ (D.sh L)) (projA X bas D.w (tens Λ L) v) = (t * (s Λ : ℂ)) • unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
  intro E _ _ _ r X g bas idx n hs hn D M _ hM v₀ hv₀
  have one {Λ} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
    obtain ⟨h1, h2, s, h3, -, h4⟩ := h
    exact ⟨h1, h2, s, h3, Nat.coprime_one_right s, h4⟩
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hsh {L} (hL : L ∈ D.lats) : SelfD X (D.sh L) := Lev.selfD_idq D.ne_bot D.proper D.cop hL.1
  have vac := TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have ten := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have pp := GlobalTheory.Dict.ProjProj.proj_proj E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have hΛ₀ : X.Λ ∈ D.lats := ⟨Lev.selfD_of_sympl hs, 1, Lev.cop_one, fun v hv => by simpa using hv,
    fun v hv => by simpa using hv⟩
  have key : ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v →
      ‖SW.ip v (v₀ L)‖ = √((((D.sh X.Λ).toAddSubgroup.relIndex X.Λ.toAddSubgroup ^ n : ℕ) : ℝ)⁻¹) ∧
        0 < ‖SW.ip v (v₀ L)‖ := by
    intro L hL v hv
    have h := (vac L hL.1 1 _ hstd).2.2.2 _ (hsh hL) _ hstd v _ hv (hv₀ L hL)
    rw [((ten L hL.1 1 _ hstd).2.2.2.2.1 _ (hsh hL)).1] at h
    obtain ⟨-, s, h1, h2, h3⟩ := hL
    rw [Level.sh, relIndex_shift h1.of_mul_right_left h2 h3] at h
    exact eq_sqrt (norm_nonneg _) h
  refine ⟨_, fun Λ => √(((Λ.toAddSubgroup.relIndex (stdL E n).toAddSubgroup ^ r : ℕ) : ℝ)⁻¹), ?_,
    fun L hL v hv => ⟨_, (key L hL v hv).1, fun Λ hΛ => ?_⟩⟩
  · obtain ⟨v, hv⟩ := (vac _ hΛ₀.1 1 _ hstd).1
    exact (key _ hΛ₀ v hv).1 ▸ (key _ hΛ₀ v hv).2
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := vac _ (hsh hL) 1 _ (one hΛ)
  have h := (vac _ (hsh hL) 1 _ hstd).2.2.2 _ (hsh hL) _ (one hΛ) _ u (hv₀ L hL) hu
  rw [(ten _ (hsh hL) 1 _ hstd).2.2.2.2.2 _ (one hΛ)] at h
  obtain ⟨h1, h2⟩ := eq_sqrt (norm_nonneg _) h
  simp only [← h1]
  refine ⟨h2, ?_⟩
  obtain ⟨s, -, hc, s1, s2⟩ := hΛ.2.2
  have hM' : (M : 𝓞 E) ∈ conjI D.𝔪 := Lev.mem_conjI.2 (by rwa [map_natCast])
  have e1 := pp L L _ hL.1 hL.1 (hsh hL) _ hstd _ (one hΛ) _ (one hΛ)
    (le_sup_of_coprime hc (nsmul_tens_left s1) (nsmul_tens_right fun x hx =>
      Lev.smul_le_idq _ _ _ (Submodule.smul_mem_smul hM hx))) v hv
  have e2 := pp L _ _ hL.1 (hsh hL) (hsh hL) _ hstd _ hstd _ (one hΛ)
    (le_sup_of_coprime hc.symm (nsmul_tens_right fun x hx => Submodule.smul_le_right (hx _ hM'))
      (nsmul_tens_left s2)) v hv
  have b₀ := (hv₀ L hL).1
  rw [e1, ← e2, (vac _ (hsh hL) 1 _ hstd).2.2.1 v hv.1 _ (hv₀ L hL), hp _ (TensVac.sb_smul _ b₀) u hu,
    hp _ b₀ u hu, TensVac.ip_smul_left _ b₀ hu.1, mul_smul, mul_smul, ← smul_eq_unitv hu.1 hu.2.1 h2]

end GlobalTheory.Dict.ShVac
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

private lemma mapL_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  simp

private lemma mapL_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (a b : GL (Fin r) E) (L : Lt E r) :
    mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [Matrix.mulVec_mulVec]

private lemma smul_left_cancel_of_ip_self_eq_one {n g : ℕ} {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) {a b : ℂ}
    (h : a • v = b • v) : a = b := by
  have ha := TensVac.ip_smul_left a hv hv
  have hb := TensVac.ip_smul_left b hv hv
  rw [h1, _root_.mul_one] at ha hb
  rw [← ha, ← hb, h]

theorem vac_multiplier_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  intro E _ _ _ r X g bas idx n hs hn D v₀ hvac mu hmu
  have hsd : SelfD X X.Λ := Lev.selfD_of_sympl hs
  have hlat : ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L ∈ D.lats := fun L hL ga hga =>
    Lev.mapL_mem_lats hsd hga hL
  have hred : ∀ ga ∈ D.grp, ∃ k : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k := by
    intro ga hga
    obtain ⟨-, k, hk, h⟩ := (Lev.mem_grp ga).mp hga
    exact ⟨⟨k, hk⟩, h⟩
  have hun : ∀ ga ∈ D.grp, IsUn X ga := fun ga hga => ((Lev.mem_grp ga).mp hga).1
  have hvsb : ∀ L ∈ D.lats, IsSB (v₀ L) := by
    intro L hL
    obtain ⟨h, -, -⟩ := hvac L hL
    exact h
  have hvone : ∀ L ∈ D.lats, ip (v₀ L) (v₀ L) = 1 := by
    intro L hL
    obtain ⟨-, h, -⟩ := hvac L hL
    exact h

  have hnorm : ∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1 := by
    intro ga hga L hL
    obtain ⟨k, hk⟩ := hred ga hga
    have hL' := hlat L hL ga hga
    have hip := ((wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ L) (hvsb L hL)).2.2.1
      (v₀ L) (hvsb L hL)).1
    rw [hmu ga hga L hL k hk, hvone L hL,
      TensVac.ip_smul_left _ (hvsb _ hL') (TensVac.sb_smul _ (hvsb _ hL')),
      TensVac.ip_smul_right _ (hvsb _ hL') (hvsb _ hL'), hvone _ hL', _root_.mul_one,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at hip
    have h2 : ‖mu ga L * ((D.lam k : ℂˣ) : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hip
    rw [norm_mul, Lev.norm_lam k, _root_.mul_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

  have hlam : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ k k' k'' : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k →
      D.Red (fun i => (ga' : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k' →
      D.Red (fun i => ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k'' →
      ((D.lam k'' : ℂˣ) : ℂ) = (D.lam k : ℂˣ) * (D.lam k' : ℂˣ) := by
    intro ga _ ga' _ k k' k'' hk hk' hk''
    let y0 : Matrix (Fin r) (Fin r) E := Matrix.of fun i => D.β i
    have hy : ∀ M : Matrix (Fin r) (Fin r) E, y0 * Mᵀ = Matrix.of fun i => M *ᵥ D.β i := by
      intro M
      ext i j
      simp [y0, Matrix.mul_apply, Matrix.mulVec, dotProduct, _root_.mul_comm]
    have e1 := Lev.dat_lin (le_refl r) hk'' y0
    have e2 := Lev.dat_lin (le_refl r) hk (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ)
    have e3 := Lev.dat_lin (le_refl r) hk' y0
    have hne : D.dat (le_refl r) (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ) ≠ 0 := by
      rw [hy]
      unfold SW.Level.dat
      split_ifs with hc
      · exact Units.ne_zero _
      · exact absurd ⟨⟨k', hk'⟩, fun j hj => absurd j.isLt (not_lt.mpr hj)⟩ hc
    have hd0 : D.dat (le_refl r) y0 ≠ 0 := by
      intro h0
      apply hne
      rw [e3, h0]
      simp
    have hm : y0 * ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ =
        y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ * (ga : Matrix (Fin r) (Fin r) E)ᵀ := by
      rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm, e2, e3] at e1
    apply mul_right_cancel₀ hd0
    rw [← e1]
    ring

  have hcoc : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats,
      mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
    intro ga hga ga' hga' L hL
    obtain ⟨k, hk⟩ := hred ga hga
    obtain ⟨k', hk'⟩ := hred ga' hga'
    have hgg : ga * ga' ∈ D.grp := Subgroup.mul_mem _ hga hga'
    obtain ⟨k'', hk''⟩ := hred _ hgg
    have hL' := hlat L hL ga' hga'
    have hL'' := hlat _ hL' ga hga
    have hcomp := (wG_laws E r X g bas idx n hs hn ga' (hun ga' hga') (v₀ L)
      (hvsb L hL)).2.2.2.2.2.1 ga (hun ga hga)
    have hsm := (wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ (mapL ga' L))
      (hvsb _ hL')).2.2.2.1 (mu ga' L * ((D.lam k' : ℂˣ) : ℂ))
    rw [hmu _ hgg L hL k'' hk'', hmu ga' hga' L hL k' hk', hsm, hmu ga hga _ hL' k hk, smul_smul,
      mapL_mul'] at hcomp
    have hc := smul_left_cancel_of_ip_self_eq_one (hvsb _ hL'') (hvone _ hL'') hcomp
    rw [hlam ga hga ga' hga' k k' k'' hk hk' hk''] at hc
    have hk0 : ((D.lam k : ℂˣ) : ℂ) * (D.lam k' : ℂˣ) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    apply mul_right_cancel₀ hk0
    linear_combination hc
  refine ⟨hnorm, ?_, hcoc⟩

  intro L hL
  have h1 := hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) L hL
  rw [_root_.mul_one, mapL_one'] at h1
  have hn1 := hnorm 1 (Subgroup.one_mem _) L hL
  have hne : mu 1 L ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  exact mul_left_cancel₀ hne (h1.symm.trans (_root_.mul_one _).symm)

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_even_reps_tensorLattice_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  first | exact @GlobalTheory.Dict.ZLat.exists_reps_sum | exact GlobalTheory.Dict.ZLat.exists_reps_sum | (intros; apply GlobalTheory.Dict.ZLat.exists_reps_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteAdelicLatticeTransport_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.Ker.isMov_laws | exact GlobalTheory.Ker.isMov_laws | (intros; apply GlobalTheory.Ker.isMov_laws <;> assumption)
end
