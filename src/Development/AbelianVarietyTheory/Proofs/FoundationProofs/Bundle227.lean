module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle005
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PullNorm

noncomputable def coordLin (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordLin_apply (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (z : VC D N N') : coordLin D T b j z = coordB D T b j z := rfl

theorem coordB_sum (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h1 : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (u : Fin r → ℂ) (k : Fin r) :
    coordB D T b k (∑ j, u j • embV D T (b j)) = u k := by

  rw [← coordLin_apply, map_sum]
  simp [coordLin_apply, h1]

theorem parseval (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (z : VC D N N') (h2 : z = ∑ j, coordB D T b j z • embV D T (b j)) :
    (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (z τ i j)) = ((∑ k, ‖coordB D T b k z‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ c : Fin r → ℂ,
      (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) ((∑ k, c k • embV D T (b k)) τ i j))
        = ∑ k, coordB D T b k z * (starRingEnd ℂ) (c k) := by
    intro c

    simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul, embV]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h := key fun k => coordB D T b k z
  rw [← h2] at h
  rw [h]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _

theorem gaussianWeight_thetaTranslate_normSq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) (ω z : ℂ) :
    ‖U1 Λ ω g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)
      = ‖g (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h2 : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem normSq_pullB : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  intro D T N N' r b hΛ h1 h2 g _ hg
  let eC : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    { LinearMap.pi (fun j => coordLin D T b j) with
      invFun := fun u => ∑ j, u j • embV D T (b j)
      left_inv := fun z => (h2 z).symm
      right_inv := fun u => funext fun k => coordB_sum D T b h1 u k }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := eC.restrictScalars ℝ
  have he : ∀ z k, e z k = coordB D T b k z := fun _ _ => rfl
  have hA : ∀ x, x ∈ LaB D T b ↔ ∀ k, e x k ∈ T.abelian₂ := by
    intro x
    constructor
    · intro hx k
      unfold LaB at hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, j, rfl⟩ := hy
        rw [he, ← coordLin_apply, map_smul, coordLin_apply, h1]
        split_ifs
        · simpa using hw
        · simp
      | zero => simp
      | add y z _ _ hy hz => simpa only [map_add, Pi.add_apply] using add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
    · intro hx
      rw [h2 x]
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hx j, j, rfl⟩
  haveI i1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have main := GlobalTheory.LatticeMean.mean_prod_eq_pow T.abelian₂ hΛ
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area T.abelian₂))
    (fun ω hω z => by rw [← gaussianWeight_thetaTranslate_normSq, hg ω hω]) (VC D N N') MeasureTheory.volume r e (LaB D T b) hA
  unfold normSq nrm1Sq
  simp only []
  rw [← main]
  congr 1
  funext z
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Hf, parseval D T b z (h2 z), Complex.div_ofReal_re,
    Complex.ofReal_re, pullB, norm_prod, ← Finset.prod_pow]
  simp only [he]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

end GlobalTheory.PullNorm
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

def yAt (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 *
    (lamC g.lam (wpD g.abelian₂ v) / 2 - g.C.s * (lamC g.lam (wpF g.abelian₂ v) - g.C.r) - g.C.t)

theorem norm_natCast_le (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem sm_add {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem sm_sub {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add ha (by rwa [norm_neg])

theorem it_add {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)

theorem it_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem sm_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hb

theorem sm_mul' {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact sm_mul hb ha

theorem disc_small (W : WeierstrassCurve ℂ_[p]) (x y : ℂ_[p]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (hx : ‖x‖ ≤ 1) (he : W.toAffine.Equation x y) (hy : ‖2 * y + W.a₁ * x + W.a₃‖ < 1)
    (hx' : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1) : ‖W.Δ‖ < 1 := by
  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨1, x, 0, y⟩
  have hΔ : (C • W).Δ = W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; simp [C]
  rw [WeierstrassCurve.Affine.equation_iff] at he
  have e1 : (C • W).a₁ = W.a₁ := by simp [C, WeierstrassCurve.variableChange_a₁]
  have e2 : (C • W).a₂ = W.a₂ + 3 * x := by simp [C, WeierstrassCurve.variableChange_a₂]
  have e3 : (C • W).a₃ = 2 * y + W.a₁ * x + W.a₃ := by
    simp [C, WeierstrassCurve.variableChange_a₃]; ring
  have e4 : (C • W).a₄ = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp [C, WeierstrassCurve.variableChange_a₄]; ring
  have e6 : (C • W).a₆ = 0 := by
    simp [C, WeierstrassCurve.variableChange_a₆]; linear_combination -he
  rw [← hΔ]
  have A1 : ‖(C • W).a₁‖ ≤ 1 := e1 ▸ h1
  have A2 : ‖(C • W).a₂‖ ≤ 1 := by
    rw [e2]; exact it_add h2 (it_mul (by simpa using norm_natCast_le (p := p) 3) hx)
  have A3 : ‖(C • W).a₃‖ < 1 := e3 ▸ hy
  have A4 : ‖(C • W).a₄‖ < 1 := e4 ▸ hx'
  set V := C • W
  have n4 : ‖(4 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 4
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have n8 : ‖(8 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 8
  have n27 : ‖(27 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 27
  have n9 : ‖(9 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 9
  have B2 : ‖V.b₂‖ ≤ 1 := by
    rw [WeierstrassCurve.b₂]; exact it_add (by rw [sq]; exact it_mul A1 A1) (it_mul n4 A2)
  have B4 : ‖V.b₄‖ < 1 := by
    rw [WeierstrassCurve.b₄]; exact sm_add (sm_mul n2 A4) (sm_mul A1 A3)
  have B6 : ‖V.b₆‖ < 1 := by
    rw [WeierstrassCurve.b₆, e6, mul_zero, add_zero, sq]; exact sm_mul A3.le A3
  have BetaSesquilinearity : ‖V.b₈‖ < 1 := by
    rw [WeierstrassCurve.b₈, e6]
    simp only [mul_zero, add_zero]
    refine sm_sub (sm_add (sm_sub (by norm_num) (sm_mul (it_mul A1 A3.le) A4))
      (sm_mul A2 (by rw [sq]; exact sm_mul A3.le A3))) (by rw [sq]; exact sm_mul A4.le A4)
  rw [WeierstrassCurve.Δ]
  refine sm_add (sm_sub (sm_sub ?_ (sm_mul n8 (by rw [show V.b₄ ^ 3 = V.b₄ * V.b₄ * V.b₄ by ring]; exact sm_mul (it_mul B4.le B4.le) B4)))
    (sm_mul n27 (by rw [sq]; exact sm_mul B6.le B6))) (sm_mul (it_mul (it_mul n9 B2) B4.le) B6)
  rw [neg_mul]
  rw [norm_neg]; exact sm_mul (by rw [sq]; exact it_mul B2 B2) BetaSesquilinearity

end GlobalTheory.ThetaPar
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.LatticeInvariants

lemma tsum_subtype_congr {p q : ℂ → Prop} (f : ℂ → ℂ) (h : ∀ w, f w ≠ 0 → (p w ↔ q w)) :
    ∑' w : {w // p w}, f w = ∑' w : {w // q w}, f w := by
  refine (tsum_subtype {w | p w} f).trans (Eq.trans ?_ (tsum_subtype {w | q w} f).symm)
  congr with w
  by_cases h0 : f w = 0
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h w h0]

lemma eisG_eq_tsum (Λ : AddSubgroup ℂ) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = ∑' w : Λ, ((w : ℂ) ^ (2 * k))⁻¹ := by
  simp only [eisG, one_div]
  refine tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0) (q := fun w ↦ w ∈ Λ)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w hw ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rintro rfl
  simp [hk] at hw

section

variable {L : PeriodPair} {Λ : AddSubgroup ℂ} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
include h

lemma eisG_eq_G {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  rw [eisG_eq_tsum Λ hk]
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w _ ↦ h w

lemma g2_eq : g2 Λ = L.g₂ := by rw [g2, eisG_eq_G h two_ne_zero]; rfl

lemma lattice_invariant_g3_eq : g3 Λ = L.g₃ := by rw [g3, eisG_eq_G h three_ne_zero]; rfl

lemma wpD_eq (z : ℂ) : wpD Λ z = L.derivWeierstrassP z := by
  rw [wpD, PeriodPair.derivWeierstrassP, neg_mul, ← tsum_mul_left]
  simp only [mul_one_div]
  congr 1
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ 2 / (z - w) ^ 3) fun w _ ↦ h w

lemma wpF_eq (z : ℂ) : wpF Λ z = L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, wpF, add_comm]
  congr 1
  · refine Eq.trans (tsum_congr fun w ↦ ?_) (tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0)
      (q := fun w ↦ w ∈ L.lattice)
      (fun w ↦ if w = 0 then 0 else 1 / (z - w) ^ 2 - 1 / w ^ 2) fun w hw ↦ ?_)
    · rw [if_neg w.2.2]
    · have : w ≠ 0 := by rintro rfl; simp at hw
      simp [h, this]
  · simp

lemma area_eq : area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  refine IsLeast.csInf_eq ⟨⟨?_, L.ω₂, (h _).2 L.ω₂_mem_lattice, L.ω₁, (h _).2 L.ω₁_mem_lattice,
    by rw [mul_comm]⟩, ?_⟩
  · rw [abs_pos]
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₁)
    obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₂)
    have e : (starRingEnd ℂ (m * L.ω₁ + n * L.ω₂) * (p * L.ω₁ + q * L.ω₂)).im =
        (n * p - m * q : ℤ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
      simp
      ring
    rw [e, abs_mul] at ha ⊢
    have h1 : (n * p - m * q : ℤ) ≠ 0 := by
      intro h0
      simp [h0] at ha
    have h2 : (1 : ℝ) ≤ |((n * p - m * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact le_mul_of_one_le_left (abs_nonneg _) h2

end

lemma discrete_of_eisG_ne_zero {Λ : AddSubgroup ℂ} {k : ℕ} (hk : k ≠ 0) (h : eisG Λ k ≠ 0) :
    DiscreteTopology Λ := by
  rw [eisG_eq_tsum Λ hk] at h
  have hs : Summable fun w : Λ ↦ ((w : ℂ) ^ (2 * k))⁻¹ := by
    by_contra hs
    exact h (tsum_eq_zero_of_not_summable hs)
  have hf : {w : Λ | ¬ ‖((w : ℂ) ^ (2 * k))⁻¹‖ < 1}.Finite :=
    Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually_lt_const one_pos)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ?_
  have ho : IsOpen {w : Λ | ‖(w : ℂ)‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  convert ho.sdiff hf.isClosed using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_not]
  constructor
  · rintro rfl
    simp [hk]
  · rintro ⟨h1, h2⟩
    by_contra h0
    have h3 : 0 < ‖(w : ℂ)‖ := by simpa using h0
    rw [norm_inv, norm_pow] at h2
    exact absurd h2 (not_lt.2 ((one_le_inv₀ (by positivity)).2 (pow_le_one₀ h3.le h1.le)))

lemma eisG_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ) (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = (a ^ (2 * k))⁻¹ * (2 * riemannZeta (2 * k : ℕ)) := by
  rw [eisG_eq_tsum Λ hk]
  rcases eq_or_ne a 0 with rfl | h0
  · have : ∀ w : Λ, (w : ℂ) = 0 := fun w ↦ by simpa [eq_comm] using h w w.2
    simp [this, hk]
  let e : ℤ → Λ := fun m ↦ ⟨m • a, Λ.zsmul_mem ha m⟩
  have he : Function.Bijective e := ⟨fun m n hmn ↦ by simpa [e, h0] using hmn,
    fun w ↦ (h w w.2).imp fun m hm ↦ Subtype.ext hm⟩
  rw [← (Equiv.ofBijective e he).tsum_eq,
    two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) (even_two_mul k), ← tsum_mul_left]
  congr with m
  simp [e, mul_pow]

lemma discr_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ)
    (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w) : TaylorLogMetric.discr Λ = 0 := by
  have h6 : riemannZeta 6 = Real.pi ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [TaylorLogMetric.discr, g2, g3, eisG_of_cyclic ha h two_ne_zero, eisG_of_cyclic ha h three_ne_zero]
  norm_num only [riemannZeta_four, h6]
  simp only [← inv_pow]
  ring

lemma exists_periodPair_of_discr_ne_zero {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  have hd : DiscreteTopology Λ := by
    by_cases h2 : eisG Λ 2 = 0
    · refine discrete_of_eisG_ne_zero three_ne_zero fun h3 ↦ h ?_
      simp [TaylorLogMetric.discr, g2, g3, h2, h3]
    · exact discrete_of_eisG_ne_zero two_ne_zero h2
  let M : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule Λ
  have hM : DiscreteTopology M := hd
  by_cases hs : Submodule.span ℝ (M : Set ℂ) = ⊤
  · have hZ : IsZLattice ℝ M := ⟨hs⟩
    let b := Module.finBasisOfFinrankEq ℤ M ((ZLattice.rank ℝ M).trans Complex.finrank_real_complex)
    have hi := (b.ofZLatticeBasis ℝ M).linearIndependent
    have e : ⇑(b.ofZLatticeBasis ℝ M) = ![(b 0 : ℂ), b 1] := by
      ext i
      fin_cases i <;> simp
    refine ⟨⟨b 0, b 1, e ▸ hi⟩, fun z ↦ ?_⟩
    change z ∈ M ↔ z ∈ Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)}
    rw [← Matrix.range_cons_cons_empty _ _ ![], ← e, b.ofZLatticeBasis_span ℝ M]
  · have h1 : Module.finrank ℤ M ≤ 1 := by
      have e := Real.finrank_eq_int_finrank_of_discrete (s := (M : Set ℂ))
        (by rw [Submodule.span_eq]; exact hM)
      rw [Set.finrank, Set.finrank, Submodule.span_eq] at e
      have := Submodule.finrank_lt hs
      rw [Complex.finrank_real_complex] at this
      omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
    exact absurd (discr_of_cyclic (a := v) v.2 fun w hw ↦
      (hv ⟨w, hw⟩).imp fun m hm ↦ congrArg Subtype.val hm) h

lemma exists_periodPair_of_invariants {a b : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  let L := periodPairOfTau τ
  have h1 := g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_periodPairOfTau τ)
  have h0 := g₂_cube_sub_g₃_sq_ne_zero L
  rw [modularJ_def, hτ, div_eq_div_iff h0 h] at h1
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq h0 h (by linear_combination h1 / 1728)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  refine ⟨scalePeriods L c hc0, ?_, ?_⟩
  · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
  · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp

theorem invariants_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  intro L Λ h
  have hΔ : TaylorLogMetric.discr Λ ≠ 0 := by
    rw [TaylorLogMetric.discr, g2_eq h, lattice_invariant_g3_eq h]
    exact g₂_cube_sub_g₃_sq_ne_zero L
  refine ⟨g2_eq h, lattice_invariant_g3_eq h, hΔ, area_eq h, fun z _ ↦ ⟨wpF_eq h z, wpD_eq h z⟩,
    fun Λ' h2 h3 ↦ ?_, fun a b ↦ exists_periodPair_of_invariants⟩
  obtain ⟨L', h'⟩ := exists_periodPair_of_discr_ne_zero (Λ := Λ')
    (by rwa [TaylorLogMetric.discr, h2, h3])
  rw [g2_eq h, g2_eq h'] at h2
  rw [lattice_invariant_g3_eq h, lattice_invariant_g3_eq h'] at h3
  ext z
  rw [h, h', lattice_eq_of_g₂_eq_of_g₃_eq h2 h3]

end GlobalTheory.LatticeInvariants
end
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
end
