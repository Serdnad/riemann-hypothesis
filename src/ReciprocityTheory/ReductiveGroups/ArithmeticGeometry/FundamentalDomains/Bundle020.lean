module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem Data.fj_flow_real (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (hbdd : ∃ C, ∀ x ∈ X.dom, X.pnorm la P x ≤ C)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * X.fj la ξ ν P x := by
  classical
  obtain ⟨hΛ, hξ0, -⟩ : ξ ∈ X.Λ ∧ herm X.Gm ξ ξ = 0 ∧ ξ ≠ 0 := hξ
  unfold Data.fj
  by_cases hc : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k
  swap
  · rw [if_neg hc, if_neg hc, mul_zero]
  rw [if_pos hc, if_pos hc]
  by_cases hD : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤
  swap
  · rw [dite_eq_right hD, dite_eq_right hD, mul_zero]
  rw [dite_eq_left hD, dite_eq_left hD]
  have hFD : IsAddFundamentalDomain (X.periods la) hD.choose volume := hD.choose_spec.2.1

  set F : (X.Ψ → ℝ) → ℂ := fun t => P (X.flow ξ (fun τ => (t τ : ℂ)) x) *
    cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) with hF
  have hsum : ∀ a b : X.Ψ → ℝ, ∑ τ, (ν τ : ℂ) * (((a + b) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * a τ + ∑ τ, (ν τ : ℂ) * b τ := by
    intro a b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

  have hFper : ∀ p ∈ X.periods la, ∀ t, F (p + t) = F t := by
    intro p hp t
    simp only [hF]
    have hfl : (fun τ => (((p + t) τ : ℝ) : ℂ)) = cR X p + (fun τ => (t τ : ℂ)) := by
      funext τ
      simp only [cR, Pi.add_apply, Complex.ofReal_add]
    have hdom : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom :=
      flow_real_mem_dom (X := X) hξ0 t x hx
    rw [hfl, ← flow_flow (X := X) hξ0, sec_periodic (X := X) la P hP hΛ hξ0 hp _ hdom]
    obtain ⟨k, hk⟩ := hc p hp
    have h1 : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * p τ) = 1 := by
      have hk' : ∑ τ, (ν τ : ℂ) * p τ = (k : ℂ) / 2 := by
        have h2 := congrArg (fun y : ℝ => (y : ℂ)) hk
        push_cast at h2
        linear_combination h2 / 2
      rw [hk', show -(4 * Real.pi * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    rw [hsum p t, mul_add, Complex.exp_add, h1, one_mul]

  have hstep : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * F (s + t) := by
    intro t
    have hfl : (fun τ => (t τ : ℂ)) + (fun τ => (s τ : ℂ)) = fun τ => (((s + t) τ : ℝ) : ℂ) := by
      funext τ
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
    rw [flow_flow (X := X) hξ0, hfl]
    simp only [hF]
    rw [hsum s t]
    have he : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) *
          cexp (-(4 * Real.pi * I) * (∑ τ, (ν τ : ℂ) * s τ + ∑ τ, (ν τ : ℂ) * t τ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hint : ∫ t in hD.choose, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * ∫ t in hD.choose, F t := by
    simp_rw [hstep]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact fd_translate (X.periods la) hD.choose hFD F hFper s
  rw [hint]
  ring

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Amat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun b' b => hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (Fin.castLE X.p0_le b'))

def Bmat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  Matrix.of fun a b => -hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (kap X.p0_le a))

lemma col_mul' (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = A *ᵥ col B a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma mulVec_eq_sum_col (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) : M *ᵥ w = ∑ c, w c • col M c := by
  funext k
  simp only [Matrix.mulVec, dotProduct, col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ ↦ mul_comm _ _

lemma yvec_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      h1 τ *ᵥ ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) := by
  simp only [col_mul', Matrix.mulVec_sum, Matrix.mulVec_smul]

private lemma hermC_sum_smul_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ}
    (c : Fin m → ℂ) (y : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) v = ∑ b, c b * hermC τ G (y b) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

lemma Pos_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Pos X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ b', ‖(Amat X h1 z0 x0 τ *ᵥ u) b'‖ ^ 2 := by
  unfold Pos
  refine Finset.sum_congr rfl fun b' _ ↦ ?_
  have h : (Amat X h1 z0 x0 τ *ᵥ u) b' = ∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (Fin.castLE X.p0_le b')) := by
    simp only [Matrix.mulVec, dotProduct, Amat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h]

lemma Neg_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Neg X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ a, ‖(Bmat X h1 z0 x0 τ *ᵥ u) a‖ ^ 2 := by
  unfold PositiveSpanMatrices.Neg
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h : (Bmat X h1 z0 x0 τ *ᵥ u) a = -∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (kap X.p0_le a)) := by
    simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h, norm_neg]

lemma colW_expand (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) {x0 : Frame X.Ψ r}
    (hortho : X.IsOrtho x0) (τ : X.Ψ) (hdet0 : (mat x0 τ).det ≠ 0) (b : Fin X.p0) :
    col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      ∑ b', Amat X h1 z0 x0 τ b' b • col (mat x0 τ) (Fin.castLE X.p0_le b') +
        ∑ a, Bmat X h1 z0 x0 τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  set y := col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hy
  set α := (mat x0 τ)⁻¹ *ᵥ y with hα
  have hyα : y = ∑ c, α c • col (mat x0 τ) c := by
    rw [← mulVec_eq_sum_col, hα, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), Matrix.one_mulVec]
  have hcd : ∀ c d, hermC τ.1 X.Gm (col (mat x0 τ) c) (col (mat x0 τ) d) =
      if c = d then ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) else 0 := by
    intro c d
    have := congrFun (congrFun (hortho τ) c) d
    simpa [gram, Matrix.diagonal_apply] using this
  have hh : ∀ d, hermC τ.1 X.Gm y (col (mat x0 τ) d) = α d * ((sgn X.p0 (d : ℕ) : ℝ) : ℂ) := by
    intro d
    rw [hyα, hermC_sum_smul_left']
    simp only [hcd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  rw [hyα, sum_split X.p0_le]
  congr 1
  · refine Finset.sum_congr rfl fun b' _ ↦ ?_
    congr 1
    simp only [Amat, Matrix.of_apply]
    rw [← hy, hh]
    have hb' := b'.isLt
    simp [sgn, hb']
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    simp only [Bmat, Matrix.of_apply]
    rw [← hy, hh, show sgn X.p0 (kap X.p0_le a : ℕ) = -1 by simp [sgn, kap]]
    push_cast
    ring

lemma lowBlock_castLE (Z : X.Coord) (τ : X.Ψ) (b' b : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le b') (Fin.castLE X.p0_le b) = if b' = b then 1 else 0 := by
  have hb' := b'.isLt
  simp only [Data.lowBlock, Matrix.of_apply, Fin.castLE_inj, Fin.coe_castLE]
  rw [dite_eq_right (by omega)]
  simp

lemma lowBlock_kap (Z : X.Coord) (τ : X.Ψ) (a : Fin (r - X.p0)) (b : Fin X.p0) :
    X.lowBlock Z τ (kap X.p0_le a) (Fin.castLE X.p0_le b) = Z τ a b := by
  simp only [Data.lowBlock, Matrix.of_apply, if_neg (kap_ne_castLE X.p0_le a b), zero_add]
  rw [dite_eq_left ⟨by simp [kap], by simp [b.isLt]⟩]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [kap])) (Fin.ext (by simp))

lemma colZ (x0 : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (b : Fin X.p0) :
    col (mat (X.xZ x0 Z) τ) (Fin.castLE X.p0_le b) =
      col (mat x0 τ) (Fin.castLE X.p0_le b) + ∑ a, Z τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  have hm : mat (X.xZ x0 Z) τ = mat x0 τ * X.lowBlock Z τ := rfl
  have hc : ∀ c k, col (X.lowBlock Z τ) c k = X.lowBlock Z τ k c := fun _ _ ↦ rfl
  rw [hm, col_mul', mulVec_eq_sum_col, sum_split X.p0_le]
  simp only [hc, lowBlock_castLE, lowBlock_kap, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace HermitianLatticeMaps

open Matrix NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ty (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)

noncomputable def mulQ (α : E) : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (α • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars ℚ

theorem mulQ_apply (α : E) (v : Fin r → E) : mulQ α v = α • v := rfl

noncomputable def hL (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm X.Gm x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def hR (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm X.Gm x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem coe_expand (f : Basis ι ℤ X.Λ) (v : X.Λ) :
    (v : Fin r → E) = ∑ i, f.repr v i • (f i : Fin r → E) := by
  first
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       rfl)

variable (f f' : Basis ι ℤ X.Λ)

noncomputable def phi : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (RealPlaceEmbeddings.qb X f).constr ℚ fun i => (f' i : Fin r → E)

theorem phi_f (i : ι) : phi X f f' (f i : Fin r → E) = f' i := by
  first
    | (rw [← RealPlaceEmbeddings.qb_apply X f i]; unfold phi; rw [Basis.constr_basis])

theorem phi_zsum (n : ι → ℤ) :
    phi X f f' (∑ i, n i • (f i : Fin r → E)) = ∑ i, n i • (f' i : Fin r → E) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, phi_f]

theorem phi_mem {x : Fin r → E} (hx : x ∈ X.Λ) : phi X f f' x ∈ X.Λ := by
  have e : x = ∑ i, f.repr ⟨x, hx⟩ i • (f i : Fin r → E) := coe_expand X f ⟨x, hx⟩
  rw [e, phi_zsum]
  exact Submodule.sum_mem _ fun i _ => zsmul_mem (f' i).2 _

theorem phi_phi (x : Fin r → E) : phi X f' f (phi X f f' x) = x := by
  have e : (phi X f' f).comp (phi X f f') = LinearMap.id := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f, LinearMap.id_apply]
  exact LinearMap.congr_fun e x

theorem smul_coe (ω : 𝓞 E) (v : X.Λ) : ((ω • v : X.Λ) : Fin r → E) = (ω : E) • (v : Fin r → E) := by
  first
    | rfl

variable {f f'}

theorem phi_omega (h : ty X f = ty X f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 := congrArg Prod.snd h
  have hk : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j =
      f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun h2 k) i) j
  have e1 := coe_expand X f (RingOfIntegers.basis E k • f i)
  have e2 := coe_expand X f' (RingOfIntegers.basis E k • f' i)
  rw [smul_coe] at e1 e2
  rw [e1, phi_zsum, e2]
  simp only [hk]

theorem phi_smul (h : ty X f = ty X f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have key : ∀ i, phi X f f' (α • (f i : Fin r → E)) = α • (f' i : Fin r → E) := by
    intro i
    have hα := (NumberField.integralBasis E).sum_repr α
    rw [← hα]

    simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, NumberField.integralBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact phi_omega X h k i
  have e : (phi X f f').comp (mulQ α) = (mulQ α).comp (phi X f f') := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply, key, phi_f]
  have := LinearMap.congr_fun e v
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply] at this

theorem phi_herm (h : ty X f = ty X f') (x y : Fin r → E) :
    herm X.Gm (phi X f f' x) (phi X f f' y) = herm X.Gm x y := by
  have h1 := congrArg Prod.fst h
  have hb : ∀ i j, herm X.Gm (f' i : Fin r → E) (f' j) = herm X.Gm (f i : Fin r → E) (f j) :=
    fun i j => (congrFun (congrFun h1 i) j).symm
  have s1 : ∀ i y, herm X.Gm (phi X f f' (f i)) (phi X f f' y) =
      herm X.Gm (f i : Fin r → E) y := by
    intro i y
    have e : (hR X (phi X f f' (f i))).comp (phi X f f') = hR X (f i) := by
      refine (RealPlaceEmbeddings.qb X f).ext fun j => ?_
      rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f]
      exact hb i j
    exact LinearMap.congr_fun e y
  have e2 : (hL X (phi X f f' y)).comp (phi X f f') = hL X y := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply]
    exact s1 i y
  exact LinearMap.congr_fun e2 x

noncomputable def phiE (h : ty X f = ty X f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := phi_smul X h

theorem exists_gl (h : ty X f = ty X f') :
    ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : ty X f' = ty X f := h.symm
  have hc : (phiE X h).comp (phiE X h') = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f' f v
  have hc' : (phiE X h').comp (phiE X h) = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f f' v
  have hMM : LinearMap.toMatrix' (phiE X h) * LinearMap.toMatrix' (phiE X h') = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have hMM' : LinearMap.toMatrix' (phiE X h') * LinearMap.toMatrix' (phiE X h) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  have hv : ∀ v, LinearMap.toMatrix' (phiE X h) *ᵥ v = phi X f f' v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h) v
  have hv' : ∀ v, LinearMap.toMatrix' (phiE X h') *ᵥ v = phi X f' f v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h') v
  refine ⟨⟨LinearMap.toMatrix' (phiE X h), LinearMap.toMatrix' (phiE X h'), hMM, hMM'⟩,
    ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · show herm X.Gm (LinearMap.toMatrix' (phiE X h) *ᵥ x) (LinearMap.toMatrix' (phiE X h) *ᵥ y) = _
    rw [hv, hv, phi_herm X h]
  · show x ∈ X.Λ ↔ LinearMap.toMatrix' (phiE X h) *ᵥ x ∈ X.Λ
    rw [hv]
    refine ⟨phi_mem X f f', fun hx => ?_⟩
    rw [← phi_phi X f f' x]
    exact phi_mem X f' f hx
  · show LinearMap.toMatrix' (phiE X h) *ᵥ _ = _
    rw [hv, phi_f]
  · show LinearMap.toMatrix' (phiE X h') *ᵥ v = _
    rw [hv', phi, Basis.constr_apply_fintype]
    simp only [Basis.equivFun_apply]

end HermitianLatticeMaps

end ReciprocityTheory.ChartRestriction.G.FD
end
