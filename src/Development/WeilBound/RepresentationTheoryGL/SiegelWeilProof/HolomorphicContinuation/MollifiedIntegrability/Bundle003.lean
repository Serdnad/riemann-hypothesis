module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseB
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.MeasureTheory.Integral.Pi
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def FD (L : List (Fin n × Fin n)) (f : E n → ℂ) : E n → ℂ := L.foldr (fun kl g => Dkl kl.1 kl.2 g) f

theorem FD_cons (kl : Fin n × Fin n) (L : List (Fin n × Fin n)) (f : E n → ℂ) :
    FD (kl :: L) f = Dkl kl.1 kl.2 (FD L f) := rfl

theorem FD_append (L L' : List (Fin n × Fin n)) (f : E n → ℂ) : FD (L ++ L') f = FD L (FD L' f) := by
  simp [FD, List.foldr_append]

theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirC f w) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).re)) := h1.clm_apply contDiff_const
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).im)) := h1.clm_apply contDiff_const
  exact ha.add (contDiff_const.mul hb)

theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

theorem contDiff_FD {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (FD L f) := by
  induction L with
  | nil => exact hf
  | cons kl L ih => exact contDiff_Dkl ih _ _

theorem differentiable_of_top {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem Dkl_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Differentiable ℝ (F i))
    (k l : Fin n) : Dkl k l (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * Dkl k l (F i) y := by
  funext y
  unfold Dkl dirC
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]
  have e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y :=
    fun i hi => fderiv_const_mul ((hF i hi) y) (c i)
  rw [Finset.sum_congr rfl e]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem FD_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by
  induction L with
  | nil => rfl
  | cons kl L ih =>
    rw [FD_cons, ih]
    exact Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _

def Ls (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (k, σ k)

theorem Delta_eq (f : E n → ℂ) :
    Delta f = fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * FD (Ls σ) f y := by
  funext y
  simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD, Ls, List.foldr_map]

def Good (f : E n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L f y‖ ≤ h y

theorem good_FD {f : E n → ℂ} (hf : Good f) (L : List (Fin n × Fin n)) : Good (FD L f) := by
  refine ⟨contDiff_FD hf.1 L, fun L' => ?_⟩
  rw [← FD_append]
  exact hf.2 _

theorem good_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Good (F i)) :
    Good (fun y => ∑ i ∈ s, c i * F i y) := by
  refine ⟨?_, fun L => ?_⟩
  · exact ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1
  · rw [FD_sum s c F (fun i hi => (hF i hi).1) L]
    have : ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y := fun i hi => (hF i hi).2 L
    choose! h hint hb using this
    refine ⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, MeasureTheory.integrable_finsetSum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)

theorem good_Delta {f : E n → ℂ} (hf : Good f) : Good (Delta f) := by
  rw [Delta_eq]
  exact good_sum _ _ _ fun σ _ => good_FD hf _

theorem good_iter {f : E n → ℂ} (hf : Good f) (k : ℕ) : Good (Delta^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact good_Delta ih

theorem ibp_iter (hIBP : IBP) {f : E n → ℂ} (hf : Good f) (t : ℝ) (β : E n) (ht : t ≠ 0) (hβ : (herm β).det ≠ 0)
    (N : ℕ) : ∫ y, f y * chr t β y =
      ((-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹) ^ N * ∫ y, (Delta^[N] f) y * chr t β y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

abbrev MC (n : ℕ) := Fin n → Fin n → ℂ

def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0

def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)

def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}

def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R

def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y

def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)

end PositivityTheory.Rg.Sw.WR.Z
end
end

section

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im

def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b

def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)

def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det

def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)

def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)

def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)

def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))

end PositivityTheory.Rg.Sw.WR.D
end
end

section

noncomputable section

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

def Twist : Prop :=
  ∀ (n : ℕ) (H : E n → ℂ), ContDiff ℝ (⊤ : ℕ∞) H → ∀ N : ℕ, ∃ G : ℕ → E n → ℂ,
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ ∀ (z : ℂ) (y : E n),
      (Delta^[N] (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y)) y =
        ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * G j y

def Lagr : Prop :=
  ∀ D : ℕ, ∃ C : ℝ, ∀ (c : ℕ → ℂ) (B : ℝ), (∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * c j‖ ≤ B) →
    ∀ j ≤ D, ‖c j‖ ≤ C * B

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section

noncomputable section

open MeasureTheory Complex Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GB

def sgnR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by
  unfold sgn sgnR; split_ifs <;> simp

theorem evX_Qb (ε : Fin m → Bool) (bb : Bool) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qb ε bb i j) x = ∑ a ∈ Finset.univ.filter (fun a => ε a = bb), star (x a i) * x a j := by
  simp [evX, Qb]

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp

theorem trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem herm_transpose (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : bᵀ.IsHermitian := by
  ext i j
  have := congrFun (congrFun hb j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]

end GB

open GB in
theorem base : Base := by
  intro m n ε c t hc b hb
  unfold secN
  have hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) =
      ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j) := by
    intro x
    have h1 : evX (1 : PX m n) x = 1 := by simp [evX]
    rw [h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]
  have e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a := by
    rw [sgn_eq]; push_cast; ring
  rw [e]
  rfl

end PositivityTheory.Rg.Sw.WR.G
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)

def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F

def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F

def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R

def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}

def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}

def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M

def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)

def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))

def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b

end PositivityTheory.Rg.Sw.WR.K.GB
end
end
