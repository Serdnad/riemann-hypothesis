module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR

open PositivityTheory.Rg.Sw

variable {n : ℕ}

abbrev E (n : ℕ) := Fin n → Fin n → ℝ

def uM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • herm y)⁻¹

def vM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • herm y)⁻¹

def dP (y : E n) : ℝ := (1 + herm y * herm y).det.re

def evUV (s : ℂ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  MvPolynomial.eval (fun k => if k.1 then vM s y k.2.1 k.2.2 else uM s y k.2.1 k.2.2) R

def cls (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q * evUV s R y

def vkl (k l : Fin n) : Fin n → Fin n → ℂ := fun a b =>
  (if a = k ∧ b = l then (1 + Complex.I) / 2 else 0) + (if a = l ∧ b = k then (1 - Complex.I) / 2 else 0)

def dirC (f : E n → ℂ) (w : Fin n → Fin n → ℂ) (y : E n) : ℂ :=
  fderiv ℝ f y (fun a b => (w a b).re) + Complex.I * fderiv ℝ f y (fun a b => (w a b).im)

def Dkl (k l : Fin n) (f : E n → ℂ) : E n → ℂ := dirC f (vkl k l)

def Delta (f : E n → ℂ) : E n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f

def chr (t : ℝ) (β : E n) (y : E n) : ℂ := Complex.exp (-(Complex.I * t * ∑ a, ∑ b, β a b * y a b))

def Gauss : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c t P (herm y) = cls ((t / c : ℝ) : ℂ) 0 (Finset.univ.filter fun a => ε a = true).card
        (Finset.univ.filter fun a => ε a = false).card R y

def ClsBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (z : ℂ),
    ContDiff ℝ (⊤ : ℕ∞) (cls s z p q R) ∧ ∀ L : List (Fin n × Fin n), ∃ C : ℝ, ∀ y,
      ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) (cls s z p q R) y‖ ≤ C * (dP y) ^ (-(z.re + (p + q : ℝ) / 2))

def ClsGain : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    ∃ (J : ℕ) (a : Fin J → Polynomial ℂ) (G : Fin J → E n → ℂ), (∀ j, Continuous (G j)) ∧
      (∃ C : ℝ, ∀ j y, ‖G j y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2)) ∧
      ∀ z y, (Delta^[N] (cls s z p q R)) y = ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j, (a j).eval z * G j y

def IBP : Prop :=
  ∀ (n : ℕ) (f : E n → ℂ) (t : ℝ) (β : E n), ContDiff ℝ (⊤ : ℕ∞) f → t ≠ 0 → (herm β).det ≠ 0 →
    (∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) →
    ∫ y, f y * chr t β y = (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ * ∫ y, Delta f y * chr t β y

def Integr : Prop :=
  ∀ (n : ℕ), (∃ c : ℝ, 0 < c ∧ ∀ y : E n, c * (1 + ∑ a, ∑ b, y a b ^ 2) ≤ dP y) ∧
    ∀ σ : ℝ, (n : ℝ) ^ 2 / 2 < σ → Integrable fun y : E n => (dP y) ^ (-σ)

def Dens : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ (P : PX m n) (N : ℕ),
    (n : ℝ) ^ 2 < (m + N : ℕ) →
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 →
        ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β =
          ((herm β).det ^ N)⁻¹ * ((-1) ^ n / ((-(Complex.I * t)) ^ n)) ^ N *
            ∫ y, (Delta^[N] (fun y => secN ε c t P (herm y))) y * chr t β y

def WRSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 → ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
        (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
          Integrable (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
          W z = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
        W 0 = ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β

end PositivityTheory.Rg.Sw.WR
end
end

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def Amat (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * t * sgn ε a) • bᵀ

def IntegP : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable fun x : Fin m → Fin n → ℂ => evX P x * gs c x

def Wick : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ (M : PX m n) (a : Fin m) (i : Fin n),
      secN ε c t (X (a, i, true) * M) b = ∑ j, (Amat ε c t b a)⁻¹ j i * secN ε c t (pderiv (a, j, false) M) b

def Rot : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k, k.2.2 = true → d k = 0) → d ≠ 0 →
      secN ε c t (monomial d 1) b = 0

def Base : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    secN ε c t 1 b = ∏ a, ((Real.pi : ℂ) ^ n / (Amat ε c t b a).det)

end PositivityTheory.Rg.Sw.WR.G
end
end

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ent (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE.toContinuousLinearMap).comp (ent k.1 k.2.1) else ent k.1 k.2.1

theorem ent_apply (a : Fin m) (i : Fin n) (v : Fin m → Fin n → ℂ) : ent a i v = v a i := rfl

theorem crd_apply (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem evX_pderiv_mul_X (p : PX m n) (k b : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    evX (pderiv b (p * X k)) x = evX (pderiv b p) x * crd k x + evX p x * (if k = b then 1 else 0) := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : k = b
  · subst h; simp [evX_eq]
  · simp [evX_eq, Pi.single_apply, h]

def dEv (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : evX (C a : PX m n) = fun _ => a := by funext y; simp [evX]
    rw [h]; refine (hasFDerivAt_const a x).congr_fderiv ?_
    simp [dEv, evX]
  | add p q hp hq =>
    have h : evX (p + q) = fun y => evX p y + evX q y := by funext y; simp [evX]
    rw [h]; refine (hp.add hq).congr_fderiv ?_
    unfold dEv; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]; congr 1; simp [evX]
  | mul_X p k hp =>
    have h : evX (p * X k) = fun y => evX p y * crd k y := by funext y; simp [evX_eq]
    rw [h]; refine (hp.mul (crd k).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul,
      Finset.sum_add_distrib]
    have e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    have e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e1, e2]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end
