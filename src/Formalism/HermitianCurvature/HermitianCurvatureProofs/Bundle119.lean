module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.QuantumDeterminants

theorem hasDerivAt_normPow (z v : ℂ) (hz : z ≠ 0) (n : ℕ) :
    HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ n)
      ((n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2)) 0 := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hsq : HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ 2) (2 * (v * conj z).re) 0 := by
    have := hline.norm_sq
    simpa [Complex.inner] using this
  have h0 : (fun t : ℝ => ‖z + t • v‖ ^ 2) 0 ≠ 0 := by simpa using pow_ne_zero 2 hz'
  have hsqrt := hsq.sqrt h0
  have hn : (fun t : ℝ => √(‖z + t • v‖ ^ 2)) = fun t => ‖z + t • v‖ := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hsqrt
  have hv : (n : ℝ) * ‖z + (0 : ℝ) • v‖ ^ (n - 1) * (2 * (v * conj z).re / (2 * √(‖z + (0 : ℝ) • v‖ ^ 2))) =
      (n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2) := by
    simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _)]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have hp := (hsqrt.pow n).congr_deriv hv
  exact hp

theorem hasDerivAt_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    HasDerivAt (fun t : ℝ => ∏ a, ‖(c + t • (Pi.single l v : Fin r → ℂ)) a‖ ^ n a)
      ((n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2)) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun a (t : ℝ) => ‖c a + t • (Pi.single l v : Fin r → ℂ) a‖ ^ n a)
    (fun a _ => hasDerivAt_normPow (c a) ((Pi.single l v : Fin r → ℂ) a) (hc a) (n a))
  have hv : (∑ i, (∏ j ∈ Finset.univ.erase i, ‖c j + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) j‖ ^ n j) •
        ((n i : ℝ) * ‖c i‖ ^ n i * (((Pi.single l v : Fin r → ℂ) i * conj (c i)).re / ‖c i‖ ^ 2))) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, zero_smul, add_zero, smul_eq_mul]
      rw [← Finset.mul_prod_erase Finset.univ (fun a => ‖c a‖ ^ n a) (Finset.mem_univ l)]
      ring
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ l) h
  exact h.congr_deriv hv

theorem fderiv_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c ∧
    fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
  classical
  have hd : DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c := by
    have := HasFDerivAt.finsetProd (u := Finset.univ) (x := c)
      (g := fun a (x : Fin r → ℂ) => ‖x a‖ ^ n a)
      (fun a _ => (((differentiableAt_apply (𝕜 := ℝ) a c).norm ℂ (hc a)).pow (n a)).hasFDerivAt)
    exact this.differentiableAt
  refine ⟨hd, ?_⟩
  have hline : HasDerivAt (fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ)) (Pi.single l v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l v : Fin r → ℂ)).const_add c
  have hc0 : c + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) = c := by simp
  have h1 : HasDerivAt ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) ∘ fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ))
      (fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v)) 0 := by
    have hd' := hd.hasFDerivAt
    rw [← hc0] at hd'
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    rwa [hc0] at this
  exact h1.unique (hasDerivAt_prodPow r n c hc l v)

theorem gauge_scalar (z : ℂ) (hz : z ≠ 0) (m : ℕ) (P : ℝ) :
    z * ((1 / 2 : ℂ) * ((((m : ℝ) * P * ((1 * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ) -
      Complex.I * (((m : ℝ) * P * ((Complex.I * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ))) = (P : ℂ) * ((m : ℂ) / 2) := by
  have h1 : (1 * conj z).re = z.re := by simp
  have h2 : (Complex.I * conj z).re = z.im := by simp
  have hc : ((z.re : ℂ)) - Complex.I * (z.im : ℂ) = conj z := by apply Complex.ext <;> simp
  have hzz : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hN0 : (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [h1, h2]
  push_cast
  calc _ = ((m : ℂ) * P / 2) * (z * ((z.re : ℂ) - Complex.I * (z.im : ℂ))) / (‖z‖ : ℂ) ^ 2 := by ring
    _ = (P : ℂ) * ((m : ℂ) / 2) := by
      have hN1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [hc, hzz]; field_simp

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.GaugeNormPower

theorem gauge_positivity : PBN.GaugeP := by
  intro E _ _ r n H c hc hH l
  obtain ⟨hψ, hψ'⟩ := fderiv_prodPow r n c hc l 1
  obtain ⟨-, hψI⟩ := fderiv_prodPow r n c hc l Complex.I
  have hfun : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') =
      (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H := by
    funext c'; exact Complex.coe_smul _ _
  rw [hfun]
  have hD : ∀ w, fderiv ℝ ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H) c w =
      (∏ a, ‖c a‖ ^ n a) • fderiv ℝ H c w + fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c w • H c := by
    intro w
    rw [(hψ.hasFDerivAt.smul hH.hasFDerivAt).fderiv]
    simp
  have hs : c l * ((1 / 2 : ℂ) * (((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l 1) : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l Complex.I) : ℝ) : ℂ))) =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) * ((n l : ℂ) / 2) := by
    rw [hψ', hψI]
    exact gauge_scalar (c l) (hc l) (n l) _
  simp only [pOp, if_pos hc, wirt]
  rw [hD, hD]
  simp only [← Complex.coe_smul]
  linear_combination (norm := module) hs • H c

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Asm

def ggP (TT : ℝ) : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)

theorem gg_eval (TT : ℝ) (ζ : ℂ) : MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] (ggP TT) = gg TT ζ := by
  simp only [ggP, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, gg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.mul_conj]
  push_cast
  ring

theorem PS.congr {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) :
    PS TT g := by
  obtain ⟨m, p, hp⟩ := hf
  exact ⟨m, p, fun ζ hζ => by rw [h ζ hζ]; exact hp ζ hζ⟩

theorem PS.const (TT : ℝ) (a : ℂ) : PS TT (fun _ => a) :=
  ⟨0, MvPolynomial.C a, fun ζ _ => by simp⟩

theorem PS.mul {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * p', fun ζ hζ => ?_⟩
  rw [map_mul, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.add {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * ggP TT ^ m' + p' * ggP TT ^ m, fun ζ hζ => ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, gg_eval, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.sum {TT : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, PS TT (f i)) :
    PS TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PS.congr (PS.const TT 0) fun ζ _ => by simp
  | insert a s ha ih =>
    exact PS.congr (PS.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      fun ζ _ => by rw [Finset.sum_insert ha]

theorem PSV.apply {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f : ℂ → V} (hf : PSV TT f)
    (L : V →ₗ[ℂ] ℂ) : PS TT (fun ζ => L (f ζ)) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine PS.congr (PS.sum Finset.univ (fun i ζ => a i ζ * L (v i)) fun i _ => PS.mul (ha i) (PS.const TT _))
    fun ζ hζ => ?_

  rw [hf ζ hζ, map_sum]
  simp only [map_smul, smul_eq_mul]

end Asm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

section defs

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rc (Z : Q.Mx k r) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g

def wordR (w : List (Q.Mx k r)) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  w.foldr (fun Z h => Rc Z h) f

def dZV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 - Complex.I • fderiv ℝ f ζ Complex.I)

def dZbV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 + Complex.I • fderiv ℝ f ζ Complex.I)

end defs

def GLc (k r : ℕ) (Z : Q.Mx k r) : Prop :=
  Q.inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z) ∧ Q.inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)

def GWc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : Q.Mx k r) : Prop :=
  P.QrD.InLieW k r z (hpart1 (Hpk k r) Z) ∧ P.QrD.InLieW k r z (hpart2 (Hpk k r) Z)

def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) := {g | 0 < Q.GGl k r z z' g}

def mu0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r := NF.muZ k r (TheSec.theSection k r z z') ζ

def etaZ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ

def etaZb (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ

def RcLin : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
    ∀ (a : ℂ) (Z Z' : Q.Mx k r), GLc k r Z → GLc k r Z' → Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g

def RcSmooth : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f f' : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → Q.SmoothLev k r (Fin.last r) D f' → ∀ Z : Q.Mx k r, GLc k r Z →
      Q.SmoothLev k r (Fin.last r) D (Rc Z f) ∧
      (∀ (a : ℂ), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc Z (fun x => a • f x + f' x) g = a • Rc Z f g + Rc Z f' g) ∧
      ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E'), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
        Rc Z (fun x => L (f x)) g = L (Rc Z f g)

def RcComm : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ Z₁ Z₂ : Q.Mx k r, GLc k r Z₁ → GLc k r Z₂ →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc Z₁ (Rc Z₂ f) g - Rc Z₂ (Rc Z₁ f) g = Rc (Z₁ * Z₂ - Z₂ * Z₁) f g

def LeftCov : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)), IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) → inWb k r z →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z, ∀ g ∈ D, h * g ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g)) →
    ∀ μ ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ B : Q.Mx k r, GWc k r z B →
      GLc k r (μ⁻¹ * B * μ) ∧ Rc (μ⁻¹ * B * μ) F μ = (P.QrD.ecOp π B).comp (F μ)

def RightCov : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)), IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') → inWb k r z' →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z', ∀ g ∈ D, g * h ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h)) →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ A : Q.Mx k r, GWc k r z' A →
      GLc k r A ∧ Rc A F g = (F g).comp (P.QrD.ecOp π' A)

def SecDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
      GLc k r (etaZ k r z z' ζ) ∧ GLc k r (etaZb k r z z' ζ) ∧ (mu0 k r z z' ζ) ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F →
        Rc (etaZ k r z z' ζ) F (mu0 k r z z' ζ) = dZV (fun w => F (mu0 k r z z' w)) ζ ∧
        Rc (etaZb k r z z' ζ) F (mu0 k r z z' ζ) = dZbV (fun w => F (mu0 k r z z' w)) ζ

def Decomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ a b : Fin (k + 1), ∃ (n₁ n₂ : ℕ) (B₁ : Fin n₁ → Q.Mx k r) (b₁ : Fin n₁ → ℂ → ℂ) (B₂ : Fin n₂ → Q.Mx k r)
      (b₂ : Fin n₂ → ℂ → ℂ) (β₁ β₂ : ℂ → ℂ),
      (∀ t, GWc k r z' (B₁ t)) ∧ (∀ t, GWc k r z (B₂ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₁ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₂ t)) ∧
      PS (Tz k r z * Tz k r z') β₁ ∧ PS (Tz k r z * Tz k r z') β₂ ∧
      ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
        Matrix.single (wI k r a) (wI k r b) (1 : ℂ) =
          ∑ t, b₁ t ζ • B₁ t + (mu0 k r z z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * (mu0 k r z z' ζ) +
            β₁ ζ • etaZ k r z z' ζ + β₂ ζ • etaZb k r z z' ζ

def PSCalc : Prop :=
  ∀ (TT : ℝ), 0 < TT →
    (∀ c : ℂ, PS TT (fun _ => c)) ∧ PS TT id ∧ PS TT (fun ζ => conj ζ) ∧ PS TT (sig TT) ∧ PS TT (fun ζ => (gg TT ζ)⁻¹) ∧
    (∀ f g, PS TT f → PS TT g → PS TT (fun ζ => f ζ + g ζ) ∧ PS TT (fun ζ => f ζ * g ζ)) ∧
    (∀ f, PS TT f → PS TT (NF.dZ f) ∧ PS TT (NF.dZb f)) ∧
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'],
      (∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) ∧
      (∀ (a : ℂ → ℂ) (f : ℂ → V), PS TT a → PSV TT f → PSV TT (fun ζ => a ζ • f ζ)) ∧
      (∀ (L : V →ₗ[ℂ] V') (f : ℂ → V), PSV TT f → PSV TT (fun ζ => L (f ζ))) ∧
      (∀ (f : ℂ → V), PSV TT f → PSV TT (dZV f) ∧ PSV TT (dZbV f)) ∧
      (∀ v : V, PSV TT (fun _ => v))

def LowerUnipotentMatrixWords : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ Y : ℂ, ∃ (n : ℕ) (κ : Fin n → ℂ → ℂ) (w : Fin n → List (Q.Mx k r)),
      (∀ i, PS (Tz k r z * Tz k r z') (κ i)) ∧ (∀ i, ∀ Z ∈ w i, ∃ a b : Fin (k + 1), Z = Matrix.single (wI k r a) (wI k r b) 1) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
          Q.tL k r z z' (Fin.last r) Y 1 0 F (mu0 k r z z' ζ) = ∑ i, κ i ζ • wordR (w i) F (mu0 k r z z' ζ)

def WordPSV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ w : List (Q.Mx P.k P.r), (∀ Z ∈ w, GLc P.k P.r Z) →
        PSV P.TT (fun ζ => wordR w ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def WordPSVOfCut : Prop :=
  RcLin → RcSmooth → RcComm → LeftCov → RightCov → SecDeriv → Decomp → PSCalc → WordPSV

def CorePolyOfCut : Prop := LowerUnipotentMatrixWords → WordPSV → PSCalc → CorePoly

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem evenPart_poly (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    ∃ q : Polynomial ℂ, ∀ t s : ℂ, t ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![t, t, s] p + MvPolynomial.eval ![-t, -t, s] p = q.eval s := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rcases Nat.even_or_odd' (u 0 + u 1) with ⟨j, hj | hj⟩
    · refine ⟨Polynomial.C (2 * a) * (Polynomial.X ^ 2 + Polynomial.C c) ^ j * Polynomial.X ^ (u 2), fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [← pow_add, ← pow_add, hj, pow_mul, pow_mul, neg_sq, h]
      ring
    · refine ⟨0, fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_zero]
      rw [← pow_add, ← pow_add, hj, Odd.neg_pow ⟨j, rfl⟩]
      ring
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨q₁ + q₂, fun t s h => ?_⟩
    rw [map_add (f := _), map_add (f := _), Polynomial.eval_add, ← hq₁ t s h, ← hq₂ t s h]
    ring

theorem phase_extraction_holds : PhaseExtract := by
  intro TT f _ hPS hrot
  obtain ⟨m, p, hp⟩ := hPS
  obtain ⟨q, hq⟩ := evenPart_poly (TT : ℂ) p
  refine ⟨m, Polynomial.C (1 / 2) * q, fun ζ hζ => ?_⟩
  have hn : Complex.normSq ((‖ζ‖ : ℝ) : ℂ) = Complex.normSq ζ := by
    rw [Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]; ring
  have hn' : Complex.normSq (-((‖ζ‖ : ℝ) : ℂ)) = Complex.normSq ζ := by
    rw [Complex.normSq_neg, hn]
  have h1 : f ζ = f ((‖ζ‖ : ℝ) : ℂ) := by
    have := hrot (Complex.arg ζ) ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [← this]
    congr 1
    unfold rot
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have h2 : f ζ = f (-((‖ζ‖ : ℝ) : ℂ)) := by
    have := hrot Real.pi ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [h1, ← this]
    congr 1
    unfold rot
    rw [Complex.exp_pi_mul_I]; ring
  have e1 := hp ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
  have e2 := hp (-((‖ζ‖ : ℝ) : ℂ)) (by rw [hn']; exact hζ)
  have g1 : gg TT ((‖ζ‖ : ℝ) : ℂ) = gg TT ζ := by unfold gg; rw [hn]
  have g2 : gg TT (-((‖ζ‖ : ℝ) : ℂ)) = gg TT ζ := by unfold gg; rw [hn']
  have s1 : sig TT ((‖ζ‖ : ℝ) : ℂ) = sig TT ζ := by unfold sig; rw [hn]
  have s2 : sig TT (-((‖ζ‖ : ℝ) : ℂ)) = sig TT ζ := by unfold sig; rw [hn']
  rw [g1, s1, ← h1, Complex.conj_ofReal] at e1
  rw [g2, s2, ← h2, map_neg, Complex.conj_ofReal] at e2
  have hcurve : (((‖ζ‖ : ℝ) : ℂ)) ^ 2 = sig TT ζ ^ 2 + (TT : ℂ) := by
    unfold sig
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.ofReal_add,
      Complex.normSq_eq_norm_sq]
    congr 1; ring
  have := hq _ _ hcurve
  rw [← e1, ← e2] at this
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← this]
  ring

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end
