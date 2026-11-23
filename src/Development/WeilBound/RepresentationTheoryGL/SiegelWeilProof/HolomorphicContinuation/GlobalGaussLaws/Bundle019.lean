module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def aC (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  Matrix.fromBlocks (Matrix.diagonal fun j => Complex.exp (z * X j)) 0 0 (Matrix.diagonal fun j => Complex.exp (-(z * X j)))

def stripS (X : Fin n → ℝ) : Set ℂ := {z | ∀ j, |z.im * X j| < Real.pi / 4}

def ptZ (y : GR n) (X : Fin n → ℝ) (z : ℂ) (sgnI : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let M := mR y * aC X z
  (M.toBlocks₁₁ * (sgnI • 1) + M.toBlocks₁₂) * (M.toBlocks₂₁ * (sgnI • 1) + M.toBlocks₂₂)⁻¹

def jC (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) : ℂ :=
  let M := mR y * aC X z
  M.det ^ e * (M.toBlocks₂₁ * (Complex.I • 1) + M.toBlocks₂₂).det ^ (-(p : ℤ)) *
    (M.toBlocks₂₁ * ((-Complex.I) • 1) + M.toBlocks₂₂).det ^ (-(q : ℤ))

def gC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace)

def famC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

def DReal : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ s : ℝ, famC ε t c e y X s = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) (y * a s) (Complex.I • 1) *
      gZf ε t c (actZ (y * a s) (Complex.I • 1)) u

def DBound : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famC ε t c e y X z u) (stripS X)) ∧
    ContinuousOn (fun p : GR n × ℂ × (Fin m → Fin n → ℂ) => famC ε t c e p.1 X p.2.1 p.2.2) (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p ∈ N, p.2 ∈ stripS X → ∀ u, ‖famC ε t c e p.1 X p.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

def DCalc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ (s : ℝ) (r : ℕ) (u : Fin m → Fin n → ℂ),
      iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s = (Real.exp (s * (m : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j))) ∧
    ∀ (r : ℕ) (s : ℝ), Filter.Tendsto (fun h : ℝ => ∫ u : Fin m → Fin n → ℂ,
        ‖(iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) (s + h) - iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s) / h -
          iteratedDeriv (r + 1) (fun s' : ℝ => famC ε t c e 1 X s' u) s‖ ^ 2) (𝓝[≠] 0) (𝓝 0)

def DifferenceQuotientIsometryExchange : Prop :=
  ∀ (m n : ℕ) (T : ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (κ : ℝ), 0 < κ →
    (∀ f, IsSch f → IsSch (T f)) → (∀ f g, IsSch f → IsSch g → T (f - g) = T f - T g) →
    (∀ a f, IsSch f → T (fun u => a * f u) = fun u => a * T f u) →
    (∀ f, IsSch f → ∫ u, ‖T f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) →
    ∀ (G : ℝ → (Fin m → Fin n → ℂ) → ℂ) (G' E' : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ), (∀ s', IsSch (G s')) → IsSch G' →
      Continuous E' → Filter.Tendsto (fun h : ℝ => ∫ u, ‖(G (s + h) u - G s u) / h - G' u‖ ^ 2) (𝓝[≠] 0) (𝓝 0) →
      (∀ u, Filter.Tendsto (fun h : ℝ => (T (G (s + h)) u - T (G s) u) / h) (𝓝[≠] 0) (𝓝 (E' u))) → T G' = E'

def DHol : Prop :=
  GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure →
  ∀ (P : Type) [TopologicalSpace P] [FirstCountableTopology P] (U : Set ℂ), IsOpen U → ∀ φ : P → ℂ → Mx D V.rank n → ℂ,
    (∀ p z, z ∈ U → φ p z ∈ schwartzA θ V.rank n) → (∀ p x, DifferentiableOn ℂ (fun z => φ p z x) U) →
    (∀ x, ContinuousOn (fun pz : P × ℂ => φ pz.1 pz.2 x) (Set.univ ×ˢ U)) →
    (∀ p, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ p zx.1 zx.2) (U ×ˢ Set.univ)) →
    (∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧ M ∈ schwartzA θ V.rank n ∧
      ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖) →
    let F : P → ℂ → ℂ := fun p z =>
      ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ p z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν
    ContinuousOn (fun pz : P × ℂ => F pz.1 pz.2) (Set.univ ×ˢ U) ∧ (∀ p, DifferentiableOn ℂ (F p) U) ∧
      ∀ p (r : ℕ) z, z ∈ U → iteratedDeriv r (F p) z =
        ⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ p w (GlobalTheory.SiegelFormula.invPt V h ξ)) z) q ∂autMeasure V ν

def DSieg : Prop :=
  ∀ (n : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ), z ∈ stripS X →
    IsSiegel (ptZ y X z Complex.I) ∧ IsSiegel (ptZ y X z (-Complex.I))ᴴ ∧
    ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 ∧
    ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0

def GCSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z Z' : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSiegel Z'ᴴ →
    IsSch (gC ε t c Z Z')

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB

variable {n : ℕ}

def dR (β : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (β j : ℂ)

theorem dR_conjTranspose (β : Fin n → ℝ) : (dR β)ᴴ = dR β := by
  simp [dR, Matrix.diagonal_conjTranspose]

theorem dR_mul (β β' : Fin n → ℝ) : dR β * dR β' = dR (fun j => β j * β' j) := by
  simp [dR, Matrix.diagonal_mul_diagonal]

theorem dR_add (β β' : Fin n → ℝ) : dR β + dR β' = dR (fun j => β j + β' j) := by
  simp [dR, Matrix.diagonal_add]

theorem dR_neg (β : Fin n → ℝ) : -dR β = dR (fun j => -β j) := by
  simp [dR, Matrix.diagonal_neg]

theorem dR_one : dR (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [dR]

theorem dR_inv (β : Fin n → ℝ) (hβ : ∀ j, β j ≠ 0) : (dR β)⁻¹ = dR (fun j => (β j)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [dR_mul]
  rw [← dR_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (hβ j)

theorem kth_eq (θ : Fin n → ℝ) : kth θ = fromBlocks (dR fun j => Real.cos (θ j)) (dR fun j => Real.sin (θ j))
    (-dR fun j => Real.sin (θ j)) (dR fun j => Real.cos (θ j)) := rfl

theorem kth_decomp (θ : Fin n → ℝ) (hc : ∀ j, Real.cos (θ j) ≠ 0) :
    kth θ = nU (dR fun j => Real.tan (θ j)) * nbar (dR fun j => -(Real.sin (θ j) * Real.cos (θ j))) *
      mM (dR fun j => (Real.cos (θ j))⁻¹) := by
  have hinv : ((dR fun j => (Real.cos (θ j))⁻¹)ᴴ)⁻¹ = dR fun j => Real.cos (θ j) := by
    rw [dR_conjTranspose, dR_inv _ (fun j => inv_ne_zero (hc j))]
    simp only [inv_inv]
  rw [kth_eq]
  simp only [nU, nbar, mM, hinv, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, dR_mul]
  rw [dR_add, dR_neg]
  congr 1
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq (θ j))
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  · congr 1
    funext j
    have h1 := hc j
    field_simp

theorem kth_half (θ : Fin n → ℝ) : kth θ = kth (fun j => θ j / 2) * kth (fun j => θ j / 2) := by
  have hc : ∀ j, Real.cos (θ j) = Real.cos (θ j / 2) * Real.cos (θ j / 2) -
      Real.sin (θ j / 2) * Real.sin (θ j / 2) := by
    intro j
    have := Real.cos_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    linear_combination Real.sin_sq_add_cos_sq (θ j / 2)
  have hs : ∀ j, Real.sin (θ j) = Real.cos (θ j / 2) * Real.sin (θ j / 2) +
      Real.sin (θ j / 2) * Real.cos (θ j / 2) := by
    intro j
    have := Real.sin_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    ring
  rw [kth_eq, kth_eq, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg, Matrix.neg_mul, dR_mul, dR_neg, dR_add]
  congr 1
  · congr 1
    funext j
    rw [hc j]
    ring
  · congr 1
    funext j
    rw [hs j]
  · congr 1
    funext j
    rw [hs j]
    ring
  · congr 1
    funext j
    rw [hc j]
    ring

end PositivityTheory.Rg.Sw.Glob.VacD
end
end

section

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcEH

open DCalcH DCalcBH DCalcDH

variable {m n : ℕ}

theorem crd_cont (X : Fin n → ℝ) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => crd (vS u X s) := by
  refine continuous_pi fun k => ?_
  unfold crd vS
  split_ifs <;> fun_prop

theorem fF_cont (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => fF c X Q u s := by
  unfold fF fP
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · simp only [evX_eq]
    exact (MvPolynomial.continuous_eval Q).comp (crd_cont X s)
  · simp only [gs, vS]
    fun_prop

theorem norm_gs (c : ℝ) (v : Fin m → Fin n → ℂ) : ‖gs c v‖ = Real.exp (-(c * sqN v)) := by
  simp only [gs, sqN]
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem sq_vS_le (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s R : ℝ) (hs : |s| ≤ R) :
    Real.exp (-(2 * R * ∑ j, |X j|)) * sqN u ≤ sqN (vS u X s) ∧ sqN (vS u X s) ≤ Real.exp (2 * R * ∑ j, |X j|) * sqN u := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hX : ∀ j, |2 * s * X j| ≤ 2 * R * ∑ j, |X j| := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| := Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hs h1 (abs_nonneg _) hR
    nlinarith
  have hterm : ∀ a j, ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (2 * s * X j) := by
    intro a j
    rw [norm_vS, ← Real.exp_nat_mul]; push_cast; ring_nf
  unfold sqN
  simp only [hterm]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    linarith [neg_abs_le (2 * s * X j), hX j]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity) |>.trans_eq (mul_comm _ _)
    linarith [le_abs_self (2 * s * X j), hX j]

theorem fF_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) :
    ∃ K a, 0 ≤ K ∧ 0 < a ∧ ∀ u, ∀ s' ∈ Set.Icc (s - 1) (s + 1), ‖fF c X Q u s'‖ ≤ K * Real.exp (-(a * sqN u)) := by
  set R := |s| + 1
  set M := ∑ j, |X j|
  set κ := Real.exp (-(2 * R * M))
  set κ' := Real.exp (2 * R * M)
  have hκ : 0 < κ := Real.exp_pos _
  have hκ' : 1 ≤ κ' := Real.one_le_exp (by positivity)
  obtain ⟨C, N, hC, hev⟩ := evX_growth Q
  obtain ⟨C2, hC2, hpe⟩ := poly_exp N (c * κ) (by positivity)
  refine ⟨Real.exp (R * m * M) * (C * (κ' ^ N * C2)), c * κ / 2, by positivity, by positivity, fun u s' hs' => ?_⟩
  have hs'R : |s'| ≤ R := by
    rw [abs_le]; constructor <;> linarith [hs'.1, hs'.2, neg_abs_le s, le_abs_self s]
  obtain ⟨hlo, hhi⟩ := sq_vS_le u X s' R hs'R
  have hS := sqN_nonneg u
  have h1 : ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ ≤ Real.exp (R * m * M) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have : |∑ j, X j| ≤ M := Finset.abs_sum_le_sum_abs _ _
    have h2 : s' * (m : ℝ) * ∑ j, X j ≤ |s'| * m * |∑ j, X j| := by
      calc s' * (m : ℝ) * ∑ j, X j ≤ |s' * (m : ℝ) * ∑ j, X j| := le_abs_self _
        _ = |s'| * m * |∑ j, X j| := by rw [abs_mul, abs_mul, Nat.abs_cast]
    have h3 : |s'| * m * |∑ j, X j| ≤ R * m * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hs'R (by positivity)) this (abs_nonneg _) (by positivity)
    linarith
  have h2 : ‖evX Q (vS u X s')‖ ≤ C * (κ' ^ N * (1 + sqN u) ^ N) := by
    refine (hev _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [sqN_nonneg (vS u X s')]) ?_ N
    nlinarith
  have h3 : ‖gs c (vS u X s')‖ ≤ Real.exp (-(c * κ * sqN u)) := by
    rw [norm_gs]; refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlo hc.le
    linarith
  unfold fF fP
  rw [norm_mul, norm_mul]
  calc ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ * (‖evX Q (vS u X s')‖ * ‖gs c (vS u X s')‖)
      ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (1 + sqN u) ^ N) * Real.exp (-(c * κ * sqN u))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg hC (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))))
          (by positivity) (by positivity)
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * ((1 + sqN u) ^ N * Real.exp (-(c * κ * sqN u))))) := by ring
    _ ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (C2 * Real.exp (-(c * κ / 2 * sqN u))))) := by
        have := hpe (sqN u) hS
        gcongr
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * C2)) * Real.exp (-(c * κ / 2 * sqN u)) := by ring

end DCalcEH

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Topology Metric

namespace PositivityTheory.Rg.Sw.Glob

namespace DilDH

variable {E : Type} [MetricSpace E] [ProperSpace E]

theorem deriv_step {U : Set ℂ} (hU : IsOpen U) {g : ℂ → E → ℂ}
    (hc : ContinuousOn (fun p : ℂ × E => g p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ u, DifferentiableOn ℂ (fun z => g z u) U) :
    ContinuousOn (fun p : ℂ × E => deriv (fun z => g z p.2) p.1) (U ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z0, u0⟩ := p
  have hz0 : z0 ∈ U := hp.1
  have hopen : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall z0 (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2 := by
    apply (isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually
    intro w hw
    have hwU : w ∈ U := hK hw
    have hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0) :=
      hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)
    have h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp (continuous_swap.tendsto (u0, w))
    have h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))
    have hε' : 0 < ε * r / 4 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2
    calc dist (g q.2 q.1) (g q.2 u0)
        ≤ dist (g q.2 q.1) (g w u0) + dist (g q.2 u0) (g w u0) := dist_triangle_right _ _ _
      _ < ε * r / 4 + ε * r / 4 := add_lt_add hq1 hq2
      _ = ε * r / 2 := by ring
  have hd0 : ContinuousAt (deriv fun z => g z u0) z0 :=
    ((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have e1 := (continuous_fst.tendsto (z0, u0)).eventually
    (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))
  have e2 := (continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)
  have e3 := (continuous_snd.tendsto (z0, u0)).eventually hunif
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨z, u⟩ := q
  simp only at hq1 hq2 hq3 ⊢
  have hzU : closedBall z r ⊆ closedBall z0 (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w z0 ≤ dist w z + dist z z0 := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hw hq2.le
      _ = 2 * r := by ring
  have hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z :=
    (Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm
  have hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z :=
    (Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm
  have hsph : sphere z r ⊆ U := sphere_subset_closedBall.trans (hzU.trans hK)
  have hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z)
      < ε * r / 2 / r := by
    rw [dist_eq_norm]
    apply Complex.norm_cderiv_sub_lt hr0
    · intro w hw
      rw [← dist_eq_norm]
      exact hq3 w (hzU (sphere_subset_closedBall hw))
    · exact (hd u).continuousOn.mono hsph
    · exact (hd u0).continuousOn.mono hsph
  have hhalf : ε * r / 2 / r = ε / 2 := by field_simp
  rw [hhalf] at hdiff
  have hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2 := by
    rw [hcu, hcu0]
    exact hdiff
  calc dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z0)
      ≤ dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z)
        + dist (deriv (fun z => g z u0) z) (deriv (fun z => g z u0) z0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hq1
    _ = ε := by ring

def scaleL (m n : ℕ) (s : ℝ) (X : Fin n → ℝ) : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun u := fun i j => u i j * (Real.exp (s * X j) : ℂ)
  invFun u := fun i j => u i j * (Real.exp (-(s * X j)) : ℂ)
  map_add' u v := by funext i j; simp [add_mul]
  map_smul' r u := by funext i j; simp [Complex.real_smul, mul_assoc]
  left_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]
  right_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]

end DilDH

theorem schScale : SchScale := by
  intro m n f s X a hf
  obtain ⟨S, hS⟩ := hf
  refine ⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_eq_mul, ← hS]
  rfl

theorem contDeriv : ContDeriv := by
  intro m n U hU f hc hd r
  induction r generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    have h1 := DilDH.deriv_step hU hc hd
    have h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U :=
      fun u => (hd u).deriv hU
    have h3 := ih (fun z u => deriv (fun z => f z u) z) h1 h2
    simpa only [iteratedDeriv_succ'] using h3

end PositivityTheory.Rg.Sw.Glob
end
end
