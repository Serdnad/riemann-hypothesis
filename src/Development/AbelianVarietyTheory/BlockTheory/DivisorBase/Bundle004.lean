module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram

open GlobalTheory.HermFrame

variable {n a g : ℕ}

def polydisc (n : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | ∀ k, ‖z k‖ < ρ}

def punctured (ha : a ≤ n) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {z | z ∈ polydisc n ρ ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def tlog (w : ℂ) : ℝ := -Real.log ‖w‖ / (2 * Real.pi)

structure IsPeriodChart (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Prop where

  rk_le : rk ≤ g

  holo : ∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (polydisc n 1)

  symm : ∀ z ∈ polydisc n 1, (τ₀ z).IsSymm

  psd : ∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef

  supp : ∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0

  toric : (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix
    (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef

  abelian : ∀ z ∈ polydisc n 1, (((τ₀ z).map Complex.im).submatrix
    (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef

def period (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (z : Fin n → ℂ) (L : Fin a → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ₀ z + ∑ i, (L i / (2 * Real.pi * I)) • (B i).map (Int.cast : ℤ → ℂ)

def imPeriod (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ₀ z).map Complex.im + ∑ i, tlog (z (Fin.castLE ha i)) • (B i).map (Int.cast : ℤ → ℝ)

def hodgeGram (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (imPeriod ha τ₀ B z).map Complex.ofReal

def poincareGram (a : ℕ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun k =>
    ((if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2 : ℝ) : ℂ)

def BoundsOn (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ρ c C : ℝ) : Prop :=
  (∀ z ∈ punctured ha ρ, (imPeriod ha τ₀ B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) ∧
  (∀ z ∈ punctured ha ρ,
    ((C * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ)
      - imPeriod ha τ₀ B z).PosSemidef) ∧
  OneFormBound (punctured ha ρ) (fun _ => 1) (poincareGram a) (conn (hodgeGram ha τ₀ B)) C ∧
  TwoFormBound (punctured ha ρ) (hodgeGram ha τ₀ B) (poincareGram a) (curv (hodgeGram ha τ₀ B)) C

def HodgeChartBounds : Prop :=
  ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B →
    ∃ ρ c C : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < c ∧ BoundsOn ha τ₀ B ρ c C


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w :=
  div_pos (neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr h0) h1)) (by positivity)


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by
  ext j k
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.add_im, Complex.im_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL i, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Complex.norm_exp, Real.log_exp]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Complex.mul_im, Complex.div_re, Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp


open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by
  apply _root_.GlobalTheory.HermFrame.conn_eq_of_isSymm
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1 :=
    Filter.eventually_all.2 fun k =>
      (continuous_apply k).norm.continuousAt.eventually_lt continuousAt_const (hz k)
  filter_upwards [hnear] with x hx
  have hB : ∀ i, ((B i).map (Int.cast : ℤ → ℝ))ᵀ = (B i).map (Int.cast : ℤ → ℝ) := fun i => by
    have := (h.psd i).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτ : ((τ₀ x).map Complex.im)ᵀ = (τ₀ x).map Complex.im := by
    rw [← Matrix.transpose_map, (h.symm x hx).eq]
  have hI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B x).IsSymm := by
    unfold Matrix.IsSymm _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod
    rw [Matrix.transpose_add, Matrix.transpose_sum, hτ]
    simp only [Matrix.transpose_smul, hB]
  exact hI.map _

end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end
end

section

open Matrix MeasureTheory
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

abbrev Fl (g : ℕ) : Type := Fin g ⊕ Fin g → ℝ

def riem {g : ℕ} (x y : Fl g) : ℝ :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))

def symp (g : ℕ) : Fl g [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := riem (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, add_mul, mul_add, Finset.sum_add_distrib] <;> ring
  map_update_smul' := by
    intro inst v i c x
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, ← Finset.sum_sub_distrib, Finset.mul_sum] <;>
      exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by
    unfold riem
    fun_prop
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simp only [riem, h01]
    exact Finset.sum_eq_zero fun _ _ => by ring

def stdLat (g : ℕ) : Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))

def wedgePow {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : Fin k × Fin 2 → T) : ℝ :=
  (1 / 2 ^ k) * ∑ σ : Equiv.Perm (Fin k × Fin 2),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, α ![v (σ (i, 0)), v (σ (i, 1))]

def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : Fin g → ℂ :=
  (fun i => (x (Sum.inl i) : ℂ)) ᵥ* τ + fun i => (x (Sum.inr i) : ℂ)

def flatOf {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : Fl g :=
  Sum.elim ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹)
    ((fun i => (z i).re) - ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re)

abbrev Sp (g : ℕ) : Type := Matrix.symplecticGroup (Fin g) ℝ

section Family

abbrev Pt (E : Type) (g : ℕ) : Type := E × (Fin g → ℂ)

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ}

abbrev Form2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) : Type :=
  Pt E g [⋀^Fin 2]→L[ℝ] ℝ

def IsPeriodMap (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  IsOpen B ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) ∧ ∀ b ∈ B, IsSiegel (τ b)

def cov (B : Set E) (g : ℕ) : Set (Pt E g) := B ×ˢ Set.univ

def flat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Fl g := flatOf (τ P.1) P.2

def dflat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Pt E g →L[ℝ] Fl g :=
  fderiv ℝ (flat τ) P

def om0 (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Form2 E g :=
  (symp g).compContinuousLinearMap (dflat τ P)

def pull (f : Pt E g → Pt E' g) (α : Pt E' g → Form2 E' g) (P : Pt E g) : Form2 E g :=
  (α (f P)).compContinuousLinearMap (fderiv ℝ f P)

def transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 + per (τ P.1) x)

def ddc (u : Pt E g → ℝ) (P v w : Pt E g) : ℝ :=
  (1 / (4 * π)) * (fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • v)) P w -
    fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • w)) P v)

def IsFactor (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  (∀ l ∈ M, DifferentiableOn ℂ (j l) (cov B g) ∧ ∀ P ∈ cov B g, j l P ≠ 0) ∧
  ∀ l ∈ M, ∀ l' ∈ M, ∀ P ∈ cov B g, j (l + l') P = j l (transl τ l' P) * j l' P

def IsMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (cov B g) ∧ (∀ P ∈ cov B g, 0 < h P) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, h (transl τ l P) * ‖j l P‖ ^ 2 = h P

def ChernIsFlat (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) : Prop :=
  ∀ P ∈ cov B g, ∀ v w : Pt E g, -ddc (fun Q => Real.log (h Q)) P v w = om0 τ P ![v, w]

def InducesPolarisation (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  ∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ,
    (∀ l ∈ M, Differentiable ℂ (f l) ∧ ∀ z, j l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧
    ∀ l ∈ M, ∀ l' ∈ M, ∀ z,
      f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = (riem l l' : ℂ)

end Family

def symMat (g : ℕ) : Submodule ℂ (Fin g → Fin g → ℂ) where
  carrier := {A | ∀ i j, A i j = A j i}
  add_mem' := fun {A B} hA hB i j => by simp [hA i j, hB i j]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c A hA i j => by simp [hA i j]

def tauU {g : ℕ} (s : symMat g) : Matrix (Fin g) (Fin g) ℂ := Matrix.of s.1

def siegel (g : ℕ) : Set (symMat g) := {s | IsSiegel (tauU s)}

def symPart {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : symMat g :=
  ⟨fun i j => (A i j + A j i) / 2, fun i j => by simp only [add_comm]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
end
end

section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal LinearAlgebra.Projectivization

noncomputable section

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def IsProjective (A : FinHolAtlas d X) : Prop :=
  ∃ (N : ℕ) (F : X → ℙ ℂ (Fin (N + 1) → ℂ)), Function.Injective F ∧
    ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ G : X → Fin (N + 1) → ℂ,
      (∀ i, A.HoloOn W fun y => G y i) ∧
      (∀ y ∈ W, ∃ h : G y ≠ 0, F y = Projectivization.mk ℂ (G y) h) ∧
      ∀ j, x ∈ (A.chart j).source → ∀ v : Fin d → ℂ,
        fderiv ℂ (G ∘ (A.chart j).symm) (A.chart j x) v ∈ Submodule.span ℂ {G x} → v = 0

def IsIrreducibleAnalytic (A : FinHolAtlas d X) (Z : Set X) : Prop :=
  A.IsAnalyticSubset Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂, A.IsAnalyticSubset Z₁ → A.IsAnalyticSubset Z₂ → Z = Z₁ ∪ Z₂ → Z = Z₁ ∨ Z = Z₂

def IsIrreducibleComponent (A : FinHolAtlas d X) (S C : Set X) : Prop :=
  Maximal (fun C' => IsIrreducibleAnalytic A C' ∧ C' ⊆ S) C

def padZero (n d : ℕ) (z : Fin n → ℂ) : Fin d → ℂ :=
  fun k => if h : (k : ℕ) < n then z ⟨k, h⟩ else 0

def IsStraightening (A : FinHolAtlas d X) (Z : Set X) (n : ℕ)
    (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) : Prop :=
  n ≤ d ∧ IsCompatChart A ψ ∧
    Z ∩ ψ.source = {y ∈ ψ.source | ∀ k : Fin d, n ≤ (k : ℕ) → ψ y k = 0}

def regularLocus (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) : Set X :=
  {x ∈ Z | ∃ ψ, IsStraightening A Z n ψ ∧ x ∈ ψ.source}

def param (n : ℕ) (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) (z : Fin n → ℂ) : X :=
  ψ.symm (padZero n d z)

def paramDens (n : ℕ) (Φ : LocPot X) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
    (z : Fin n → ℂ) : ℝ :=
  maDens (fun _ z' => Φ.φ (param n ψ z) (param n ψ z')) z

def IsPieceFamily (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (S : Set X) {k : ℕ}
    (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ)) : Prop :=
  (∀ j, IsStraightening A Z n (ψ j)) ∧ (∀ j, MeasurableSet (B j)) ∧
    (∀ j, ∀ z ∈ B j, padZero n d z ∈ (ψ j).target ∧ param n (ψ j) z ∈ S) ∧
    Pairwise fun i j => Disjoint (param n (ψ i) '' B i) (param n (ψ j) '' B j)

def regIntegral (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (Φ : LocPot X) (S : Set X)
    (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ))
    (_ : IsPieceFamily A Z n S ψ B),
    ∑ j, ∫⁻ z in B j, f (param n (ψ j) z) * ‖paramDens n Φ (ψ j) z‖ₑ

def normSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  ‖s y y‖ * Real.exp (-L.φ y y)


open scoped Classical in
def absLogNorm (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ≥0∞ :=
  if s y y = 0 then ∞ else ENNReal.ofReal |logNormSec L s y|

def boundary {m : ℕ} (σ : Fin m → X → X → ℂ) : Set X :=
  {y | ∃ i, σ i y y = 0}

def rFun (L : LocPot X) (σ : X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - 2 * logNormSec L σ y

def pFun {m : ℕ} (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ) (y : X) : ℝ :=
  -c * ∑ i, Real.log (rFun (Λ i) (σ i) y)

def poincarePot {m : ℕ} (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ)
    (c : ℝ) : LocPot X :=
  α + LocPot.ofFun fun y => pFun Λ σ c y / 2

def FormBoundedBy (A : FinHolAtlas d X) (α L : LocPot X) (K : ℝ) : Prop :=
  IsPsh A (α.rsmul K + L) ∧ IsPsh A (α.rsmul K + L.rsmul (-1))

def IsAdmissibleConst {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (c : ℝ) : Prop :=
  0 < c ∧ ∃ K : Fin m → ℝ, (∀ i, 0 ≤ K i ∧ FormBoundedBy A α (Λ i) (K i)) ∧
    c * ∑ i, K i ≤ Real.exp 1 / 2

def IsBoundarySetting {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (σ : Fin m → X → X → ℂ) (c : ℝ) : Prop :=
  IsPotential A α ∧ IsPosPot A α ∧
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧
      interior {y | σ i y y = 0} = ∅ ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) ∧
    IsAdmissibleConst A α Λ c

end

end GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
end
