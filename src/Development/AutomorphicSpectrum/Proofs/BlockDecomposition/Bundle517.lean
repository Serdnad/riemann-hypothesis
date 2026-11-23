module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle495
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hk
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
end

section

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.Sep

variable {n : ℕ}

theorem sum_swap (X P Q : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, X a b * (P a b - Q b a) = ∑ a, ∑ b, (X a b * P a b - X b a * Q a b) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem real_linear_skew (L : Mat n →ₗ[ℝ] ℂ) (X : Mat n) (hX : Xᴴ = -X) :
    L X = ∑ a, ∑ b, X a b * ((1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I))
      - (1 / 2 : ℂ) * (L (Matrix.single b a 1) + Complex.I * L (Matrix.single b a Complex.I))) := by
  have hs : ∀ (a b : Fin n) (z : ℂ), Matrix.single a b z =
      z.re • Matrix.single a b (1 : ℂ) + z.im • Matrix.single a b Complex.I := by
    intro a b z
    simp only [Matrix.smul_single]
    rw [← Matrix.single_add]
    simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  have hX' : ∀ a b, X b a = -conj (X a b) := by
    intro a b
    have := congrFun (congrFun hX a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2
  have h1 : L X = ∑ a, ∑ b, (((X a b).re : ℂ) * L (Matrix.single a b 1) + ((X a b).im : ℂ) * L (Matrix.single a b Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs a b (X a b), map_add (f := _), map_smul, map_smul]
    simp [Complex.real_smul]
  rw [h1]
  refine Eq.trans ?_ (sum_swap (fun a b => X a b)
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I)))
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) + Complex.I * L (Matrix.single a b Complex.I)))).symm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hX' a b]
  have hc : conj (X a b) = ((X a b).re : ℂ) - ((X a b).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ((X a b).re : ℂ) + ((X a b).im : ℂ) * Complex.I = X a b := Complex.re_add_im _
  have key : ∀ x y p q : ℂ, x * p + y * q = (x + y * Complex.I) * ((1 / 2 : ℂ) * (p - Complex.I * q))
      - (-(x - y * Complex.I)) * ((1 / 2 : ℂ) * (p + Complex.I * q)) := by
    intro x y p q
    linear_combination (y * q) * Complex.I_sq
  have := key (X a b).re (X a b).im (L (Matrix.single a b 1)) (L (Matrix.single a b Complex.I))
  rw [hz, ← hc] at this
  exact this

theorem Kf_apply (a b : Fin n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (1 / 2 : ℂ) * (Rd (Matrix.single a b 1) h.1 g - Complex.I * Rd (Matrix.single a b Complex.I) h.1 g)
      - (1 / 2 : ℂ) * (Rd (Matrix.single b a 1) h.1 g + Complex.I * Rd (Matrix.single b a Complex.I) h.1 g) := by
  have e : (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (e1 GlobalTheory.CompanionTheory.ModelS.DR a b h).1 g - (f1 GlobalTheory.CompanionTheory.ModelS.DR b a h).1 g := by
    simp [GlobalTheory.CompanionTheory.ModelS.Kf, e2, sub_eq_add_neg]
  rw [e, GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply b a h hg]
  simp [Eu]
  ring

def AX (X : Mat n) : Module.End ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n) := ∑ a, ∑ b, X a b • GlobalTheory.CompanionTheory.ModelS.Kf a b

theorem AX_apply (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (AX X w).1 g = Rd X w.1 g := by
  let L : Mat n →ₗ[ℝ] ℂ := ((fderiv ℝ w.1 g).comp (GlobalTheory.CompanionTheory.RCalc.mulL g)).toLinearMap
  have hL : ∀ v, L v = Rd v w.1 g := fun _ => rfl
  have e : (AX X w).1 g = ∑ a, ∑ b, X a b * (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g := by
    simp [AX, LinearMap.sum_apply, Finset.sum_apply]
  rw [e, ← hL X, real_linear_skew L X hX]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Kf_apply a b w hg]
  rfl

theorem AX_mem (X : Mat n) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n))
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) {w : GlobalTheory.CompanionTheory.ModelS.SmF n} (hw : w ∈ S) :
    AX X w ∈ S := by
  simp only [AX, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b w hw)

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) ((NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt t h
  simp only [Complex.coe_smul] at this ⊢
  exact this

theorem exp_deriv (X : Mat n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X t i j
  exact this

theorem exp_mem (X : Mat n) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GLs n := by
  have h : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := (GlobalTheory.CompanionTheory.GLK.expG X t).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero

theorem curve_deriv (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => w.1 (NormedSpace.exp ((t : ℂ) • X))) ((AX X w).1 (NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg := exp_mem X t
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth w.2.1 hg).hasFDerivAt
  have := hd.comp_hasDerivAt t (exp_deriv X t)
  rw [AX_apply X hX w hg]
  exact this

theorem ode_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E) (f : ℝ → E)
    (h : ∀ t, HasDerivAt f (B (f t)) t) (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  have := ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
    (f := f) (g := fun _ => 0)
    (fun _ => B.lipschitzWith.lipschitzOnWith)
    (fun t => ⟨h t, trivial⟩) (fun t => ⟨by simpa using hasDerivAt_const t (0 : E), trivial⟩) h0
  exact congrFun this t

theorem vanish_curve (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)) (fd : FiniteDimensional ℂ S)
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) (h1 : ∀ w ∈ S, w.1 1 = 0)
    (X : Mat n) (hX : Xᴴ = -X) (t : ℝ) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (hw : w ∈ S) :
    w.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := by
  classical
  let bs := Module.finBasis ℂ S
  let C : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    fun i j => bs.repr ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ j
  have hexp : ∀ (u : S) (g : Mat n), u.1.1 g = ∑ j, bs.repr u j * (bs j).1.1 g := by
    intro u g
    have h := congrArg (fun v : S => v.1.1 g) (bs.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  let f : ℝ → Fin (Module.finrank ℂ S) → ℂ := fun t i => (bs i).1.1 (NormedSpace.exp ((t : ℂ) • X))
  let B : (Fin (Module.finrank ℂ S) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ S) → ℂ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).restrictScalars ℝ
  have hd : ∀ t, HasDerivAt f (B (f t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have hc := curve_deriv X hX (bs i).1 t
    have e : (AX X (bs i).1).1 (NormedSpace.exp ((t : ℂ) • X)) = B (f t) i := by
      have := hexp ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ (NormedSpace.exp ((t : ℂ) • X))
      refine this.trans ?_
      show _ = (C.mulVec (f t)) i
      rfl
    rw [← e]
    exact hc
  have h0 : f 0 = 0 := by
    funext i
    simpa [f] using h1 _ (bs i).2
  have hz := ode_zero B f hd h0 t
  rw [hexp ⟨w, hw⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (bs j).1.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := congrFun hz j
  rw [this, mul_zero]

theorem main : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S →
    (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
    ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  intro n S fd hS h1 w hw k
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryLog.main n k
  have := vanish_curve S fd hS h1 X hX 1 w hw
  simp only [Complex.ofReal_one, one_smul] at this
  rw [hk]
  exact this

end GlobalTheory.CompanionTheory.ModelS.Sep
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

section Tempered

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem tempered_mul_entry {l m n : Type*} [Fintype m] {M : W → Matrix l m ℂ} {N : W → Matrix m n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j)
    (hN : ∀ i j, Function.HasTemperateGrowth fun x => N x i j) (i : l) (j : n) :
    Function.HasTemperateGrowth fun x => (M x * N x) i j := by
  simp only [Matrix.mul_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => (hM i k).mul (hN k j)

theorem tempered_trace {n : Type*} [Fintype n] {M : W → Matrix n n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j) :
    Function.HasTemperateGrowth fun x => (M x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => hM k k

end Tempered

variable {D : D7} {r : ℕ}

def quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) (X : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ :=
  -∑ τ, (tauE D τ c * Matrix.trace (a.map (tauE D τ) *
    ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ))))).re

theorem tempered_quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) :
    Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => ((quadForm D c G a X : ℝ) : ℂ) := by
  have hc : ∀ (τ : D.what₂.Tau) (i : Fin m) (j : Fin n),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => Matrix.of (X τ) i j := fun τ i j =>
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))).hasTemperateGrowth)
  have hs : ∀ (τ : D.what₂.Tau) (i : Fin n) (j : Fin m),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => (Matrix.of (X τ))ᴴ i j := fun τ i j =>
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ)))).hasTemperateGrowth)
  have hg : ∀ τ : D.what₂.Tau, Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ =>
      tauE D τ c * Matrix.trace (a.map (tauE D τ) *
        ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ)))) := fun τ =>
    (Function.HasTemperateGrowth.const _).mul (tempered_trace
      (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _)
        (tempered_mul_entry (hs τ)
          (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _) (hc τ)))))
  have hsum := Function.HasTemperateGrowth.sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    ((-(Complex.ofRealCLM.comp Complex.reCLM)).hasTemperateGrowth).comp (hg τ)
  convert hsum using 1
  funext X
  simp [quadForm]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e :=
  (hθ τ).1 e

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D l n) = compAt θ τ x * compAt θ τ y := by
  have := Matrix.map_mul (L := x) (M := y) (f := (θ τ).comp (infPart D))
  exact this

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (y : Mx D m n) :
    compAt θ τ (adj y) = (compAt θ τ y)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.Mem.VolExists.infEmb_sigR (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (hθ τ)]
  rfl

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (rat M) = M.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  exact theta_incA hθ τ _

theorem multM_eq_quadForm {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (V : HSp D) (a : HermE D r)
    (y : Mx D V.rank r) :
    multM θ α V a y = quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1
      (fun τ i j => compAt θ τ y i j) := by
  unfold multM lam quadForm
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, map_mul, theta_incA hθ, GlobalTheory.PhaseReal.theta_pair θ hθ]
  congr 3
  show _ * compAt θ τ (inner V y y) = _
  congr 1
  unfold GlobalTheory.StdUnn.inner
  rw [compAt_mul', compAt_mul', compAt_adj hθ, gA, compAt_rat hθ]
  rfl

theorem multM_tempered : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  intro D r θ hθ α V a
  refine ⟨fun X => ((quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1 X : ℝ) : ℂ),
    tempered_quadForm D _ _ _, fun y => ?_⟩
  rw [multM_eq_quadForm hθ]

end GlobalTheory.CompanionTheory.WSum
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_fold {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ) (hP : Integrable P m.μ) :
    ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  have : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hμ := m.hμ
  have := hμ.1
  let e : Matrix (Fin ρ) (Fin p) D.host.E ≃ ratMx D ρ p :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) =
      ∑' g : ratMx D ρ p, P (g +ᵥ y) := fun y => e.tsum_eq fun g => P (g +ᵥ y)
  simp only [h1]
  rw [hμ.2.1.integral_eq_tsum'' P hP]
  refine (integral_tsum (ι := ratMx D ρ p) (f := fun g y => P (g +ᵥ y)) (fun g => ?_) ?_).symm
  · exact ((hP.comp_add_left (g : Mx D ρ p)).aestronglyMeasurable).restrict
  · rw [← hμ.2.1.lintegral_eq_tsum'' fun x => ‖P x‖ₑ]
    exact hP.2.ne

end GlobalTheory.CompanionTheory.FJE
end
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_finite_levi_stable_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  first | exact @GlobalTheory.CompanionTheory.LvStableChains.exists_stable | exact GlobalTheory.CompanionTheory.LvStableChains.exists_stable | (intros; apply GlobalTheory.CompanionTheory.LvStableChains.exists_stable <;> assumption)
end
