module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def coords (H : Mat n) : Fin n × Fin n → ℝ := fun p => ((H * hb p).trace).re

def oPt (n : ℕ) : Fin n × Fin n → ℝ := coords 1

def Kf {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d x y : Mat n) :
    V →L[ℂ] V :=
  Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * Fr y⁻¹

def Kc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ)
    (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d : Mat n) (y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ)) : V →L[ℂ] V :=
  ((c : ℂ) * ((hOf y.2).det ^ n)⁻¹) • Kf Fr k Γ T d (σ y.1) (σ y.2)

def HbFacts : Prop :=
  ∀ n : ℕ, (∀ p, (hb p : Mat n).IsHermitian) ∧ (∀ p q : Fin n × Fin n, ((hb p : Mat n) * hb q).trace = if p = q then 1 else 0) ∧
    (∀ H : Mat n, H.IsHermitian → hOf (coords H) = H) ∧ (∀ v : Fin n × Fin n → ℝ, coords (hOf v) = v) ∧
    (∀ v : Fin n × Fin n → ℝ, (hOf v).IsHermitian) ∧ ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 ∧ ∑ p, (hb p : Mat n).trace • hb p = 1 ∧
    oPt n ∈ cone n

def FrameDer : Prop :=
  ∀ (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (σ : (Fin n × Fin n → ℝ) → Mat n) (F : Mat n → Z),
    ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) → ContDiffOn ℝ ∞ F (GLs n) →
    (∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (x * k.1) = F x) →
    ∀ v ∈ cone n, ∀ x ∈ GLs n, x * xᴴ = hOf v → ∀ X : Mat n, X.IsHermitian →
      fderiv ℝ (fun w => F (σ w)) v (coords ((2 : ℂ) • (x * X * xᴴ))) = fderiv ℝ F x (x * X)

def KChain : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ ∧
        ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y) =
          ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ,
      ContDiffOn ℝ ∞ (Kc σ c Fr k Γ T d) (cone n ×ˢ cone n) ∧
      (∀ y ∈ cone n ×ˢ cone n, Γ * Kc σ c Fr k Γ T d y = Kc σ c Fr k Γ T d y * Γ) ∧
      ∀ y ∈ cone n ×ˢ cone n, ∑ i, ε (hb i) * fderiv ℝ (Kc σ c Fr k Γ T d) y (Pi.single i 1, 0) +
        ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) y (0, Pi.single i 1) * ε (hb i) = 0

def KSupp : Prop :=
  SuppSt → ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n),
    ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (R : ℝ), (∀ y ∈ GLs n, R < lg y → k y = 0) →
    ∀ (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) → ∀ c : ℝ,
      ∃ C ⊆ cone n, IsCompact C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ cone n, v ∉ C →
        ∀ᶠ y in nhds (s • v + (1 - s) • oPt n, v), Kc σ c Fr k Γ T (diagonal z) y = 0

def End1 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    (∀ F : Mat n → ℂ, ContinuousOn F (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0) →
        (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (y * k.1) = F y) →
        ∫ y : G n, F y.val ∂μ = c * ∫ v in cone n, F (σ v) * ((hOf v).det ^ n)⁻¹) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContinuousOn k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ) → ∀ (d : G n) (R : ℝ),
    (∀ x ∈ GLs n, R < lg x → k (x⁻¹ * d.val * xᴴ⁻¹) = 0) →
      Integrable (fun x => phiOf E T k (tw x d)) μ ∧
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        ∫ x, phiOf E T k (tw x d) ∂μ

def End0 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    (∀ F : Mat n → ℂ, ContinuousOn F (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0) →
        (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (y * k.1) = F y) →
        ∫ y : G n, F y.val ∂μ = c * ∫ v in cone n, F (σ v) * ((hOf v).det ^ n)⁻¹) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ), ContinuousOn k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ) → (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) →
    (∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x) →
    ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        val (infOf lam) * conj (weylChar lam fun a => z a ^ 2)

def LAsm : Prop := HbFacts → FrameDer → KChain → KSupp → End1 → End0 → Homot → ConeSt → LOf

end PositivityTheory.RgBcC.LfSt
end
end

section

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulRL (c : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c)

@[simp] theorem mulRL_apply (c y : Mat n) : mulRL c y = y * c := rfl

def mulLRL (a c : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ a).comp (LinearMap.mulRight ℝ c))

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_star_mul k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem unit_star_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_mul_star k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem inv_val (k : Matrix.unitaryGroup (Fin n) ℂ) : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = (k.1)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

theorem fderiv_right {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (c g : Mat n) (Φ : W →L[ℝ] W)
    (hF : DifferentiableAt ℝ F (g * c)) (hF' : DifferentiableAt ℝ F g)
    (hEq : (fun y => F (y * c)) =ᶠ[nhds g] fun y => Φ (F y)) (Z : Mat n) :
    fderiv ℝ F (g * c) (Z * c) = Φ (fderiv ℝ F g Z) := by
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have h1 : HasFDerivAt (fun y => F (y * c)) ((fderiv ℝ F (g * c)).comp (mulRL c)) g := by
    exact hF.hasFDerivAt.comp g (mulRL c).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Φ (F y)) (Φ.comp (fderiv ℝ F g)) g := Φ.hasFDerivAt.comp g hF'.hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun L : Mat n →L[ℝ] W => L Z) e
  simpa using this

section Cx

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem fr_star (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) : Fr (k.1)ᴴ = E.ρ k⁻¹ := by
  rw [← inv_val, h.onK]

theorem rho_mul_inv (k : Matrix.unitaryGroup (Fin n) ℂ) : E.ρ k * E.ρ k⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem eps_rho_inv (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) (hX : X.IsHermitian) :
    ε X * E.ρ k⁻¹ = E.ρ k⁻¹ * ε (k.1 * X * (k.1)ᴴ) := by
  have := h.frε (k.1)ᴴ (unit_star_mem k) X hX
  rwa [fr_star h, Matrix.conjTranspose_conjTranspose] at this

theorem eps_rho (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) (hY : Y.IsHermitian) :
    ε Y * E.ρ k = E.ρ k * ε ((k.1)ᴴ * Y * k.1) := by
  have := h.frε k.1 (unit_mem k) Y hY
  rwa [h.onK] at this

theorem fr_diff (h : CxData lam E Fr ε ι S Γ T) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ Fr x :=
  (h.smooth.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem dFr_conj (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) :
    fderiv ℝ Fr 1 ((k.1)ᴴ * (Y * k.1)) = E.ρ k⁻¹ * fderiv ℝ Fr 1 Y * E.ρ k := by
  set L : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
    (ContinuousLinearMap.mulLeftRight ℂ (E.V →L[ℂ] E.V) (E.ρ k⁻¹) (E.ρ k)).restrictScalars ℝ with hL
  have hEq : (fun y => Fr ((k.1)ᴴ * (y * k.1))) =ᶠ[nhds (1 : Mat n)] fun y => L (Fr y) := by
    filter_upwards [isOpen_GLs.mem_nhds (one_mem_GLs (n := n))] with y hy
    rw [h.mul _ (unit_star_mem k) _ (mem_GLs_mul hy (unit_mem k)), h.mul _ hy _ (unit_mem k), fr_star h, h.onK]
    simp [hL, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have hpt : (k.1)ᴴ * ((1 : Mat n) * k.1) = 1 := by rw [Matrix.one_mul, unit_star_mul]
  have h1 : HasFDerivAt (fun y => Fr ((k.1)ᴴ * (y * k.1))) ((fderiv ℝ Fr 1).comp (mulLRL (k.1)ᴴ k.1)) 1 := by
    have hd := (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
    rw [← hpt] at hd
    have := hd.comp (1 : Mat n) (mulLRL (k.1)ᴴ k.1).hasFDerivAt
    rw [hpt] at this
    exact this
  have h2 : HasFDerivAt (fun y => L (Fr y)) (L.comp (fderiv ℝ Fr 1)) 1 :=
    L.hasFDerivAt.comp (1 : Mat n) (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun M : Mat n →L[ℝ] (E.V →L[ℂ] E.V) => M Y) e
  simpa [hL, mulLRL, ContinuousLinearMap.mulLeftRight_apply] using this

end Cx

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.ChainPf

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def DC {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr : Mat n → (V →L[ℂ] V))
    (f : Mat n → V) : Mat n → V :=
  fun x => ∑ p, ε (hb p) (Rd (hb p) f x + fderiv ℝ Fr 1 (hb p) (f x))

def kapL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y)

def kapR {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))

def DCinCE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ f ∈ CE E, DC ε Fr f ∈ CE E

def DCwave : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ u, IsWave E u →
    IsWave E fun t => DC ε Fr (u t)

def ParamInt : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (g : ℝ → ℝ) (T : ℝ), IsBump g T →
    ContDiffOn ℝ ∞ (fun x => ∫ t, (g t : ℂ) • u t x) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x

def ZopDC : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (h : Mat n → E.V), ContDiffOn ℝ ∞ h (GLs n) → ∀ w : List (Bool × ℕ),
      ContDiffOn ℝ ∞ (zOp w h) (GLs n) ∧ ∀ x ∈ GLs n, zOp w (DC ε Fr h) x = DC ε Fr (zOp w h) x

def ActDer : Prop :=
  Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ (act μ E k f) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (act μ E k f) x = ∫ y : G n, Ld X k y.val (f (x * y.val)) ∂μ

def IBPAct : Prop :=
  Unimod → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ∀ X, ∀ x ∈ GLs n, ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ = -∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ

def KapEquiv : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ (k : Mat n → (E.V →L[ℂ] E.V)),
    ContDiffOn ℝ ∞ k (GLs n) → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂) →
    ContinuousOn (kapL ε Fr k) (GLs n) ∧ ContinuousOn (kapR ε Fr k) (GLs n) ∧
    ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      kapL ε Fr k (y * k₂.1) = kapL ε Fr k y * E.ρ k₂ ∧ kapR ε Fr k (y * k₂.1) = kapR ε Fr k y * E.ρ k₂

end PositivityTheory.RgBcC.LfSt.ChainPf
end
end
