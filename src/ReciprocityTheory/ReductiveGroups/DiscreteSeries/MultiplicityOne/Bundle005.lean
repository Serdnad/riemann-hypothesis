module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepsA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle002
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StDiagExists : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    IsCRepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → ContinuousOn π (UWset k r z) →
    Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    ∃ D : RealPlaceData k r Wp Wp, D.z = z ∧ D.π = π ∧ IsDiag D

def StSchurG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∃ d : ℝ, IsFdegG D X d

def StPairs : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ d : ℝ, IsFdegG D X d → ∀ a₁ a₂ : ℝ, ∀ u ∈ VflA X a₁, ∀ v ∈ VflA X a₂,
      ∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-(min a₁ a₂ - AG k r - 1))

def StBeConv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ (b : ℝ), AS k r + 1 ≤ b → ∀ u v : X.Hs,
      (∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-b)) →
      Integrable (beInt D X u v) (D.μW.prod D.μN)

def StBeEquiv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u u' : X.Hs, Integrable (beInt D X u u') (D.μW.prod D.μN) →
      ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u') ∧
        beOp D X u (X.σ (m * h) u') = star (psiD D m) • (beOp D X u u').comp (D.π h⁻¹)

def StRepro : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ d : ℝ, IsFdegG D X d → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X,
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG ∧
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG

def StSmooth : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ φ φ' : Mat k r → ℂ, IsTestG φ → IsTestG φ' → ∀ m : ℕ,
      InCC (X.a - AG k r - 1) m (mc X (sigInt D X φ X.w) (sigInt D X φ' X.w))

def StFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    ∃ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r z γ

def StInvGroup : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ g ∈ GV k r, gbar k r γ g ∈ GV k r) ∧ (∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r) ∧
    (∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z) ∧ (∀ u ∈ UUset k r D.z γ, gbar k r γ u ∈ UUset k r D.z γ) ∧
    (∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g) ∧
    (∀ g ∈ GV k r, th k r γ (th k r γ g) = g) ∧
    D.μG.map (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = D.μG ∧
    D.μN.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μN ∧
    D.μW.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μW

def StInvChar : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m ∧ psiD D (th k r γ m) = psiD D m

def StInvCC : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∃ C : ℝ, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g) ∧
    ∀ (A : ℝ) (m : ℕ) (F : Mat k r → ℂ), InCC A m F → InCC A m (F ∘ th k r γ)

def StReps : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (c : Fin r → ℂ) (d : ℂ), (∀ a, c a ≠ 0) → 1 < ‖d‖ →
      (γ * mud k d * γ⁻¹)ᴴ * Hb k * (γ * mud k d * γ⁻¹) = Hb k ∧
      herm (Hpk k r) (embWb k r (γ * mud k d * γ⁻¹) *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d ∧
      g0 k r γ c d ∈ GV k r ∧ th k r γ (g0 k r γ c d) = g0 k r γ c d ∧
      ∃ h ∈ UWset k r D.z, ∃ h' ∈ UWset k r D.z, gq D (c, -((Tz k r D.z : ℝ) : ℂ) * d) = h⁻¹ * g0 k r γ c d * h'

def StTransM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹

def StSym : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (f : Mat k r → ℂ) (q : (Fin r → ℂ) × ℂ), Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG →
      q ∈ Qset D → Tz k r D.z * Tz k r D.z < Complex.normSq q.2 → Ef D (scalF Wp f) q ≠ ∞ →
      JF D (scalF Wp (f ∘ th k r γ)) (gq D q) = JF D (scalF Wp f) (gq D q)

def StSymBeta : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ A : ℝ, AB k r ≤ A → JCont D A → ∀ (f : Mat k r → ℂ) (F' : Mat k r → (Wp →L[ℂ] Wp)),
      InCC A 5 f → InCC A 5 F' → beta D (scalF Wp (f ∘ th k r γ)) F' = beta D (scalF Wp f) F'

def StBetaInf : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    XiExists → AB k r ≤ A → ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      Integrable (Ph D F F') D.μSS → betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS

def StDichoG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) ∨
    ∃ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs, (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) ∧
      ∀ h ∈ GV k r, ∀ v : X.Hs, C (X.σ h v) = X.σ (th k r γ h)⁻¹ (C v)

def StDichoW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : Wp,
      ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ * star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) ∨
    ∃ C : Wp ≃ₗᵢ⋆[ℂ] Wp, (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C x, D.π h (C y)⟫_ℂ) ∧
      ∀ h ∈ UWset k r D.z, ∀ v : Wp, C (D.π h v) = D.π (th k r γ h)⁻¹ (C v)

def StMixed : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    aM k r ≤ X.a → ∀ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs,
      (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) →
      ∀ u ∈ Vfl X, C u ∈ VflA X (X.a - AG k r - 1)

def ThmM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∃ l : X.Hs → Wp, IsMultOneMap D X l

def StMFix : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ W' : Mat k r → Wp, AEStronglyMeasurable (fun y : Mt k r => W' (Matrix.of y)) D.μG →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, W' (m * h * x) = psiD D m • D.π h (W' x)) →
        (∀ x ∈ GV k r, Integrable (fun y : Mt k r => gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) D.μG) →
        ∃ c : ℂ, ∀ x ∈ GV k r,
          ∫ y : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of y))) • W' (x * Matrix.of y) ∂D.μG = c • l (X.σ x X.w)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

theorem zero_ne_last (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h2
  omega

def sgd (d : ℂ) : ℂ := ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)

theorem sgd_sq (d : ℂ) (hd : 1 < ‖d‖) : sgd d * sgd d = d * conj d - 1 := by
  have hx : 0 ≤ Complex.normSq d - 1 := by
    have h1 : 1 < Complex.normSq d := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg d]
    linarith
  unfold sgd
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_one]

theorem star_sgd (d : ℂ) : star (sgd d) = sgd d := by
  unfold sgd
  exact Complex.conj_ofReal _

section entries
variable (hk : 1 ≤ k) (d : ℂ)
include hk

theorem character_first_entry : mud k d 0 0 = -conj d := by
  unfold mud
  simp
theorem character_last_entry : mud k d (Fin.last k) 0 = -sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.1.symm), if_pos ⟨rfl, rfl⟩]
theorem mud0L : mud k d 0 (Fin.last k) = sgd d := by
  have h0 := zero_ne_last hk
  unfold mud sgd
  rw [if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1), if_pos ⟨rfl, rfl⟩]
theorem mudLL : mud k d (Fin.last k) (Fin.last k) = d := by
  have h0 := zero_ne_last hk
  unfold mud
  rw [if_neg (fun h => h0 h.1.symm), if_neg (fun h => h0 h.2.symm), if_neg (fun h => h0 h.1.symm),
    if_pos ⟨rfl, rfl⟩]

theorem mud_col {l j : Fin (k + 1)} (hj0 : j ≠ 0) (hjL : j ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hj0 h.2), if_neg (fun h => hj0 h.2), if_neg (fun h => hjL h.2),
    if_neg (fun h => hjL h.2)]

theorem mud_row {l j : Fin (k + 1)} (hl0 : l ≠ 0) (hlL : l ≠ Fin.last k) :
    mud k d l j = if l = j then 1 else 0 := by
  unfold mud
  rw [if_neg (fun h => hl0 h.1), if_neg (fun h => hlL h.1), if_neg (fun h => hl0 h.1),
    if_neg (fun h => hlL h.1)]

theorem sum_two {f : Fin (k + 1) → ℂ} (hf : ∀ l, l ≠ 0 → l ≠ Fin.last k → f l = 0) :
    ∑ l, f l = f 0 + f (Fin.last k) := Finset.sum_eq_add 0 (Fin.last k) (zero_ne_last hk) (fun c _ hc => hf c hc.1 hc.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

theorem mul_mud_col (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i j : Fin (k + 1)} (hj0 : j ≠ 0)
    (hjL : j ≠ Fin.last k) : (P * mud k d) i j = P i j := by
  rw [Matrix.mul_apply]
  simp [mud_col hk d hj0 hjL]

theorem mul_mud_blk (P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) (hj : j = 0 ∨ j = Fin.last k) :
    (P * mud k d) i j = P i 0 * mud k d 0 j + P i (Fin.last k) * mud k d (Fin.last k) j := by
  rw [Matrix.mul_apply]
  apply sum_two hk
  intro l hl0 hlL
  rw [mud_row hk d hl0 hlL, if_neg, mul_zero]
  rintro rfl
  rcases hj with h | h
  · exact hl0 h
  · exact hlL h

end entries

theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then (if i = Fin.last k then -1 else 1) else 0 := by
  unfold Hb
  rw [Matrix.diagonal_apply]

theorem mud_unitary (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d)ᴴ * Hb k * mud k d = Hb k := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  ext i j
  have hP : ∀ a b : Fin (k + 1), ((mud k d)ᴴ * Hb k) a b = star (mud k d b a) * (if b = Fin.last k then -1 else 1) := by
    intro a b; unfold Hb; rw [mul_diagonal, conjTranspose_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, character_first_entry hk, character_last_entry hk, if_true, if_neg h0L, if_neg h0L.symm, hss,
        Complex.star_def]
      ring
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hi0]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hP, hP, Hb_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, character_last_entry hk, mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, star_neg, hss, Complex.star_def,
        Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [mud0L hk, mudLL hk, if_true, if_neg h0L, if_neg h0L.symm, hss, Complex.star_def]
      linear_combination hs
    · simp only [mud_col hk d hi0 hiL, if_neg (Ne.symm hi0), if_neg (Ne.symm hiL), if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hP, mud_row hk d hj0 hjL, Hb_apply]
    by_cases hij : i = j
    · subst hij; simp [hjL]
    · rw [if_neg (Ne.symm hij), if_neg hij]; simp

theorem mud_conj_mul (hk : 1 ≤ k) (d : ℂ) (hd : 1 < ‖d‖) : (mud k d).map (starRingEnd ℂ) * mud k d = 1 := by
  have hs := sgd_sq d hd
  have hss := star_sgd d
  have h0L := zero_ne_last hk
  have hc : ∀ a b : Fin (k + 1), ((mud k d).map (starRingEnd ℂ)) a b = conj (mud k d a b) := fun a b => rfl
  have hsc : conj (sgd d) = sgd d := hss
  ext i j
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [mul_mud_blk hk d _ _ _ (Or.inl rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, character_last_entry hk, if_true, map_neg, hsc, Complex.conj_conj]
      linear_combination -hs
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, character_first_entry hk, if_neg h0L.symm, map_neg, hsc]
      ring
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  rcases eq_or_ne j (Fin.last k) with rfl | hjL
  · rw [mul_mud_blk hk d _ _ _ (Or.inr rfl), hc, hc, Matrix.one_apply]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [character_first_entry hk, mud0L hk, mudLL hk, if_neg h0L, if_neg h0L.symm, map_neg, hsc, Complex.conj_conj]
      ring
    rcases eq_or_ne i (Fin.last k) with rfl | hiL
    · simp only [character_last_entry hk, mudLL hk, mud0L hk, if_true, map_neg, hsc]
      linear_combination -hs
    · simp only [mud_row hk d hi0 hiL, if_neg hi0, if_neg hiL]
      simp
  · rw [mul_mud_col hk d _ hj0 hjL, hc, mud_col hk d hj0 hjL, Matrix.one_apply]
    split_ifs <;> simp

theorem herm_mulVec {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    herm H (A *ᵥ u) (A *ᵥ v) = herm (Aᴴ * H * A) u v := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (u v : Fin n → ℂ) :
    herm H (a • u) (b • v) = a * conj b * herm H u v := by
  unfold herm
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem herm_mud_last (hk : 1 ≤ k) (d : ℂ) :
    herm (Hb k) (mud k d *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -d := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp [Pi.single_apply, Hb_apply, mudLL hk d]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wbE_smul {r : ℕ} (a : ℂ) (v : Fin (k + 1) → ℂ) : wbE k r (a • v) = a • wbE k r v := by
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [wbE, h]

theorem bvec_wI {r : ℕ} (j : Fin (k + 1)) : bvec (wI k r j) = wbE k r (Pi.single j 1) := by
  funext i
  simp only [bvec, wI, wbE, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

end ReciprocityTheory.ChartRestriction.DS.Mult1.RepsA
end
end
