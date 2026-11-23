module

public import Formalism.HermitianCurvature.StatementU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {N : ℕ}

theorem pd_mono {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : a ≤ b) (hP : IsPolyDeg a P) :
    IsPolyDeg b P := by
  obtain ⟨q, hq, he⟩ := hP
  exact ⟨q, hq.trans h, he⟩

theorem pd_const (c : ℂ) : IsPolyDeg (N := N) 0 (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg b Q) :
    IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_cmul {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => c * P g) := by
  have h := pd_mul (pd_const c) hP
  rwa [zero_add] at h

theorem pd_mulc {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => P g * c) := by
  have h := pd_mul hP (pd_const c)
  rwa [add_zero] at h

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg a (P i)) : IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact pd_mono (Nat.zero_le a) (pd_const 0)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact pd_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg (d i) (P i)) : IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact pd_const 1
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact pd_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_X (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g a b) :=
  ⟨MvPolynomial.X (Sum.inl (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_Xs (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g a b)) :=
  ⟨MvPolynomial.X (Sum.inr (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_det (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => M g i j)) : IsPolyDeg n (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  refine pd_sum _ _ fun σ _ => pd_cmul _ ?_
  have h2 := pd_prod (Finset.univ : Finset (Fin n)) (fun _ => 1) (fun i g => M g (σ i) i)
    (fun i _ => h (σ i) i)
  simpa using h2

theorem pd_det_star (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => star (M g i j))) : IsPolyDeg n (fun g => star (M g).det) := by
  have e : (fun g => star (M g).det) = fun g => ((M g).map (starRingEnd ℂ)).det := by
    funext g
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, starRingEnd_apply]
  rw [e]
  exact pd_det n _ fun i j => h i j

theorem pd_herm (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => herm H (g *ᵥ v) w) := by
  simp only [herm, dotProduct, mulVec]
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => pd_mulc _ (pd_X j l)))

theorem pd_herm_star (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (herm H (g *ᵥ v) w)) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul']
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => isPolyDeg_one_conj_entry_mul j l))
where
  isPolyDeg_one_conj_entry_mul (j l : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g j l) * star (v l)) :=
    pd_mulc _ (pd_Xs j l)

end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
def costP (k j ρ : ℕ) (X : B.Mat k (j + ρ)) : ℕ := if inLieP k j ρ X then 0 else j

def WB {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (cost : B.Mat k r → ℕ)
    (φ : B.Mat k r → E) (n : ℕ) (C e : ℝ) : Prop :=
  ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    u.length + v.length ≤ n → ∀ g ∈ B.GV k r,
      ‖B.dLR u v φ g‖ ≤ C * B.gN g ^ (e + ((((u ++ v).map cost).sum : ℕ) : ℝ))

def DjCurve : Prop :=
  ∀ (k j ρ : ℕ) (Y : B.Mat k (j + ρ)), inLieP k j ρ Y → ∃ c₁ c₂ : ℂ,
    ‖c₁‖ ≤ (j : ℝ) * mx Y ∧ ‖c₂‖ ≤ (j : ℝ) * mx Y ∧
    ∀ (g : B.Mat k (j + ρ)) (t : ℝ),
      DjU k j ρ (g * NormedSpace.exp ((t : ℂ) • Y)) = Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g ∧
      DjU k j ρ (NormedSpace.exp (-((t : ℂ) • Y)) * g) = Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g

def PolyB : Prop :=
  ∀ (k r κ : ℕ) (P : B.Mat k r → ℂ), IsPolyDeg κ P →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P ∧ ∀ n : ℕ, ∃ C : ℝ, WB (fun _ => 0) P n C κ

def DjPoly : Prop := ∀ k j ρ : ℕ, IsPolyDeg j (DjU k j ρ)

def GfPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), IsPolyDeg (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ))

def CompC : Prop :=
  ∀ (k r : ℕ) (ψ : B.Mat k r → ℂ) (χ : ℂ → ℂ) (cost : B.Mat k r → ℕ) (n : ℕ) (C₀ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ n → u ++ v ≠ [] → ∀ g ∈ B.GV k r, ψ g ∈ tsupport χ →
        ‖B.dLR u v ψ g‖ ≤ C₀ * B.gN g ^ ((((u ++ v).map cost).sum : ℕ) : ℝ)) →
    ∃ C : ℝ, WB cost (fun g => χ (ψ g)) n C 0

def CompR : Prop :=
  ∀ (k r : ℕ) (ψ : B.Mat k r → ℝ) (h : ℝ → ℝ) (cost : B.Mat k r → ℕ) (n : ℕ) (C₀ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
    (∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ n → u ++ v ≠ [] → ∀ g ∈ B.GV k r,
        ‖B.dLR u v (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * B.gN g ^ ((((u ++ v).map cost).sum : ℕ) : ℝ)) →
    ∃ C : ℝ, WB cost (fun g => ((h (ψ g) : ℝ) : ℂ)) n C 0

def WBmul : Prop :=
  ∀ (k r : ℕ) (φ₁ φ₂ : B.Mat k r → ℂ) (c₁ c₂ : B.Mat k r → ℕ) (n : ℕ) (C₁ C₂ e₁ e₂ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₂ →
    WB c₁ φ₁ n C₁ e₁ → WB c₂ φ₂ n C₂ e₂ → ∃ C : ℝ, WB (c₁ + c₂) (fun g => φ₁ g * φ₂ g) n C (e₁ + e₂)

def DjWB : Prop :=
  ∀ (k j ρ : ℕ) (χ : ℂ → ℂ) (n : ℕ), IsCutC χ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => χ (DjU k j ρ g)) ∧
      ∃ C : ℝ, WB (costP k j ρ) (fun g => χ (DjU k j ρ g)) n C 0

def GfWB : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (χε : ℝ → ℝ) (ε : ℝ) (n : ℕ), IsCutG ε χε →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((χε (Gf k r z z' g) : ℝ) : ℂ)) ∧
      ∃ C : ℝ, WB (fun _ => 2 * (r + 1)) (fun g : B.Mat k r => ((χε (Gf k r z z' g) : ℝ) : ℂ)) n C 0

def CoreStar : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ d : ℕ) (Θ : B.DiffOp k (j + ρ) Wp Wq) (χ : ℂ → ℂ)
    (φ : B.Mat k (j + ρ) → ℂ),
    InDD k j ρ o κ Θ → IsCutC χ → ∀ (Q mm₀ : ℕ) (A₀ : ℝ), Q + o ≤ mm₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ g, DjU k j ρ g ∉ tsupport χ → φ g = 0) →
    (∃ Cφ : ℝ, WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) →
    ∃ C : ℝ, ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Star k j ρ (B.opApply Θ (fun g => φ g • f g))
        (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) Q (C * c)
        ((fun w : ℂ => ‖w‖) '' tsupport χ)

end PI.UnitaryCorollaryDerivatives
end
end
