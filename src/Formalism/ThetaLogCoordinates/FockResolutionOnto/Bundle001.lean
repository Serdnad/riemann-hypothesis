module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.ShiftLastLetterThresholds
public import Formalism.MahlerMeasure.Bundle005
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def FirstCoordinateRaisingCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]),
    F ∈ YCond p LL j M ↔
      ∀ l : List (Fin r), ((l.map fun c => glAct p LL j 0 c).prod) F ∈
        MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}

def MulEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), j ≤ K →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j M)

def MulLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), K + 1 ≤ j → LL.vec (Fin.last K) = true →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)))

def FilEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ f, f ∈ FilE p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        f = X (Fin.last K, ρ) ^ e * h

def FilBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → FilE p LLw J M ρ w (Fin.last K, ρ) e = ⊥

def GrEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ x, x ∈ grLat p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 h

def GrBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → grLat p LLw J M ρ w (Fin.last K, ρ) e = ⊥

end Formalism.InvariantFactorPaths.L4
end

section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

noncomputable def Wm (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  LinearMap.mulLeft ℚ_[p] (X (Fin.last K, a))

noncomputable def dW (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  (pderiv (Fin.last K, a)).toLinearMap

noncomputable def eulW (p : ℕ) [Fact p.Prime] (K r : ℕ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a : Fin r, Wm p K a ∘ₗ dW p K a

noncomputable def Uop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  Wm p K a ∘ₗ (((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K r) - ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b

noncomputable def Omega (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (ρ : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a ∈ univ.erase ρ, Uop p LL c (univ.erase ρ) a ∘ₗ dW p K a

def UComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a s t : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LL.vec (Fin.last K) = true → s ∈ Cs → t ∈ Cs →
    glAct p LL (K + 1) s t (Uop p LL c Cs a F) - Uop p LL c Cs a (glAct p LL (K + 1) s t F) =
      if t = a then Uop p LL c Cs s F else 0

def UKeepsLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (a : Fin r),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ), Uop p LL c univ a F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ)

def UKeepsEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r)
    (j : ℕ) (M : WithTop ℤ), j ≤ K →
    ∀ F ∈ YCond p LL j M, Uop p LL c Cs a F ∈ YCond p LL j M

def UDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) (o : ℕ),
    ∀ F ∈ Pol p r (setLast LL o), Uop p LL c Cs a F ∈ Pol p r (setLast LL (o + 1))

def ResU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (ρ a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), a ≠ ρ →
    initPart (Fin.last K, ρ) 0 (Uop p LL c univ a F) = Uop p LL c (univ.erase ρ) a (initPart (Fin.last K, ρ) 0 F)

def Sl2Injective : Prop :=
  ∀ (k V : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] (e f h : V →ₗ[k] V),
    (∀ x, h (e x) - e (h x) = (2 : k) • e x) → (∀ x, h (f x) - f (h x) = -((2 : k) • f x)) →
    (∀ x, e (f x) - f (e x) = h x) →
    ∀ (u : V) (μ : ℤ) (j : ℕ), h u = ((μ : ℤ) : k) • u → (∃ s : ℕ, (f ^ s) u = 0) → μ + j ≤ 0 → (e ^ j) u = 0 → u = 0

def EArith : Prop :=
  ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    1 ≤ ∑ a ∈ range s, β a →
    0 < (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
      ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ)

def OmegaInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    ∀ x ∈ Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓
        TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ),
      Omega p LL c ρ x = 0 → x = 0

end Formalism.InvariantFactorPaths.L4
end

section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def YCondDrop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (M : WithTop ℤ),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ Pol p r LL, F ∈ YCond p LL (K + 1) M → F ∈ YCond p LL K M

def ResInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 →
    ∀ h ∈ Y p LL J M, initPart (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ

def ResMM : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ResOntoK p LL J M ρ →
    ∀ x, x ∈ XH p LL J M ρ w ↔ ∃ h ∈ MMw p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = x

def ProjX : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ ((K + 3) * e1)) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)

def ProjAtOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 → HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 →
    ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ →
    ProjAt p LLw J M ρ w e ((K + 3) * e1)

end Formalism.InvariantFactorPaths.L4
end

section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def PartnerDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (k : ℕ) (g : Fin k → Vs) (D : ℝ),
    LinearIndependent ℤ_[p] g →
    (∀ u ∈ Submodule.span ℤ_[p] (Set.range g),
      (∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a) →
      ∃ u' ∈ Submodule.span ℤ_[p] (Set.range g), (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    (p : ℝ) ^ (-(D * k)) ≤ ‖(Matrix.of fun a b => be (g a) (g b)).det‖

def GradedPieceBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D c : ℕ) (κ : ℝ),
    ProjAt p LLw J M ρ w e D → SatAt p LLw J M ρ w e c → ((D + 2 * c : ℕ) : ℝ) ≤ κ →
    ∀ (k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
      (p : ℝ) ^ (-(κ * k)) ≤
        ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

end Formalism.InvariantFactorPaths.L4
end
