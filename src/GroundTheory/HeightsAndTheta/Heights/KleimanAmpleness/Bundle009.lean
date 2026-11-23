module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def LineTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q₁ Q₂ : LineBundle S x), ∃ Q : LineBundle S x, Q.toSubSystem = Q₁.toSubSystem.twist Q₂.toSubSystem

def TwistAlg.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (M : SubSystem S x Ω) (p q : ℕ) (m m' : ℤ) (b₁ b₂ : ℕ), (q : ℤ) * m = p * m' →
    (twistMul M p m).pow (q * b₁ + b₂) =
      ((twistMul M p m).pow b₂).twist ((twistMul M q m').pow (p * b₁))

def RestrictTwist.Statement : Prop :=
  (∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := S) x ≤ primeOf (S := S) y → ∀ c : ℤ,
      ∃ r : Ω → K', RestrictData (twistSys S x c) hxy (twistSys S y c) r) ∧
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (Q₁ Q₂ : LineBundle S x) (Q₁' Q₂' : LineBundle S y) (r₁ r₂ : Ω → K'),
    RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁ →
    RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂ →
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r

def NefRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (M : LineBundle k x) (M' : LineBundle k y) (r : Ω → K'),
      RestrictData M.toSubSystem hxy M'.toSubSystem r → Nef M.toSubSystem → Nef M'.toSubSystem

def StepData.JProper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ f ∉ primeOf (S := k) x

def SubvarDrop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (d : ℕ) (pp : Ideal (Poly k N)), IsSubvar x (primeOf (S := k) x) (d + 1) → pp.IsPrime →
    (∀ p ∈ pp, ∀ n : ℕ, homogeneousComponent n p ∈ pp) → primeOf (S := k) x ≤ pp →
    (∃ j, (X j : Poly k N) ∉ pp) → (∃ f ∈ pp, f ∉ primeOf (S := k) x) → ∃ e ≤ d, IsSubvar x pp e

def StepTwo.Reduce.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (pr : Fin n → Ideal (Poly S N)) (sh : Fin n → ℤ),
      (∀ i, (pr i).IsPrime ∧ (∀ p ∈ pr i, ∀ d : ℕ, homogeneousComponent d p ∈ pr i) ∧
        primeOf (S := S) x ≤ pr i ∧
        ∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr i) ∧
      ∀ (Q : LineBundle S x) (c : ℤ),
        (∀ i, (∃ j, (X j : Poly S N) ∉ pr i) →
          Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c + sh i)))
            ((Q.twist (twistSys S x (c + sh i))).twist (idealSys x (pr i))) 1)) →
        Subsingleton (SubSystem.quotH ((M₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
          ((M₂.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TildeTail.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : FinGradedSub (S := S) (x := x) Ω), x ≠ 0 →
    ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (M.tildeSys (deg j)).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (M.tildeSys c).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j}

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M : FinGradedSub (S := S) (x := x) E),
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ZeroIdealChart.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (I : Chart x) (y : Ω),
    (∀ δ ∈ T.D.sub I, y * δ ∈ chartRing k x I) → T.si * y ∈ idealMod (x := x) T.J I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Piece.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (N₀ N₁ : FinGradedSub (S := S) (x := x) E) (g : E) (e : ℤ)
    (pp : Ideal (Poly S N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → g ∈ N₁.piece e →
    (∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g}) →
    (∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) →
    ∀ (Q : LineBundle S x) (c : ℤ),
      ((∃ j, (X j : Poly S N) ∉ pp) →
        Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
          ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1)) →
      Subsingleton (SubSystem.quotH ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
        ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


variable (S x E) in
def FinGradedSub.zero : FinGradedSub (S := S) (x := x) E where
  piece _ := ⊥
  smul_mem _ _ _ m _ hm := by
    rw [Submodule.mem_bot] at hm ⊢
    rw [hm, smul_zero]
  fg := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun _ => bot_le⟩

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeFiniteE.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (i : ℕ) (c : ℤ),
    Module.Finite S ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TildeFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : FinGradedSub (S := S) (x := x) Ω) (i : ℕ) (c : ℤ),
    Module.Finite S ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeShift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (c : ℤ),
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistTilde.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω),
    ∃ P : FinGradedSub (S := S) (x := x) E,
      (∀ c : ℤ, P.piece c = Submodule.span S {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧
        m ∈ M.piece b ∧ a + b = c ∧ z = q • m}) ∧
      ∀ I, ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = P.tilde 0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleCech.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, (∀ J, (F'.sub J).FG) ∧ ∀ a i : ℕ,
      Nonempty ((F.twist (H.pow a)).H i ≃ₗ[S] (F'.twist (twistSys S h (a : ℤ))).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleDegree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h →
    interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleDim.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h → IsSubvar h (primeOf (S := k) h) e

end

end GroundTheory.Heights₂.Heights.Kleiman
end
