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

open Filter

noncomputable section

universe u w

def SectionCount.Top.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) (d + 1) → IsVeryAmple Nb.toSubSystem →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionMulInj.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp →
    ∀ (D M : LineBundle k x) (s : Ω), (∃ f ∈ zeroIdeal D.toSubSystem s, f ∉ pp) →
    ∀ (I : Chart x), ∀ y ∈ M.sub I,
      s * y ∈ ((M.toSubSystem.twist D.toSubSystem).twist (idealSys x pp)).sub I →
      y ∈ (M.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionNonvanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ D : LineBundle k x, D.toSubSystem.Generated →
    ∃ s ∈ D.toSubSystem.secs, ∃ I, s ∉ (D.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ClaimSeq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x),
    ∃ Jg : FinGradedSub (S := k) (x := x) Ω,
      (∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
        f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) ∧
      ∀ (b : ℕ) (c : ℤ) (I : Chart x) (z : Ω),
        z ∈ ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I ↔
          ∃ y ∈ ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I, z = T.si * y

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def CycleSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    (∀ G ∈ J.minimalPrimes, ringKrullDim (Poly S N ⧸ G) ≤ 2) →
    ∀ᶠ c : ℕ in atTop,
      interSum J ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ J.minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult J G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Curve.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ G : Ideal (Poly S N), IsSubvar x G 1 → 𝔪.map (C : S →+* Poly S N) ≤ G →
    ∀ᶠ c : ℕ in atTop, interSum G ![M.toSubSystem] c = interNum G ![M.toSubSystem]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def CycleSplit.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    ∃ (n : ℕ) (pp : Fin n → Ideal (Poly S N)) (d : Fin n → ℤ),
      (∀ j, (pp j).IsPrime ∧ (∀ p ∈ pp j, ∀ e : ℕ, homogeneousComponent e p ∈ pp j) ∧ J ≤ pp j) ∧
      (∀ (G : Ideal (Poly S N)) [G.IsPrime], G ∈ J.minimalPrimes →
        (((Finset.univ.filter fun j => pp j = G).card : ℕ) : ℕ∞) = cutMult J G) ∧
      ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
        restrLen J (Q.twist (twistSys S x (c : ℤ))) =
          ∑ j, restrLen (pp j) (Q.twist (twistSys S x ((c : ℤ) + d j)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Small.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ pp : Ideal (Poly S N), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → 𝔪.map (C : S →+* Poly S N) ≤ pp → ringKrullDim (Poly S N ⧸ pp) ≤ 1 →
    ∀ᶠ c : ℕ in atTop, interSum pp ![M.toSubSystem] c = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def IdealTwistFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ F : SubFamily S x Ω, F.toSubSystem = Q.twist (idealSys (x := x) J') ∧ ∀ I, (F.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def RestrictGenerated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (pp : Ideal (Poly S N)), primeOf (S := S) x ≤ pp → primeOf (S := S) y = pp →
    ∀ (Q : LineBundle S x) (Q' : LineBundle S y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r → Q'.toSubSystem.Generated →
      ∀ I : Chart x, Q.toSubSystem.sub I ≤
        Submodule.span (chartRing S x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
          z = s I} ⊔ (Q.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubSystem.twistPows (F : SubSystem S x E) : (t : ℕ) → (Fin t → SubSystem S x Ω) → (Fin t → ℕ) → SubSystem S x E
  | 0, _, _ => F
  | t + 1, L, n => (F.twistPows t (fun j => L j.castSucc) (fun j => n j.castSucc)).twist ((L (Fin.last t)).pow (n (Fin.last t)))

variable (k : Type u) [Field k] [Algebra k Ω] [Module k E] [IsScalarTower k Ω E]

def eulerChar (F : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (F.H i) : ℤ)

end Defs

def SnapperFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x)
    (n : Fin t → ℕ) (c : ℤ) (i : ℕ),
    FiniteDimensional k (((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c)).H i)

def Snapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ),
    IsSubvar x (primeOf (S := k) x) e →
    ∀ (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
      (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x),
    ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, Q.totalDegree ≤ e ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        ((eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
          (twistSys k x c)) : ℤ) : ℚ) =
          MvPolynomial.eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

def TwistVanishAll.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω),
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ c₀ : ℤ, ∀ (i b : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton (((G.twist (B.pow b)).twist (twistSys S x c)).H i)

def AmpleVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ H : LineBundle S x, IsVeryAmple H.toSubSystem →
    ∃ a₀ : ℕ, ∀ (i a : ℕ), 1 ≤ i → a₀ ≤ a → Subsingleton ((F.twist (H.pow a)).H i)

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

def StepThree.Away.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (b : ℕ) (c : ℤ), 0 ≤ c → ∀ I : Chart x,
      ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ^ b •
          ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω)

end

end GroundTheory.Heights₂.Heights.Kleiman
end
