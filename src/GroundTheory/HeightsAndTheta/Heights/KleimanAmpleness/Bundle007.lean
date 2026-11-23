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

universe u w

def CutOneGenerator.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs →
    ¬ ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), L.sub (singleChart hj) ≤
      (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
        Submodule.span (chartRing k x (singleChart hj)) {s}

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutZeroNotLe.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp e →
    s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ f ∈ zeroIdeal L.toSubSystem s, f ∉ pp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ (K pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ K, ∀ d : ℕ, homogeneousComponent d f ∈ K) → primeOf (S := S) x ≤ K →
    𝔪.map (C : S →+* Poly S N) ≤ K → g.IsHomogeneous e →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → (∀ f, f ∈ pp ↔ f * g ∈ K) →
    ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen K (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (K ⊔ Ideal.span {g}) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen pp (Q.twist (twistSys S x ((c : ℤ) - e)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GraphClosed.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G H : LineBundle k x), G.toSubSystem.Generated → IsVeryAmple H.toSubSystem →
    IsVeryAmple (G.toSubSystem.twist H.toSubSystem)

def PointGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x), IsSubvar x (primeOf (S := k) x) 0 → Q.toSubSystem.Generated

section Hypotheses

variable (k : Type u) [Field k]

theorem generated_twistSys_zero' {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by
  have h1 : (1 : Ω) ∈ (twistSys S x 0).secs := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact one_mem_twistMod_zero I
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hz
    exact hz I
  · change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr h1)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 → ∀ L : Fin 0 → SubSystem k y Ω,
      interNum (primeOf (S := k) y) L = (Module.finrank k (funField (k := k) y) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (n : ℕ), IsSubvar y pp n →
    ∀ (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y) (r : Fin n → Ω → K'),
      (∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (r i)) →
      interNum pp (fun i => (L' i).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def LeadingCoeffPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M Nb : LineBundle k x) (q : ℕ) (m : ℤ) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    Nef M.toSubSystem → Nb.toSubSystem = twistMul M.toSubSystem q m → IsVeryAmple Nb.toSubSystem →
    ((d + 1 : ℕ) : ℤ) * b < m →
    0 < interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotTrans.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ F₃ : SubSystem S x E), (∀ I, F₃.sub I ≤ F₂.sub I) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    Subsingleton (SubSystem.quotH F₂ F₃ 1) → Subsingleton (SubSystem.quotH F₁ F₂ 1) →
    Subsingleton (SubSystem.quotH F₁ F₃ 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (e : ℕ), IsSubvar y pp e →
    ∀ (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∀ᶠ c : ℕ in atTop, restrLen pp (Q'.toSubSystem.twist (twistSys k y (c : ℤ))) =
        restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Kernel.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (j : Fin (N + 1)) (b : ℕ) (F : SubSystem S x Ω), x j ≠ 0 →
    (∀ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, x j ^ b * t ∈ F.secs) ∧
    ∀ s ∈ (F.twist (idealSys x (primeOf (S := S) x ⊔
        zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)))).secs,
      ∃ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, s = x j ^ b * t

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) -
          (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℝ) ≤
        (interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℝ) * (n : ℝ) ^ d / (d.factorial : ℝ) +
          C * (n : ℝ) ^ d / n

end

end GroundTheory.Heights₂.Heights.Kleiman
end
