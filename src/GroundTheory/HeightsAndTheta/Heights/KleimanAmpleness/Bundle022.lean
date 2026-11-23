module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : AddMonoidAlgebra.coeff (X j * g - 1 : Poly k N) 0 = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_single (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by
  have hf : List.finRange 1 = [0] := rfl
  split_ifs with h
  · simp [tensorSub, hf, h, twistSys_zero_twist]
  · simp [tensorSub, hf, h]

end Helpers

theorem NefRestrict.proof (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def QuotSectionsFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x) (J : Ideal (Poly k N)),
    Module.Finite k (SubSystem.quotH Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotientH0Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F G : SubSystem S x E), (∀ I, G.sub I ≤ F.sub I) →
    Module.Finite S (F.H 0) → Module.Finite S (G.H 1) → Module.Finite S (SubSystem.quotH F G 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (pp : Ideal (Poly S N)) (c : ℤ), pp.IsPrime →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → primeOf (S := S) x ≤ pp →
    Module.Finite S (SubSystem.quotH (Q.twist (twistSys S x c))
      ((Q.twist (twistSys S x c)).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w


open Classical in
def SectionCount.Drop.Filt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) → 1 ≤ b →
    ∃ β ∈ (twistSys k x (b : ℤ)).secs,
      (∃ I, β ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub I) ∧
      ∃ (m : ℕ) (pp : Fin m → Ideal (Poly k N)) (e : Fin m → ℕ) (c : Fin m → ℤ),
        (∀ j, IsSubvar x (pp j) (e j) ∧ e j ≤ d ∧
          primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β ≤ pp j) ∧
        (∀ qq : Ideal (Poly k N),
          ((Finset.univ.filter fun j => e j = d ∧ pp j = qq).card : ℤ) =
            if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
                IsSubvar x qq d then
              haveI : qq.IsPrime := h.1.1.1
              ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ)
            else 0) ∧
        ∀ n i : ℕ,
          (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℤ) -
              (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℤ) ≤
            ∑ j, (Module.finrank k (SubSystem.quotH
              ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j)))
              (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j))).twist
                (idealSys x (pp j))) 0) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle S x) (J₁ pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) → primeOf (S := S) x ≤ J₁ →
    g.IsHomogeneous e → (∀ f, f ∈ pp ↔ f * g ∈ J₁) →
    ∃ φ : (Q.twist (idealSys x (J₁ ⊔ Ideal.span {g}))).secs →ₗ[S]
        SubSystem.quotH (Q.twist (twistSys S x (-(e : ℤ))))
          ((Q.twist (twistSys S x (-(e : ℤ)))).twist (idealSys x pp)) 0,
      ∀ s, φ s = 0 → (s : Ω) ∈ (Q.twist (idealSys x J₁)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.HilbW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (pp : Ideal (Poly k N)) (e : ℕ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
          ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) : ℝ) -
        (interNum pp (fun _ : Fin e => Nb.toSubSystem) : ℝ) * (m : ℝ) ^ e / (e.factorial : ℝ)| ≤
        C * (m : ℝ) ^ e / m

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def SectionCount.Drop.Term.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (b : ℕ) (pp : Ideal (Poly k N)) (e : ℕ) (c : ℤ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ c' : ℕ, ∀ n i : ℕ,
      Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
        ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0) ∧
      Module.finrank k (SubSystem.quotH
          ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c))
          (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c)).twist
            (idealSys x pp)) 0) ≤
        Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
          ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperSubquotFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F F₁ F₂ : SubFamily k x E), (∀ I, (F.sub I).FG) → (∀ I, F₁.sub I ≤ F.sub I) →
    (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ i : ℕ, FiniteDimensional k (SubSystem.quotH F₁.toSubSystem F₂.toSubSystem i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ I : Chart x,
      ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω) ⊔
          (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Gen.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ I : Chart x,
      ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ ((T.L.pow b).twist (twistSys k x c)).sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I₂) ∧ z = s I} ⊔
        (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end
