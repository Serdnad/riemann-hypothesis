module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeEmbed.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ),
    (∀ (n : ℕ) (f : CombC S (negSet a) n),
      KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
        embed S a (n + 1) (combD S (negSet a) n f)) ∧
    (∀ (c d : K → ℤ), blockSum a = c + d → ∀ (n : ℕ) (f : CombC S (negSet a) n),
      embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) ∧
    ((∀ p, 0 ≤ a p) → ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def MulQuotEq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (s : Ω),
    (∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) →
    (∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I) →
    (∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) →
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧
        primeOf (S := k) x ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDiffPoly.Statement : Prop :=
  ∀ (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) (μ : Fin t → ℤ),
    IsNumPolyLT t D (fun n c => f n (c + 1) - f n c) →
    (∀ j, IsNumPolyLT t D (fun n c => f (Function.update n j (n j + 1)) (c + μ j) - f n c)) →
    IsNumPolyLT t (D + 1) f

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperHyperplane.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp → ∀ a : ℤ,
    ∃ (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp ≤ qq m ∧
        (X i : Poly k N) ∈ qq m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L n (c + 1) - pieceChar k pp a L n c = ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotAdd.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ F₃ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    (∀ I, F₃.sub I ≤ F₂.sub I) →
    eulerCharQuot k F₁.toSubSystem F₃.toSubSystem =
      eulerCharQuot k F₁.toSubSystem F₂.toSubSystem + eulerCharQuot k F₂.toSubSystem F₃.toSubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerCharQuot k
            ((F₁.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
            ((F₂.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v'

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

structure QuotIso {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    {E' : Type v'} [AddCommGroup E'] [Module Ω E'] [Module S E'] [IsScalarTower S Ω E']
    (F₁ F₂ : SubSystem S x E) (G₁ G₂ : SubSystem S x E') where

  equiv : ∀ I : Chart x,
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[S] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I)

  comm : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I),
    equiv J (SubSystem.quotRes F₁ F₂ I J h y) = SubSystem.quotRes G₁ G₂ I J h (equiv I y)

end Defs

def SnapperQuotIso.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (E' : Type v') [AddCommGroup E'] [Module Ω E'] [Module k E'] [IsScalarTower k Ω E']
    (F₁ F₂ : SubSystem k x E) (G₁ G₂ : SubSystem k x E'), QuotIso F₁ F₂ G₁ G₂ →
    eulerCharQuot k F₁ F₂ = eulerCharQuot k G₁ G₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperSection.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ (t : ℕ) (L : Fin t → LineBundle k x) (j : Fin t) (a : ℤ),
    ∃ (μ : ℤ) (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp < qq m) ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) - pieceChar k pp a L n c =
          ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem quotH_zero_subsingleton_of_irrelevant (F : SubSystem S x Ω) (pp : Ideal (Poly S N))
    (hpp : ∀ i, (X i : Poly S N) ∈ pp) :
    Subsingleton (SubSystem.quotH F (F.twist (idealSys x pp)) 0) := by
  have hsub : ∀ I : Chart x,
      Subsingleton (F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    change ((a - b : F.sub I) : Ω) ∈ (F.twist (idealSys x pp)).sub I
    rw [SubSystem.twist_sub_eq_mul_of_line]
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
        isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
    simpa using Submodule.mul_mem_mul h1 (a - b).2
  have hC : Subsingleton (Cech.Cochain (fun I : Chart x =>
      F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) 0) := by
    unfold Cech.Cochain
    exact ⟨fun a b => funext fun I => (hsub I.1).elim _ _⟩
  unfold SubSystem.quotH Cech.H
  infer_instance

end

theorem SectionCount.Drop.Filt.Finite.proof
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hFS : FiniteSections.Statement.{u, w}) :
    SectionCount.Drop.Filt.Finite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q pp c hpp hhom hle
  by_cases hirr : ∀ i, (X i : Poly S N) ∈ pp
  · have := quotH_zero_subsingleton_of_irrelevant (Q.twist (twistSys S x c)) pp hirr
    infer_instance
  push Not at hirr
  obtain ⟨j, hj'⟩ := hirr
  have hj : x j ≠ 0 := fun h0 => hj' (hle (by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X S j), aeval_X, h0]))
  have hPtj := PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hj'

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type w) (_ : Field K') (_ : Algebra S K')
      (ψ : chartRing S x (singleChart hj) →ₐ[S] K'), RingHom.ker ψ = chartPrime pp hj := by
    have : (chartPrime pp hj).IsPrime := hPtj.1
    have : IsDomain (chartRing S x (singleChart hj) ⧸ chartPrime pp hj) := Ideal.Quotient.isDomain _
    refine ⟨FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom S _ _).comp (Ideal.Quotient.mkₐ S (chartPrime pp hj)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj))
      (Ideal.Quotient.mk (chartPrime pp hj) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := S) hj i = 0 := Subtype.ext (show x i / x j = 0 by rw [h0, zero_div])
    rw [this, map_zero]
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 j
    rw [ratio_self hj ψ] at h1
    exact one_ne_zero h1

  obtain ⟨Q', r, hr⟩ := PrimeFiltration.Restrict.proof S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q
  have hRD : RestrictData Q.toSubSystem hxy Q'.toSubSystem r :=
    ⟨fun I => (hr I).1, fun I => (hr I).2.1, fun I => (hr I).2.2.1, fun I => (hr I).2.2.2⟩
  obtain ⟨E1⟩ := hRQ S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q Q' r hRD c 0

  obtain ⟨E2⟩ := hH0 S K' N _ K' (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)) hy0
  have hfin := (hFS S K' N _ (Q'.tensorProd (twistBundle S _ c)) hy0).1
  have hfin' : Module.Finite S (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)).secs := hfin
  exact Module.Finite.equiv (E1.trans E2).symm
end
end Kleiman
end Heights
end Heights₂
end GroundTheory
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
end
