module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.RingTheory.Nullstellensatz
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle001
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ChartDehomogPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime W → linForm t ∉ W → (W ⊔ Ideal.span {linForm t - 1}).IsPrime

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

def LocalMultComap.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (I W : Ideal S),
    Function.Surjective σ → W.IsPrime → localMult (I.comap σ) (W.comap σ) = localMult I W

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeSliceIdeal.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)) (t : Fin n → ℂ) (V : Ideal (MvPolynomial (Fin n) ℂ)),
    (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) → MvPolynomial.vanishingIdeal ℂ C ≤ V →
      MvPolynomial.vanishingIdeal ℂ {x | x ∈ C ∧ MvPolynomial.eval x (linForm t) = 1} ≤
        V ⊔ Ideal.span {linForm t - 1}

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeVanishingHomog.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)), (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) →
    IsHomogIdeal (MvPolynomial.vanishingIdeal ℂ C)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

variable {n : ℕ}

def graphHom (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ)

def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  J.comap (graphHom p)

def graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.snoc x (eval x p)

theorem graphHom_X_castSucc (p : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom p (X (Fin.castSucc i)) = X i := by
  simp [graphHom]

theorem graphHom_X_last (p : MvPolynomial (Fin n) ℂ) : graphHom p (X (Fin.last n)) = p := by
  simp [graphHom]

theorem graphHom_rename (p q : MvPolynomial (Fin n) ℂ) : graphHom p (rename Fin.castSucc q) = q := by
  rw [graphHom, aeval_rename]
  have : (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ) ∘ Fin.castSucc = X :=
    funext fun i => by simp
  rw [this, aeval_X_left_apply]

theorem graphHom_surjective (p : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom p) :=
  fun q => ⟨rename Fin.castSucc q, graphHom_rename p q⟩

theorem eval_graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (graphPt p x) q = eval x (graphHom p q) := by
  have h : (eval (graphPt p x) : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) =
      (eval x).comp (graphHom p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [graphPt, graphHom]
      · simp [graphPt, graphHom]
  exact congrArg (fun φ : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => φ q) h

theorem graphPt_init (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin.init (graphPt p x) = x := by
  simp [graphPt]

theorem graphPt_last (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : graphPt p x (Fin.last n) = eval x p := by
  simp [graphPt]

theorem graphIdeal_isPrime {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p).IsPrime :=
  Ideal.comap_isPrime _ _

theorem graphPt_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : graphPt p x ∈ zeroSet (graphIdeal J p) := by
  intro q hq
  rw [eval_graphPt]
  exact hx _ hq

theorem init_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : Fin.init x ∈ zeroSet J := by
  intro q hq
  have h := hx (rename Fin.castSucc q) (by rw [graphIdeal, Ideal.mem_comap, graphHom_rename]; exact hq)
  rw [eval_rename] at h
  exact h

theorem graphPt_init_of_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : graphPt p (Fin.init x) = x := by
  have h := hx (X (Fin.last n) - rename Fin.castSucc p)
    (by rw [graphIdeal, Ideal.mem_comap, map_sub, graphHom_X_last, graphHom_rename, sub_self]; exact J.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  rw [graphPt]
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [h]
  rfl

theorem ringKrullDim_graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg))

theorem X_last_not_mem_graphIdeal {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : MvPolynomial (Fin n) ℂ} (hp : p ∉ J) :
    X (Fin.last n) ∉ graphIdeal J p := by
  rw [graphIdeal, Ideal.mem_comap, graphHom_X_last]
  exact hp

theorem graphIdeal_sup_span (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    graphIdeal J p ⊔ Ideal.span {X (Fin.last n)} = graphIdeal (J ⊔ Ideal.span {p}) p := by
  have hs := graphHom_surjective p
  have hmap : (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).map (graphHom p) = J ⊔ Ideal.span {p} := by
    rw [Ideal.map_sup, graphIdeal, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton,
      graphHom_X_last]
  rw [← hmap]
  show _ = Ideal.comap (graphHom p) (Ideal.map (graphHom p) _)
  rw [Ideal.comap_map_of_surjective _ hs]
  refine (sup_eq_left.mpr ?_).symm
  exact le_sup_of_le_left (Ideal.comap_mono bot_le)

theorem minimalPrimes_graphIdeal_sup (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).minimalPrimes =
      (fun W => graphIdeal W p) '' (J ⊔ Ideal.span {p}).minimalPrimes := by
  rw [graphIdeal_sup_span, graphIdeal]
  exact Ideal.comap_minimalPrimes_eq_of_surjective (graphHom_surjective p) _

theorem graphIdeal_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (fun W => graphIdeal W p) :=
  Ideal.comap_injective_of_surjective _ (graphHom_surjective p)

theorem graphIdeal_mono {J W : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) (h : J ≤ W) :
    graphIdeal J p ≤ graphIdeal W p :=
  Ideal.comap_mono h

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def ComponentsGenericCount.Statement : Prop :=
  ∀ (n d : ℕ) (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ J ∈ F, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) ∧ IsFiniteProjection J A) →
    (∀ J ∈ F, ∀ J' ∈ F, J ≤ J' → J = J') →
      (∀ y : Fin d → ℂ,
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard ≤ ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞)) ∧
      ∃ Δ : MvPolynomial (Fin d) ℂ, Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard = ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞) ∧
        ∀ x, (∃ J ∈ F, x ∈ zeroSet J) → A *ᵥ x = y →
          ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ ∃ J ∈ F, g y' ∈ zeroSet J

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def InvertibleIndexMul.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) → (∀ b ∈ B, ∀ z ∈ N, b * z ∈ N) → (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ i, g i ≠ 0) → (∀ i, h i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * g i ∈ B) → (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * h i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      ((∃ b : B, b ∉ m ∧ (b : Ω) * g i ∈ M) ∧ ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * g i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * h i ∈ N) ∧ ∀ z ∈ N, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * h i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * (g i * h i) ∈ P) ∧
        ∀ z ∈ P, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * (g i * h i))) →
      0 < genIndex M B.toAddSubgroup ∧ 0 < genIndex N B.toAddSubgroup ∧
        genIndex P B.toAddSubgroup = genIndex M B.toAddSubgroup * genIndex N B.toAddSubgroup

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def LocalGen {Ω : Type} [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (m : Ideal B) (f : Ω) : Prop :=
  (∃ b : B, b ∉ m ∧ (b : Ω) * f ∈ X) ∧ ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * f

def LocalGenFamily.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * f i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      X ≠ ⊥ ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ω), (∀ j, a j ∈ X) ∧
        (∀ j, ∃ c ∈ B, c ≠ 0 ∧ c * a j ∈ B) ∧
        ∀ m : Ideal B, m.IsMaximal → ∃ j, ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a j

def LocallyPrincipalCoprimeField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (B : Subring Ω) (M : AddSubgroup Ω) (ι : Type) [Fintype ι]
    (a : ι → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y

def InvertibleProductRep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω)
    (β δ β' δ' : B) (I J : Ideal B),
    β ≠ 0 → δ ≠ 0 → β' ≠ 0 → δ' ≠ 0 →
    (∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) →
    (∀ x : Ω, x ∈ N ↔ ∃ y ∈ J, (β' : Ω) * x = δ' * y) →
    (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      LocalGen B M m (g i) ∧ LocalGen B N m (h i) ∧ LocalGen B P m (g i * h i)) →
      ∀ x : Ω, x ∈ P ↔ ∃ y ∈ I * J, ((β * β' : B) : Ω) * x = (δ * δ' : B) * y

def InvertibleIndexCharP.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    ringChar Ω ≠ 0 → Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      genIndex X B.toAddSubgroup = 1

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField

def NumberFieldBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B : AddSubgroup F), B.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) →
    ∃ C : ℝ, ∀ L : AddSubgroup F, L.FG → (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∀ ρ : (F →+* ℂ) → ℝ, (∀ σ, 0 < ρ σ) → (∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) →
        ∑ σ : F →+* ℂ, Real.log (ρ σ) + Real.log (genIndex L B) - C ≤
          Real.log (Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ})

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

theorem LatticeImageZLattice.exists_int_mul_integral {F : Type} [Field F] [NumberField F]
    (L : AddSubgroup F) (hfg : L.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ L, IsIntegral ℤ (N • x) := by
  obtain ⟨S, hS⟩ := hfg
  have halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s) := fun s =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
  choose y hy0 hyint using halg
  refine ⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩
  have h : ∀ z : L, z ∈ AddSubsemigroup.closure (↑S : Set L) →
      IsIntegral ℤ ((∏ s ∈ S, y s) • (z : F)) := by
    intro z hz
    induction hz using AddSubsemigroup.closure_induction with
    | mem s hs =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun t : L => y t) (show s ∈ S from hs)
      rw [hc, mul_comm, mul_smul]
      exact (hyint s).zsmul c
    | add a b _ _ ha hb => simpa [smul_add] using ha.add hb
  intro x hx
  exact h ⟨x, hx⟩ (hS ▸ AddSubsemigroup.mem_top _)



open scoped Classical in
theorem LatticeImageZLattice.proof : LatticeImageZLattice.Statement := by
  intro F _ _ L hfg hfull
  obtain ⟨N, hN0, hLint⟩ := LatticeImageZLattice.exists_int_mul_integral L hfg

  let e : mixedSpace F →ₗ[ℝ] mixedSpace F := (N : ℝ) • LinearMap.id
  have he₁ : Continuous e := continuous_const_smul (N : ℝ)
  have he₂ : Function.Injective e := fun a b h =>
    smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h
  have hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e) :=
    ZLattice.comap_discreteTopology ℝ _ he₁ he₂
  have hle : (latticeImage F L : Set (mixedSpace F)) ⊆
      ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage L z).mp hz
    show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F
    refine ⟨⟨N • x, hLint x hx⟩, ?_⟩
    change mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have : DiscreteTopology (latticeImage F L) := DiscreteTopology.of_subset hdisc hle
  refine ⟨this, ⟨?_⟩⟩

  rw [eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, hn, hnL⟩ := hfull (integralBasis F i)
  have hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L :=
    (mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩
  have hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice


open scoped Classical in
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
end
