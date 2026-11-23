module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u

section Statements

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (Ω : Type*) [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def Ba.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E' E'' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E'' k L Q = ck O x d N E E' k L Q + ck O x d N E' E'' k L Q ∧
        ck O x d N E' E k L Q = -ck O x d N E E' k L Q

def Bb.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ N₂ : ℕ) (V V₁ V₂ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsSubQuot O x E i p E₁ E₂ →
    IsSubQuot O x E' i p E₁' E₂' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def Bd.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (g : O), g ≠ 0 →
    IsModelOver O (mcIdeal O x) d →
    (∀ s, mseg x s ≠ 0 → ∀ v, v ∈ E'.lat s ↔ ∃ e ∈ E.lat s, v = algebraMap O Ω g • e) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g ∧
        ∀ (m n : ℕ) (h w : O), IsUnit w → 1 ≤ m → g ^ m = w * h ^ n →
          (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g =
            (n : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q h

end Statements

section FieldStatements

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric → ∀ (c n : ℕ) (Y : Fin n → K → ℤ),
      G.IsHomogeneous c → c + n = e →
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j))

end FieldStatements

section Inhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem sameGeneric_symm {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') : SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type}

def midSwapBlocks : K ⊕ (K₂ ⊕ K') ≃ K ⊕ (K' ⊕ K₂) :=
  Equiv.sumCongr (Equiv.refl K) (Equiv.sumComm K₂ K')

def midSwapVars (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  left_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl
  right_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl

theorem midSwapVars_fst {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
    (v : Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    (midSwapVars ι ι' ι₂ v).1 = midSwapBlocks v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem joinCoord_comp_midSwapVars {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type} {Ω : Type*}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) :
    joinCoord x (joinCoord z w) ∘ midSwapVars ι ι' ι₂ = joinCoord x (joinCoord w z) := by
  funext v
  obtain ⟨k | k | k, i⟩ := v <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField pairNum midSwapBlocks midSwapVars
  ptCoord ptIdx unif)

def PairNumberRelabelAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ (y : (Σ k, ι₂ k) → Ω) (d : ℕ),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (y ∘ σ)) d →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ∧ fnField O y = fnField O (y ∘ σ) ∧
        (∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g →
            IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g)) ∧
        ∀ (I₁ : IFamily (IsLocalRing.ResidueField O) ι₁) (I : IFamily (IsLocalRing.ResidueField O) ι₂),
          IsFieldIntersection I₁ → IsFieldIntersection I →
        ∀ (n : ℕ) (a a' : Fin n → K₂ → ℤ) (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          (∀ i, IsVertDiv O (mcIdeal O (y ∘ σ)) (a i ∘ e - a' i ∘ e) (f i) (g i)) →
        ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (y ∘ σ)) d (fun i => a i ∘ e) (fun i => a' i ∘ e) f g H =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O y) d a a' (fun i => rename σ (f i)) (fun i => rename σ (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (IsModelOver mcIdeal joinCoord fnField mseg SameGeneric FlagModel FlagPair IsPull IsVertDiv pairNum pullDeg liftVar)

def FlagModelJoinLeftAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F : FlagModel O x d N E E') (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (w : (Σ k, ι₂ k) → Ω),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord F.z w))) d →
      fnField O (joinCoord x (joinCoord F.z w)) = fnField O x →
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord F.z w))) N V,
      IsPull O x (joinCoord F.z w) E EB → IsPull O x (joinCoord F.z w) E' E'B →
    ∃ φ : FlagPair O (joinCoord x (joinCoord F.z w)) EB E'B,
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim F.ι' ι₂)))
        (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ)
        (f g : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
        (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F.value O I₁ G y y' f g Q =
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord F.z w))) d
            (Fin.append φ.deg fun l => pullDeg (K' := F.K' ⊕ K₂) (y l))
            (Fin.append φ.deg' fun l => pullDeg (K' := F.K' ⊕ K₂) (y' l))
            (Fin.append φ.f fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (f l))
            (Fin.append φ.g fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (g l))
            (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

namespace FlagModelJoinLeftAlt

end FlagModelJoinLeftAlt

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (IsModelOver mcIdeal joinCoord fnField mseg SameGeneric FlagModel FlagPair IsPull IsVertDiv pairNum pullDeg liftVar)

def FlagModelJoinRightAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F : FlagModel O x d N E E') (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (w : (Σ k, ι₂ k) → Ω),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord w F.z))) d →
      fnField O (joinCoord x (joinCoord w F.z)) = fnField O x →
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord w F.z))) N V,
      IsPull O x (joinCoord w F.z) E EB → IsPull O x (joinCoord w F.z) E' E'B →
    ∃ φ : FlagPair O (joinCoord x (joinCoord w F.z)) EB E'B,
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ F.ι')))
        (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ)
        (f g : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
        (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F.value O I₁ G y y' f g Q =
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord w F.z))) d
            (Fin.append φ.deg fun l => pullDeg (K' := K₂ ⊕ F.K') (y l))
            (Fin.append φ.deg' fun l => pullDeg (K' := K₂ ⊕ F.K') (y' l))
            (Fin.append φ.f fun l => rename (liftVar (Sum.elim ι₂ F.ι')) (f l))
            (Fin.append φ.g fun l => rename (liftVar (Sum.elim ι₂ F.ι')) (g l))
            (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

namespace FlagModelJoinRightAlt

end FlagModelJoinRightAlt

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagPlainValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (L : Fin r → K → ℤ) (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 →
      G.IsHomogeneous c → Q.IsHomogeneous (d + 1 - c) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ₁.deg L) (Fin.append φ₁.deg' L) (Fin.append φ₁.f fun _ => 1)
                                (Fin.append φ₁.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
          (Fin.append φ₂.deg L) (Fin.append φ₂.deg' L) (Fin.append φ₂.f fun _ => 1)
          (Fin.append φ₂.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField)

def JoinTwoModels.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d →
    ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (z₁ : (Σ k, ι₁ k) → Ω)
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (z₂ : (Σ k, ι₂ k) → Ω),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z₁)) d → fnField O (joinCoord x z₁) = fnField O x →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z₂)) d → fnField O (joinCoord x z₂) = fnField O x →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord z₁ z₂))) d ∧
        fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal fnField)

def ConeTrdegFnField.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Ω : Type) [Field Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
      (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) =
        Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω)) + Fintype.card K

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord pullDeg liftVar ptCoord)

def JoinVerticalDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsVertDiv O (mcIdeal O x) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x z)) (pullDeg (K' := K') b) (rename (liftVar ι') f)
      (rename (liftVar ι') g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

def ChernClassOnFlagPair.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), Nonempty K →
      IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ,
      IsPairExpansion k (psum (Fin N) ℤ k) Gs →
      ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck O y d N B B' k L Q =
          ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O y) x x' f g Gs (classList L μ)) ∧
    (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d →
      ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
      ∀ a : O, a ≠ 0 →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum O y d N B G L Q a =
          ∑ μ ∈ Q.support, Q.coeff μ *
            cycEval (fun W => classNum x G (classList L μ) W) (divCycle (pointIdeal O y) (C a)))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def RootPolynomialNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x : Fin N → K → ℤ) (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous c → c ≤ d →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
    ∀ a : O,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) W d (Fin.append x L)
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) =
      ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum x G (classList L μ) W) (divCycle P (C a))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def plainPolynomialPairNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O) (m : ℕ) (G : MvPolynomial (Fin N) ℤ),
    G.IsHomogeneous m → m ≤ d + 1 →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - m) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) P d
                                (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * pairNum P x x' f g
          (fun i => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) (classList L μ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def VerticalDivisorCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (ϖ : O)
    (b : K → ℤ) (f g : MRing ι O), Irreducible ϖ → IsMultiProjPrime P →
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g ↔ IsVerticalDivisor P ϖ b f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
