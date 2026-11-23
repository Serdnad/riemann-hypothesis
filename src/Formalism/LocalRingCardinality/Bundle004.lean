module

public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

noncomputable section

namespace Formalism.BasicNotions

open NumberField

def DV.Used (D : D7) (μ : D.what₂.Tup) : Prop :=
  μ = D.what₂.mu0 ∨ μ = D.what₂.muStar ∨ μ = D.what₂.muStar' ∨ ∃ w, μ = D.what₂.muAt w

structure AmbForm (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  MtH : D.what₂.Tup → HLat D.what₂.LL

  jAmb : ∀ μ, (MtH μ).V →ₛₗ[D.what₂.embLL] S.Amb μ
  MtH_good : ∀ μ, DV.Used D μ → (MtH μ).Good
  jAmb_basis : ∀ μ, DV.Used D μ → LinearIndependent ℂ (fun i => jAmb μ ((MtH μ).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jAmb μ ((MtH μ).b i))) = ⊤

  jAmb_lat : ∀ μ, DV.Used D μ → ∀ x, x ∈ (MtH μ).L ↔ ∃ c : S.Amb μ → 𝓞 D.what₂.LL,
    jAmb μ x = ∑ v ∈ (S.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  jAmb_gen : ∀ μ, DV.Used D μ → ∀ v ∈ (S.Mtilde μ).gen, v ∈ Set.range (jAmb μ)

  jAmb_norm : ∀ μ, DV.Used D μ → ∀ x,
    Formalism.HermitianLatticesTheory.normAt (MtH μ).b (MtH μ).X (InfinitePlace.mk D.what₂.embLL) x = ‖jAmb μ x‖

end Formalism.BasicNotions

end
end

section

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal



structure NChTie (D : D7) (c : NChoice D) : Prop where

  twOf_eq : ∀ a : D.nd.Loc, D.ntw.twOf a = c.twI (D.nd.w a)

  twSide_eq : ∀ a : D.nd.Loc, D.ntw.twSide a = c.sd (D.nd.w a)

  Q_eq : ∀ a : D.nd.Loc, D.nd.Q a = c.Q (D.nd.w a)

  psi_eq : ∃ ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ),
    (∀ w, ψ0 (D.what₂.places.conj w) = ψ0 w) ∧
    (∀ w g, c.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        ((c.psi' w (D.ntw.art (c.twI w) (c.Q w) g) : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w)))) ∧
    (∀ (a : D.nd.Loc) g, D.nd.embK a ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL) =
      algebraMap (D.nd.O a) (FractionRing (D.nd.O a)) ((D.ntw.psiL a g : (D.nd.O a)ˣ) : D.nd.O a))

  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : D.ntw.O0 (c.twI w)), z ≠ 0 →
    (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x *
        algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y →
    c.embW w (x : D.what₂.LL) *
        algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
          (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z))) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))

structure ThData (D : D7) where
  xd0 : ∀ i j b, Set (D.nexp.Dat i j b)
  thetaBase_invariant_action : ∀ i j b, ∀ a ∈ xd0 i j b, ∀ u : D.nexp.U, D.nexp.actG i j b u (D.nexp.th i j b a) =
    ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • D.nexp.th i j b a

end Formalism.BasicNotions

end
end

section

open MeasureTheory Matrix Formalism.MainNotions.S

noncomputable section

namespace Formalism.BasicNotions

def cdScaleTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A =
        D.cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

def dsigTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ →
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d → d = D.dsig τ

def TwCoverPair (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥D.LL0),
    ((p : ℕ) : NumberField.RingOfIntegers ↥D.LL0) ∈ w.asIdeal →
    (∃ w' : D.what₂.places.Pl, D.what₂.muAt w' ≠ D.what₂.mu0 ∧
      ∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ 0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)) →
    ∃ i, D.ntw.l i = p ∧
      ((∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ∨
       (∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0b i (x : ↥D.LL0)))

structure Ties (D : D7) : Prop where
  cdScale_tie : cdScaleTie D
  dsig_tie : dsigTie D

  bu_def : Rows.BuDefQ D.what₂

  tw_cover : TwCoverPair D

  baseField_isGalois : IsGalois ℚ ↥D.LL0

  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π

def GoodFTAll (D : Formalism.BasicNotions.D7) : Prop := ∀ σ, D.nd.goodRow σ

end Formalism.BasicNotions

end
end

section

noncomputable section

namespace Formalism.BasicNotions.SizeData₂

def hsSq {D : Formalism.BasicNotions.D7} (_L : Formalism.BasicNotions.SizeData₂ D) (u u' : D.what₂.Word) : ℝ := Formalism.MainNotions.S.hsSqD D u u'

end Formalism.BasicNotions.SizeData₂

end
end
