module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Mathlib.RepresentationTheory.Semisimple
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section General

variable {O Γ : Type} [CommRing O] [IsDomain O] [Group Γ]

def fracRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) :
    Representation (FractionRing O) Γ (Fin a → FractionRing O) :=
  glRep (mapRep (algebraMap O (FractionRing O)) ρ)

def charSum (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ (Fin t → FractionRing O) where
  toFun g := LinearMap.pi fun c : Fin t =>
    algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) • LinearMap.proj c
  map_one' := by
    ext v c
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext c
    simp [mul_assoc, Algebra.smul_def]

def blockRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ ((Fin a → FractionRing O) × (Fin t → FractionRing O)) :=
  (fracRep ρ).prod (charSum χ t)

def IsoBlock {n a : ℕ} (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ))
    (t : ℕ) : Prop :=
  ∃ e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin a → FractionRing O) × (Fin t → FractionRing O)),
    ∀ g v, e (fracRep r g v) = blockRep ρ χ t g (e v)

def BlockSemisimple {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) : Prop :=
  (blockRep ρ χ t).IsSemisimpleRepresentation


omit [IsDomain O] in
def LatticeContinuous [TopologicalSpace Γ] [TopologicalSpace O] {a : ℕ}
    (ρ : Γ →* GL (Fin a) O) : Prop :=
  Continuous fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)

theorem blockRep_apply {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : (Fin a → FractionRing O) × (Fin t → FractionRing O)) :
    blockRep ρ χ t g v =
      ((((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map
          (algebraMap O (FractionRing O))).mulVec v.1,
        fun c : Fin t => algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) * v.2 c) := by
  rfl

end General

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

structure IsComplement (r₀ : G H.E N.Om →* GL (Fin R.nV) (N.O i))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop where

  rho : IsoBlock r₀ ρ (N.chi i) R.t

  ss : BlockSemisimple ρ (N.chi i) R.t

  cont : LatticeContinuous ρ

end Record

def Complement_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i,
    ∀ r₀ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i), IsHeckeGalois D.nd i π r₀ →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsComplement D.nd i r₀ ρ

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

end
end
