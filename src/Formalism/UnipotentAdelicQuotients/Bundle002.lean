module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain

namespace HeckeValGen

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom


open Classical in
def finiteSingle (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L := by
  classical
  exact
    { toFun x := RestrictedProduct.mulSingle
        (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v x
      map_one' := RestrictedProduct.mulSingle_one _ _
      map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y }

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing L), finiteSingle L v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle L v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle L v) x y) }

end HeckeValGen
end
end

section

open NumberField

noncomputable section

namespace Formalism.D

def adeleOfParts (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F)
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x, y)

def siegelSetsSL2Adelic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ (Ω K : Set (Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (t₀ : ℝ),
      IsCompact Ω ∧ (∀ p ∈ Ω, (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0) ∧ IsCompact K ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F),
        ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))).range,
        ∃ p ∈ Ω, ∃ t : ℝ, t₀ ≤ t ∧
        ∃ a a' : InfiniteAdeleRing F,
          (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
          ∃ k ∈ K, ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
            (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) *
              !![adeleOfParts F a 1, 0; 0, adeleOfParts F a' 1] *
              (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))

end Formalism.D

end
end

section

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace JetMomFound

section FG

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![mulN F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries

def IsIsoGm (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ IsUnit (coeff 1 f) ∧
    PowerSeries.subst F.toPowerSeries f =
      (FormalGroup.𝔾ₘ : FormalGroup R).toPowerSeries.subst
        ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]

end FG

section Padic

variable {p : ℕ} [Fact p.Prime]

def CoeffFinite (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ∃ L : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] L ∧
    ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[p]) : ℂ_[p]) ∈ L

def HtOne (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ‖((coeff p (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 ∧ ∀ k < p, ‖((coeff k (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1

end Padic

def HtOneIsGm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]), CoeffFinite F → HtOne F → ∃ f : PowerSeries 𝓞_ℂ_[p], IsIsoGm F f

end JetMomFound
end
end

section

namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def zeroLocusGL {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (R : Type) [CommRing R] [Algebra F R] : Set (GL (Fin n) R) :=
  {g | ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2) P = 0}

def IsGroupLocus {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    1 ∈ zeroLocusGL S R ∧ (∀ g ∈ zeroLocusGL S R, ∀ h ∈ zeroLocusGL S R, g * h ∈ zeroLocusGL S R) ∧
      (∀ g ∈ zeroLocusGL S R, g⁻¹ ∈ zeroLocusGL S R)

def locusSubgroup {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (R : Type) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := zeroLocusGL S R
  one_mem' := (hS R).1
  mul_mem' := fun {a b} ha hb => (hS R).2.1 a ha b hb
  inv_mem' := fun {a} ha => (hS R).2.2 a ha

def ClassNumberFinite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (U : Subgroup (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))),
    IsOpen (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    IsCompact (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    ∃ T : Finset (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ U,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
            Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ *
              (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) * ((u : locusSubgroup S hS _) : GL (Fin n) _)

end HeckeCharacterZeroLocus
end
