module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Group.Measure
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Mathlib.NumberTheory.NumberField.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.PeriodIntegrals.Bundle009

@[expose] public section

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ₁ Λ₂ : Submodule (𝓞 E) (Fin n → E)), Λ₁.FG → Λ₂.FG →
    (latL A Λ₁ = latL A Λ₂ ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
        ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₁) ↔ (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₂))

end PI.LocLatEq
end
end

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatSat

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (W : Submodule E (Fin n → E)), Λ.FG →
    (latL A (Λ ⊓ W.restrictScalars (𝓞 E)) : Set (Fin n → A.Ep)) =
      (latL A Λ : Set (Fin n → A.Ep)) ∩ Submodule.span A.Ep (bc A '' (W : Set (Fin n → E)))

end PI.LocLatSat
end
end

section

noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.LocHaarRR

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def ordR {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
    (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) : Subring A.Ep :=
  let S : Subring (𝒪[A.Fp] × 𝒪[A.Fp]) :=
    RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.fst _ _))
      ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.snd _ _))
  (S.map ((𝒪[A.Fp]).subtype.prodMap (𝒪[A.Fp]).subtype)).comap sg.e.toRingEquiv.toRingHom

def RR (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) : Set A.Ep :=
  match A.split with
  | none => (A.O : Set A.Ep)
  | some sg => (ordR sg : Set A.Ep)

end

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p),
    IsReduced A.Ep → ∃ μ : Measure A.Ep, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (RR A) = 1

end PI.LocHaarRR
end
end

section

namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def BallQuotLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen (A := A) e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)

end PI
end

section

namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def EfRankSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    Finite (Pts O A) ∧ (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank K A

end PI
end

section

noncomputable section

open Matrix NumberField
open scoped TensorProduct
open PI.UJClassFin

namespace PI.UJClassMass

def gramOf {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) : Matrix (Fin M) (Fin M) E :=
  fun i j => h (b i) (b j)

def crdOf {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : Set (Fin M → E) :=
  {x | ∑ i, x i • b i ∈ L0}

def stab {G : Type*} [Group G] (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}

end PI.UJClassMass
end
end
