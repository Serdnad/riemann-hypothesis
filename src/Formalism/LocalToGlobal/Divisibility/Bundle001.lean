module

public import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.QuotientMetricDivisors.Bundle005
public import Formalism.QuotientMetricDivisors.Bundle004
public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.Analysis.Matrix.Order
public import Formalism.QuotientMetricDivisors.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

theorem exists_sqrt (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩

theorem sqrts_sub (m : ℤ) : sqrts m ⊆ (sqQ m : Set Qb) := subset_adjoin ℚ _

theorem isAlgebraicQb (LL : Fld) : Algebra.IsAlgebraic LL Qb := by
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) LL

theorem exists_ext (ι : Qb →+* ℂ) (LL : Fld) (σ : CoF ι LL →+* ℂ) :
    ∃ τ : Qb →+* ℂ, ∀ x : CoF ι LL, τ (CoF.val ι LL x) = σ x := by
  have := isAlgebraicQb LL
  let f : LL →ₐ[ℚ] ℂ := RingHom.toRatAlgHom (R := LL) σ
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f
  refine ⟨φ.toRingHom, fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

theorem exists_aut (ι τ : Qb →+* ℂ) : ∃ σ : Qb ≃ₐ[ℚ] Qb, ∀ x, τ x = ι (σ x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (algC τ).trans (algC ι).symm) (fun r => by simp), fun x => ?_⟩
  have h : ((algC ι ((algC ι).symm (algC τ x)) : algebraicClosure ℚ ℂ) : ℂ) = τ x := by
    rw [RingEquiv.apply_symm_apply]; rfl
  exact h.symm

theorem finite_pow_eq {n : ℕ} (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by
  classical
  refine (Polynomial.nthRoots n a).toFinset.finite_toSet.subset fun z hz => ?_
  simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegralQb (x : Qb) : IsIntegral ℚ x := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral

theorem fin_adjoin {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by
  have : Finite S := hS
  exact finiteDimensional_adjoin fun x _ => isIntegralQb x

end Formalism.L2.DIV
end
end

section

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

namespace Formalism.L2.DIV

section Proved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem mem_tupGrp {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills, CommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

end Proved

section ProvedK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

end ProvedK

theorem Tup.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    {S : Set ℕ} (ξ : Tup F E L S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime (ξ : Chr F E L)) : GoodPl E S v := by
  by_contra hg
  exact hv (((mem_tupGrp (ξ : Chr F E L)).mp ξ.2).2.2.2 v hg)

def IsConjOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  σ ≠ AlgHom.id F E ∧ (∀ e, σ (σ e) = e) ∧ ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e

def DetInUnitaryOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsUnit J.det →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), Matrix.GeneralLinearGroup.det g ∈ U1 σ

def QprimeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), ξ ∈ openChr F E L → (Qprime ξ).Finite

def ResCharEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), ∃! χ, IsResChar ξ P χ

end Formalism.L2.DIV

end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

section OnePlace

variable {n d : ℕ}

def metOf (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Y⁻¹)ᴴ * Y⁻¹

def frameOf (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (CFC.sqrt A)⁻¹

def quotMetC (P : Matrix (Fin d) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (P * A⁻¹ * Pᴴ)⁻¹

def restrMetC (C : Matrix (Fin n) (Fin d) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Cᴴ * A * C

end OnePlace

section AllPlaces

variable {K : Type} [Field K] [NumberField K] {n d D : ℕ}

def stdFrame (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (H.map v.embedding)

def quotFrame (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin D) (Fin D) ℂ :=
  fun v => frameOf (quotMetC (P.map v.embedding) (H.map v.embedding))

def restrFrame (E : Matrix (Fin n) (Fin d) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => frameOf (restrMetC (E.map v.embedding) (H.map v.embedding))

def weightMet {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, ((t p v : ℝ) : ℂ) • restrMetC ((pr p).map v.embedding) (metOf (X v))

def weightFrame {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (weightMet pr t X v)

def pushFrame (φ : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => φ.map v.embedding * X v


open Classical in
def spliceFrame (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  Function.update X v0 Y

def rowFrame {Ix : Type} [Fintype Ix] (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) K) (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  spliceFrame v0 Y (pushFrame φ (weightFrame pr t X))

def toHLat [StarRing K] (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : Formalism.BasicNotions.HLat K where
  V := Fin d → K
  ι := Fin d
  b := Pi.basisFun K (Fin d)
  X := X
  L := L

end AllPlaces

def FrameOfSpec : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    IsUnit (frameOf A).det ∧ metOf (frameOf A) = A

def MetOfSpec : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), IsUnit Y.det →
    (metOf Y).PosDef ∧ (metOf Y)⁻¹ = Y * Yᴴ ∧ metOf (frameOf (metOf Y)) = metOf Y

def QuotRestrPosDef : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    (∀ P : Matrix (Fin d) (Fin n) ℂ, Function.Surjective P.mulVec → (quotMetC P A).PosDef) ∧
    (∀ C : Matrix (Fin n) (Fin d) ℂ, Function.Injective C.mulVec → (restrMetC C A).PosDef)

def QuotEqRestrC : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    ∀ (C : Matrix (Fin n) (Fin d) ℂ) (P : Matrix (Fin d) (Fin n) ℂ), P * C = 1 →
      Cᴴ * A * (1 - C * P) = 0 → quotMetC P A = restrMetC C A

def StdFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v0 : InfinitePlace K) (n : ℕ)
    (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) → IsHermAt v0 H (stdFrame H)

def QuotFrameIsQuot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (quotFrame P H)

def RestrFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
    ∀ v : InfinitePlace K, IsUnit (restrFrame E H v).det ∧
      metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) ∧
      ∀ x y : Fin d → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) (restrFrame E H) v x y =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (stdFrame H) v (E.mulVec x) (E.mulVec y)

def RestrFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      IsHermAt v0 (Eᴴ * H * E) (restrFrame E H)

def RestrFrameRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    (∀ a ∈ K0, star a ∈ K0) →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec → (∀ i a, E i a ∈ K0) →
      IsRatHerm K0 (Eᴴ * H * E) (restrFrame E H) ∧ restrFrame E H = stdFrame (Eᴴ * H * E)

def QuotEqRestrAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      quotFrame Pr H v0 = restrFrame E H v0

def QuotEqRestrRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), (∀ i a, E i a ∈ K0) →
      IsOrthProj H E Pr → quotFrame Pr H = restrFrame E H

def QuotFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      IsHermAt v0 (Eᴴ * H * E) (quotFrame Pr H)

def WeightFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 →
    ∀ v : InfinitePlace K, IsUnit (weightFrame pr t X v).det ∧
      metOf (weightFrame pr t X v) = weightMet pr t X v ∧
      ∀ x y : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ∑ p, ((t p v : ℝ) : ℂ) *
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr p).mulVec y)

def WeightFramePart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 → (∀ p q, p ≠ q → pr p * pr q = 0) →
    ∀ v : InfinitePlace K,
    (∀ p q, p ≠ q → ∀ x y : Fin n → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr q).mulVec y) = 0) →
    ∀ (p : Ix) (x y : Fin n → K), (pr p).mulVec x = x →
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ((t p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y

def SpliceFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v0 : InfinitePlace K)
    (Y : Matrix (Fin n) (Fin n) ℂ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    spliceFrame v0 Y X v0 = Y ∧ ∀ v, v ≠ v0 → spliceFrame v0 Y X v = X v

end Formalism.L2.DIV
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

structure CSD (K : Type) [Field K] [NumberField K] [StarRing K] where

  Cl : Type
  [finCl : Fintype Cl]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]

  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  Gam : Cl → Type
  [grpGam : ∀ c, Group (Gam c)]
  [finGam : ∀ c, Fintype (Gam c)]

  ρ : ∀ c, Gam c →* Module.End K V

  Nab : Cl → Submodule (𝓞 K) V

  Del : Cl → Submodule (𝓞 K) V

attribute [instance] CSD.finCl CSD.addV CSD.modV CSD.modOV CSD.towV CSD.finιV CSD.decιV CSD.grpGam
  CSD.finGam

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

instance : FiniteDimensional K S.V := Module.Finite.of_basis S.bV

def Forms : Submodule K (S.Cl → S.V) where
  carrier := {f | ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c}
  add_mem' := by
    intro f g hf hg c γ
    simp only [Pi.add_apply, map_add (f := _), hf c γ, hg c γ]
  zero_mem' := by
    intro c γ
    simp
  smul_mem' := by
    intro a f hf c γ
    simp only [Pi.smul_apply, map_smul, hf c γ]

def dim : ℕ := finrank K S.Forms

def IsRat (f : S.Cl → S.V) : Prop := ∀ c i, S.bV.repr (f c) i ∈ cmMax K

def HasRatBasis : Prop := ∃ b : Basis (Fin S.dim) K S.Forms, ∀ i, S.IsRat (b i : S.Cl → S.V)


open Classical in
def basis : Basis (Fin S.dim) K S.Forms :=
  if h : S.HasRatBasis then h.choose else finBasis K S.Forms

def I : (Fin S.dim → K) →ₗ[K] (S.Cl → S.V) :=
  S.Forms.subtype ∘ₗ (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms)

def wt (c : S.Cl) : ℕ := Fintype.card (S.Gam c)

def DGam : ℕ := Finset.univ.lcm S.wt

def csum (f g : S.Cl → S.V) : K := ∑ c, ((S.wt c : K))⁻¹ * S.pair (f c) (g c)

def H : Matrix (Fin S.dim) (Fin S.dim) K :=
  Matrix.of fun i j => S.csum (S.basis i : S.Cl → S.V) (S.basis j : S.Cl → S.V)

def nabLat : Submodule (𝓞 K) (Fin S.dim → K) := valLatF S.I S.Nab

def delLat : Submodule (𝓞 K) (Fin S.dim → K) := valLatF S.I S.Del

def gramV : Matrix S.ιV S.ιV K := Matrix.of fun i j => S.pair (S.bV i) (S.bV j)

structure Good (s : ℕ) : Prop where
  symm : S.pair.IsSymm
  nondeg : S.pair.Nondegenerate
  inv : ∀ c (γ : S.Gam c) x y, S.pair (S.ρ c γ x) (S.ρ c γ y) = S.pair x y
  nab_lat : ∀ c, Submodule.IsLattice K (S.Nab c)
  del_le : ∀ c, S.Del c ≤ S.Nab c
  del_stable : ∀ c (γ : S.Gam c), ∀ y ∈ S.Del c, S.ρ c γ y ∈ S.Del c
  s_pos : 0 < s
  dual_le : ∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c), (s : 𝓞 K) • y ∈ S.Del c
  del_dual : ∀ c, ∀ y ∈ S.Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c)

structure Rat : Prop where
  pair_rat : ∀ i j, S.gramV i j ∈ cmMax K
  act_rat : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef

end CSD

end Formalism.L2.DIV
end
end
