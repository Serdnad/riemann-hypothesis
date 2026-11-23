module

public import Formalism.HarderNarasimhan.Bundle002
public import Formalism.QuotientMetricDivisors.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K]

def scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v

end Defs

def KappaInvariance : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ t : InfinitePlace K → ℝ, (∀ v, 0 < t v) →

      (∀ v, IsUnit (scaleFrame t XE v).det ∧
        ((scaleFrame t XE v)⁻¹).conjTranspose * (scaleFrame t XE v)⁻¹ =
          (t v : ℂ) • (((XE v)⁻¹).conjTranspose * (XE v)⁻¹)) ∧

      (∀ (d : ℕ) (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (φ : Matrix (Fin D) (Fin d) K)
        (v : InfinitePlace K),
        detRatio XS (scaleFrame t XE) φ v = t v ^ d * detRatio XS XE φ v) ∧
      (∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
        meanLog (fun v => t v * κ v) = meanLog t + meanLog κ) ∧

      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
        lcv (scaleFrame t XE) R = lcv XE R + (D : ℝ) * meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                  (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
            meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE R - meanLog t ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R - meanLog t) ∧

      (∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
        ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                  (Formalism.HN.dualFrame (scaleFrame t XE)) φ =
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame XE) φ - meanLog t)

def KappaNormalise : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
      (∀ v, IsUnit (scaleFrame (fun v => (κ v)⁻¹) XE v).det) ∧

      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (ρ P : ℝ), detRatio XS XE φ v = (κ v * ρ) ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 * ρ) ^ D * P) ∧
      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (P : ℝ), detRatio XS XE φ v = κ v ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 : ℝ) ^ D * P) ∧
      meanLog (fun _ : InfinitePlace K => (1 : ℝ)) = 0 ∧
      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) + meanLog κ ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R - meanLog κ ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                  Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
            Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R ∧
        ∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
          ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ - meanLog κ ∧
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                    Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
              Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ)

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  A.comap ((Matrix.mulVecLin E).restrictScalars (𝓞 K))

def IsOrthProj {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) : Prop :=
  Pr * E = 1 ∧ Eᴴ * H * (1 - E * Pr) = 0

def IsClassSum {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    (H : Matrix (Fin n) (Fin n) K) (I : (Fin n → K) →ₗ[K] (Cl → V))
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (g : Cl → ℕ) : Prop :=
  ∀ x y, hform H x y = ∑ c, ((g c : K))⁻¹ * pair (I x c) (I y c)

end Defs

def OrthProjExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      Hᴴ = H ∧ IsUnit H.det ∧ IsUnit (Eᴴ * H * E).det ∧
        IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) ∧
        ∀ Pr, IsOrthProj H E Pr → Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H)

def ProjDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A) = cutLat E (Formalism.HermitianLatticesTheory.dual (hform H) A)

def CutDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (cutLat E A) = matLat Pr (Formalism.HermitianLatticesTheory.dual (hform H) A)

def ExpIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ x ∈ A, a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
      idx w A B ≤ (D : ℤ) * vw w (a : K)

def ProjIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G0 : Type) [Fintype G0]
    (r : G0 → Matrix (Fin n) (Fin n) K) (c : G0 → K) (G : ℕ),
    (∀ s, ∃ a : 𝓞 K, (a : K) = (G : K) * c s) →
    ∀ B : Submodule (𝓞 K) (Fin n → K), (∀ s, ∀ x ∈ B, (r s).mulVec x ∈ B) →
    ∀ x ∈ B, (G : 𝓞 K) • (∑ s, c s • r s).mulVec x ∈ B

def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsFullLattice K A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
      Submodule.IsFullLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A), ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E A

def BoundsIVGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ z ∈ cutLat E A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsFullLattice K (matLat Pr A) ∧ Submodule.IsFullLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * (vw w (a : K) + vw w (DG : K))

def BoundsIV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsFullLattice K (matLat Pr A) ∧ Submodule.IsFullLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K))

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)

def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def DivIntoDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ) (R : Submodule (𝓞 K) (Fin D → K))
    (B : (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (F : Fin (n w) → K), P w F = ζ w * B ((ι w).mulVec ((π w).mulVec F))) →
    (∀ w, ∀ F ∈ M w, P w F = 0 ∨ 0 ≤ vw w (P w F)) →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ x ∈ R, B x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def smulLat {d : ℕ} (a : K) (N : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) :=
  N.map ((LinearMap.lsmul K (Fin d → K) a).restrictScalars (𝓞 K))

def IsShiftAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ) :
    Prop :=
  ∃ a : K, a ≠ 0 ∧ vw w a = -s ∧
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N)

def IsShift {d : ℕ} (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℤ) : Prop :=
  ∀ w, IsShiftAt w N N' (σ w)

def shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-σ w)

end Defs

def ShiftIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N N' : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (s : ℤ), IsShiftAt w N N' s →
      idx w N N' = -((d : ℤ) * s)

def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N →
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N = -(lcv X N) / d

def ShiftMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N → Submodule.IsFullLattice K N' →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, IsShift N N' σ →
      lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) ∧
      (0 < d → (Function.support σ).Finite ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' =
          Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
            2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ))

def ShiftEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, (Function.support σ).Finite →
      IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ ∧
      Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) ∧
      ∀ N' : Submodule (𝓞 K) (Fin d → K), IsShift N N' σ →
        N' = Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N

def ShiftPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ), IsShiftAt w N N' s →
    ∀ f : (Fin d → K) →ₗ[K] K, (∀ φ ∈ N, f φ = 0 ∨ s ≤ vw w (f φ)) →
      ∀ φ ∈ N', f φ = 0 ∨ 0 ≤ vw w (f φ)

def DivIntoDualShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d D : ℕ)
    (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin d → K) →ₗ[K] (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin d → K) →ₗ[K] (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (φ : Fin d → K) (F : Fin (n w) → K),
      P w φ F = ζ w * B φ ((ι w).mulVec ((π w).mulVec F))) →
    ∀ (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
      (τ : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w, ∀ φ ∈ N, ∀ F ∈ M w, P w φ F = 0 ∨ σ w ≤ (vw w (P w φ F) : ℝ)) →
    (∀ w, τ w ≤ ⌈σ w⌉) → IsShift N N' τ →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ φ ∈ N', ∀ x ∈ R, B φ x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)).Finite ∧
    (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ =
      ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w a : ℝ)

def DetCS : Prop :=
  ∀ (n D : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ), Hc.PosDef →
    ∀ A B : Matrix (Fin D) (Fin n) ℂ,
      ‖(A * Hc * Bᴴ).det‖ ^ 2 ≤ (A * Hc * Aᴴ).det.re * (B * Hc * Bᴴ).det.re

def LcvBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)).Finite ∧
      lcv X L = (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (gram X v e).det.re +
        2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)

def IdxChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (γ : Matrix (Fin d) (Fin d) K),
      IsLocBasis L w (fun i => ∑ k, γ k i • e k) →
      idx w (Submodule.span (𝓞 K) (Set.range e)) L = vw w γ.det ∧
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range e)) L = vw (conjPl w) γ.det

def ValBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b) ∧
    (∀ a : K, vw w (star a) = vw (conjPl w) a) ∧
    lw (conjPl w) = lw w ∧ conjPl (conjPl w) = w ∧ vw w 1 = 0 ∧
    (∀ a : K, vw w a⁻¹ = - vw w a) ∧
    (∀ a : 𝓞 K, 0 ≤ vw w (a : K))

def GramChange : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (D m : ℕ) (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) (γ : Matrix (Fin m) (Fin m) K),
      gramR Γ (fun i => ∑ k, γ k i • e k) = star γ.det * γ.det * gramR Γ e

def ImageLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (XS v).det) →
    (∀ v, IsUnit (XT v).det) →
    ∀ φ : Matrix (Fin d) (Fin d) K, IsUnit φ.det →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
      lcv XT (matLat φ L) = lcv XS L + (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio XS XT φ v)

def IdxLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A B : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite ∧
      lcv X B = lcv X A + 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w A B : ℝ)

def RatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K T →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw H w T : ℝ)).Finite ∧
      lcv X T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw H w T : ℝ)

def JwGram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)

def FinsumConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (f : HeightOneSpectrum (𝓞 K) → ℝ),
    ∑ᶠ w, f (conjPl w) = ∑ᶠ w, f w

def LocBasisEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (L : Submodule (𝓞 K) (Fin d → K)),
    Submodule.IsFullLattice K L → ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f

end Formalism.DivisionValues
end
end
