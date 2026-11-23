module

public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HarderNarasimhan.Bundle002
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
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def IsHermAt {K : Type} [Field K] [NumberField K] (v0 : InfinitePlace K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ v : InfinitePlace K, IsUnit (X v).det) ∧
    ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ = H.map v0.embedding

def cmMax (K : Type) [Field K] [StarRing K] : Subfield K where
  carrier := {a | ∀ σ : K →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)}
  mul_mem' := by
    intro a b ha hb σ
    rw [star_mul', map_mul, map_mul, map_mul, ha σ, hb σ]
  one_mem' := by intro σ; simp
  add_mem' := by
    intro a b ha hb σ
    rw [star_add, map_add (f := _), map_add (f := _), map_add (f := _), ha σ, hb σ]
  zero_mem' := by intro σ; simp
  neg_mem' := by
    intro a ha σ
    rw [star_neg, map_neg, map_neg, map_neg, ha σ]
  inv_mem' := by
    intro a ha σ
    rw [star_inv₀, map_inv₀, map_inv₀, map_inv₀, ha σ]

def twist {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) : K →+* ℂ :=
  (starRingEnd ℂ).comp (σ.comp (starRingEnd K))

def embSpan {K : Type} [Field K] {n : ℕ} (σ : K →+* ℂ) (Z : Submodule K (Fin n → K)) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun z i => σ (z i)) '' (Z : Set (Fin n → K)))

def JwGramW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (H : Matrix (Fin d) (Fin d) K),
    (∀ i j, H j i = star (H i j)) → H.det ≠ 0 →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)

def StepBW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsFullLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsFullLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsFullLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    (lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))

def StepBRW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsFullLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsFullLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsFullLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))

def BoundsChainW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsFullLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsFullLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsFullLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsFullLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∉ S, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) = 0) →
    ∀ (LG E3 : ℝ) (L E1 E2 : J → ℝ) (ell g : HeightOneSpectrum (𝓞 K) → ℝ)
      (F err Jx η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    0 < D →
    (∀ w ∈ S, (vw w (G (μ w) w) : ℝ) ≤ (D : ℝ) * g w) → ∑ w ∈ S, lw w * g w ≤ LG →
    (∀ j, lcv (XW j) (M j) / D ≤ L j) →
    (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, (jw (HT j (μ w)) w (T j (μ w)) : ℝ) ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, lw w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, lw w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, lw w * (2 / ell w ^ 2) ≤ E3 →
      lcv XE R / D ≤ meanLog κ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, lw w * F w j + LG +
        ∑ j, (E1 j + E2 j) + E3

def DescentCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Z : Submodule K (Fin n → K)),
    (∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z) →
    ∃ (d : ℕ) (z : Fin d → Fin n → K), LinearIndependent K z ∧
      Submodule.span K (Set.range z) = Z ∧ ∀ a i, z a i ∈ cmMax K

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def StepA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (n D : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (π : Matrix (Fin D) (Fin n) K)
    (ι : Matrix (Fin D) (Fin D) K)
    (B : (Fin D → K) →ₗ[K] K) (P : (Fin n → K) →ₗ[K] K) (ζ : K) (σ : ℤ),
    ζ ≠ 0 → vw w ζ = 0 →
    (∀ F : Fin n → K, P F = ζ * B (ι.mulVec (π.mulVec F))) →
    (∀ F ∈ M, P F = 0 ∨ σ ≤ vw w (P F)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat π M)), B x = 0 ∨ σ ≤ vw w (B x)

def BoundsSum : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S : Finset Pl) (D : ℕ), 0 < D →
    ∀ (lcvR logκ LG E3 : ℝ) (lcvM L E1 E2 : J → ℝ) (l ell vG g : Pl → ℝ)
      (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w, 0 ≤ l w) →
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    (∀ w ∈ S, vG w ≤ (D : ℝ) * g w) → ∑ w ∈ S, l w * g w ≤ LG →
    (∀ j, lcvM j / D ≤ L j) →
    (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, l w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, l w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ E3 →
      lcvR / D ≤ logκ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, l w * F w j + LG + ∑ j, (E1 j + E2 j) + E3

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def PrimeSumSq : Prop :=
  (∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
    ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000) ∧
  Summable (fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) ∧
  ∑' p : Nat.Primes, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 1

def PlaceSumNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ)

def UntwistedChoice : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S Tw : Finset Pl) (D : ℕ), 0 < D → Tw ⊆ S →
    ∀ (l ell : Pl → ℝ) (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, I w j + Ic w j + jT w j = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →
    (∀ w ∈ Tw, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ Tw, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    ∃ err' Jx' η' : Pl → J → ℝ,
      (∀ w ∈ Tw, ∀ j, err' w j = err w j ∧ Jx' w j = Jx w j ∧ η' w j = η w j) ∧
      (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err' w j) + 2 / ell w ^ 2) * D) ∧
      (∀ w ∈ S, ∀ j, jT w j ≤ Jx' w j * D + η' w j) ∧
      (∀ j, ∑ w ∈ S, l w * (err' w j + Jx' w j) = ∑ w ∈ Tw, l w * (err w j + Jx w j)) ∧
      (∀ j, ∑ w ∈ S, l w * η' w j / D = ∑ w ∈ Tw, l w * η w j / D) ∧
      (∀ j, ∑ w ∈ S, l w * F w j = ∑ w ∈ Tw, l w * F w j)

end Formalism.DivisionValues
end
end

section

open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D

end Formalism.DivisionValues
end
end

section

open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

section Defs

def fnorm {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ :=
  Formalism.HermitianLatticesTheory.cnorm (Y⁻¹.mulVec x)

def fmaj {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i, star (Y⁻¹.mulVec x i) * Y⁻¹.mulVec y i

def pairC {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) : ℂ :=
  ∑ i, ∑ k, x i * y k * v.embedding (B (Pi.single i 1) (Pi.single k 1))

def chainFun {m : ℕ} {C : Fin (m + 1) → Type} (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) :
    ∀ i : Fin (m + 1), C 0 → C i :=
  Fin.induction (motive := fun i => C 0 → C i) id (fun j f => Kj j ∘ f)

def chainMat {R : Type} [Semiring R] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) R) :
    ∀ i : Fin (m + 1), Matrix (Fin (c i)) (Fin (c 0)) R :=
  Fin.induction (motive := fun i => Matrix (Fin (c i)) (Fin (c 0)) R) 1 (fun j A => Kj j * A)

def minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

end Defs

def FnormRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K),
      fnorm (X v) (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ∧
      fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (y i)) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y ∧
      ((fnorm (X v) (fun i => v.embedding (x i)) ^ 2 : ℝ) : ℂ) =
        fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (x i))

def OpNormDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (a D : ℕ)
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (XM v).det) → (∀ v, IsUnit (XE v).det) →
    ∀ (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (v : InfinitePlace K) (c : ℝ), 0 ≤ c →
      (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) v B ≤ c ↔
        ∀ (x : Fin a → ℂ) (y : Fin D → ℂ), ‖pairC v B x y‖ ≤ c * fnorm (XM v) x * fnorm (XE v) y)

def CompNormAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K,
      (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) v (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j))) ∧
      (chainMat Kj (Fin.last m) ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∑ j : Fin m, Formalism.HN.htMap (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (Matrix.mulVecLin (Kj j)))

def SminLog : Prop :=
  ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (κ : ℝ) (lam : J → Ix → ℝ), 0 < κ →
    (∀ j p, 0 < lam j p) →
      0 < κ * minOver (fun p => ∏ j, lam j p) ∧
      (∀ p, κ * minOver (fun p => ∏ j, lam j p) ≤ κ * ∏ j, lam j p) ∧
      (∃ p, κ * minOver (fun p => ∏ j, lam j p) = κ * ∏ j, lam j p) ∧
      Real.log (κ * minOver (fun p => ∏ j, lam j p)) =
        Real.log κ + minOver (fun p => ∑ j, Real.log (lam j p))

def HeightBoundConstant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (κ : InfinitePlace K → ℝ) (lam lamL : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lamL j p v) → (∀ j p v, lamL j p v ≤ lam j p v) →
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
    ∀ (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ),
    (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) →
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
        Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
          minOver (fun p => ∑ j, Real.log (lamL j p v))) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2)) -
          (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lamL j p v)) - meanLog κ

end Formalism.DivisionValues
end
end
