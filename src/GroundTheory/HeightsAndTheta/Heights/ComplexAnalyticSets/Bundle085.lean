module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import Mathlib.Analysis.Analytic.Order
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem sliceCMUnmixed_local (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by
  intro P hP hPm
  obtain ⟨I, hI⟩ : ∃ I, I = J ⊔ Ideal.span (Set.range ℓ) := ⟨_, rfl⟩
  rw [← hI] at hP hS ⊢
  have hJI : J ≤ I := hI ▸ le_sup_left
  let x : Fin d → B := fun i => π (algebraMap R (Localization.AtPrime m) (ℓ i))

  have hspan : Ideal.span (Set.range x) = (I.map (algebraMap R (Localization.AtPrime m))).map π := by
    rw [hI, Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker π).2 hker.ge, bot_sup_eq,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  have hker_le : ∀ Q : Ideal R, J ≤ Q → RingHom.ker π ≤ Q.map (algebraMap R (Localization.AtPrime m)) :=
    fun Q hQ => hker ▸ Ideal.map_mono hQ
  have hcomap : ∀ Q : Ideal R, J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π =
        Q.map (algebraMap R (Localization.AtPrime m)) := fun Q hQ => by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hker_le Q hQ)]

  have hdimx : ringKrullDim (B ⧸ Ideal.span (Set.range x)) = (1 : ℕ) := by
    let f : Localization.AtPrime m →+* B ⧸ Ideal.span (Set.range x) := (Ideal.Quotient.mk _).comp π
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
    have hkf : RingHom.ker f = I.map (algebraMap R (Localization.AtPrime m)) := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap,
        hcomap I hJI]
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hkf), hS]
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact map_nonunit π _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (ℓ i)).2
      (hℓ i))
  have hsum : ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdimx, hB, ← Nat.cast_add, Nat.add_comm]

  obtain ⟨hPp, y, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmemP : ∀ s, s ∈ P ↔ s * r ∈ I := fun s => by
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot,
      show s • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (s * r) from rfl, Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun s hs => (hmemP s).2 (I.mul_mem_right r hs)
  have hdisj : ∀ Q : Ideal R, Q ≤ m → Disjoint (m.primeCompl : Set R) Q :=
    fun Q hQ => Set.disjoint_left.2 fun u hu huQ => hu (hQ huQ)
  have hprime : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).IsPrime := fun Q hQ hQm hJQ => by
    have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) Q hQ (hdisj Q hQm)
    exact Ideal.map_isPrime_of_surjective hπ (hker_le Q hJQ)
  have hback : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      (((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π).comap
        (algebraMap R (Localization.AtPrime m)) = Q := fun Q hQ hQm hJQ => by
    rw [hcomap Q hJQ]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hQ (hdisj Q hQm)
  obtain ⟨p, hp⟩ : ∃ p, p = (P.map (algebraMap R (Localization.AtPrime m))).map π := ⟨_, rfl⟩
  have hpP : p.IsPrime := hp ▸ hprime P hPp hPm (hJI.trans hIP)

  have hass : p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)) := by
    refine isAssociatedPrime_iff.2 ⟨hpP, Ideal.Quotient.mk _ (π (algebraMap R (Localization.AtPrime m) r)), ?_⟩
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
      show π a • Ideal.Quotient.mk (Ideal.span (Set.range x)) (π (algebraMap R (Localization.AtPrime m) r)) =
        Ideal.Quotient.mk _ (π (a * algebraMap R (Localization.AtPrime m) r)) by rw [map_mul]; rfl,
      Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap, ← Ideal.mem_comap, hcomap I hJI, hp,
      hcomap P (hJI.trans hIP)]
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl a
    rw [← IsLocalization.mk'_one (M := m.primeCompl) (Localization.AtPrime m) r, ← IsLocalization.mk'_mul,
      mul_one, IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    simp_rw [hmemP, mul_assoc]
  obtain ⟨hmin, hdimp⟩ := h B d x hxm hsum p hass
  refine ⟨⟨⟨hPp, hIP⟩, fun Q ⟨hQp, hIQ⟩ hQP => ?_⟩, fun hPeq => ?_⟩
  · have hQm : Q ≤ m := hQP.trans hPm
    have hJQ : J ≤ Q := hJI.trans hIQ
    have h1 : Ideal.span (Set.range x) ≤ (Q.map (algebraMap R (Localization.AtPrime m))).map π := by
      rw [hspan]
      exact Ideal.map_mono (Ideal.map_mono hIQ)
    have h2 : (Q.map (algebraMap R (Localization.AtPrime m))).map π ≤ p :=
      hp ▸ Ideal.map_mono (Ideal.map_mono hQP)
    have h3 := hmin.2 ⟨hprime Q hQp hQm hJQ, h1⟩ h2
    rw [← hback P hPp hPm (hJI.trans hIP), ← hback Q hQp hQm hJQ, ← hp]
    exact Ideal.comap_mono (Ideal.comap_mono h3)
  · have hpmax : p.IsMaximal := by
      have := Ideal.map_eq_top_or_isMaximal_of_surjective π hπ
        (maximalIdeal.isMaximal (Localization.AtPrime m))
      rw [hPeq, Localization.AtPrime.map_eq_maximalIdeal] at hp
      rw [← hp] at this
      exact this.resolve_left hpP.ne_top
    let := Ideal.Quotient.field p
    have h0 : ringKrullDim (B ⧸ p) = 0 := ringKrullDim_eq_zero_of_field (B ⧸ p)
    rw [hdimp, hdimx] at h0
    exact absurd h0 (by simp)

theorem SliceCMUnmixed.proof (h : CMQuotientUnmixed.Statement) : SliceCMUnmixed.Statement := by
  intro n d J L q hCM hdimB hdimS P hP hPm
  have : IsCohenMacaulayLocalRing (localRingAt J q) := hCM
  have hℓ : ∀ i, linPoly L i - C ((L *ᵥ q) i) ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := by
    intro i
    rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self]
  have hsl : sliceIdeal J L q = J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i)) := rfl
  rw [hsl] at hP hdimS ⊢
  have h1 := sliceCMUnmixed_local h (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) J
    (fun i => linPoly L i - C ((L *ᵥ q) i)) hℓ (localRingAt J q)
  have h2 := h1 (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h3 := h2 hdimB hdimS
  exact h3 P hP hPm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserBranchSimpleZero.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ)
    (r : ℝ) (φ : (Fin 1 → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) → φ 0 = w →
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)

theorem VarBranch.eventually_mem_zeroSet {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by
  have key : ∀ f ∈ J, ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), eval (c.toFun t) f = 0 := by
    intro f hf
    have h0 := analyticOrderAt_eq_top.1 (h f hf)
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually h0] with t ht
    have : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    rwa [this] at ht
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  filter_upwards [(s.eventually_all).2 fun g hg ↦ key g (hs ▸ Submodule.subset_span hg)] with t ht f hf
  have hle : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤ RingHom.ker (eval (c.toFun t)) :=
    Ideal.span_le.2 fun g hg ↦ ht g hg
  have hf' : f ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
    rw [Ideal.span, hs]
    exact hf
  exact hle hf'

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∃ P : MaximalSpectrum (curveNormalisation I q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ModelLocalizationMaximalPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (P : Ideal (Localization (normalModelSubmonoid M q))), P.IsMaximal →
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        P.comap ((algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
            (Ideal.Quotient.mk M.ideal)) =
          RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ ν : VarBranch I 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceHasBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ b, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimeBranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimePlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (curveLocalRing J q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation J q), ∃ ν : VarBranch J 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchSameOrder.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c d : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) →
      ∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder d f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def SameOrderBranchesMeet.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c c' : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder c' f) →
      ∃ x ∈ c.image ∩ c'.image, x ≠ q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def SameOrdersLiftCentre.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : NormalModel J)
    (γ γ' : VarBranch J 1 q) (Γ Γ' : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) →
    (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) →
    DifferentiableOn ℂ Γ' (Metric.ball 0 γ'.radius) →
    (∀ τ ∈ Metric.ball 0 γ'.radius, Γ' τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ' τ) = γ'.toFun τ) →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder γ f = branchOrder γ' f) →
      Γ 0 = Γ' 0

end

end GroundTheory.Heights₂.Heights
end
