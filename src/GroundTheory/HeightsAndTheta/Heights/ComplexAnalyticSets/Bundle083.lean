module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
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
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

instance isIntegral_curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
    ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

theorem ringKrullDim_curveNormalisation_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    ringKrullDim (curveNormalisation I q) ≤ ringKrullDim (curveLocalRing I q) :=
  Order.krullDim_le_of_strictMono
    (fun Q ↦ ⟨Q.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)), inferInstance⟩)
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap (R := curveLocalRing I q) h

theorem exists_ord_eq_ord_polynomial (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (a : curveLocalRing I q) : ∃ f : MvPolynomial (Fin n) ℂ, ∀ P : MaximalSpectrum (curveNormalisation I q),
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl y
  refine ⟨f, fun P ↦ ?_⟩
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ)) :=
    isUnit_algebraMap_curveLocalRing I q h fun H ↦ h.2 (RingHom.mem_ker.2 H)
  let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
  have hπ : ∀ g : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g =
      π (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) g) := fun _ ↦ rfl
  have hy' : π y = a := hy
  have hfh' : IsLocalization.mk' (Localization.AtPrime (RingHom.ker (eval q))) f h = y := hfh
  have heq : a *
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
    rw [← hy', ← hfh', hπ, hπ, ← map_mul, IsLocalization.mk'_spec]
  rw [← heq, map_mul, map_mul, Ring.ord_mul_of_isUnit_right ((hu.map _).map _)]

theorem OrdDeterminesPlace.proof (hfin : CurveNormalisationFinite.Statement) : OrdDeterminesPlace.Statement := by
  intro n I q hrad hdim P P' hord
  have : Module.Finite (curveLocalRing I q) (curveNormalisation I q) := hfin n I q hrad
  have : IsNoetherianRing (curveNormalisation I q) := IsNoetherianRing.of_finite (curveLocalRing I q) _

  have hdimP : ∀ Q : MaximalSpectrum (curveNormalisation I q), Ring.KrullDimLE 1 (Localization.AtPrime Q.asIdeal) := by
    intro Q
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal]
    calc (Q.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim (curveNormalisation I q) :=
          Ideal.height_le_ringKrullDim_of_ne_top Q.isMaximal.ne_top
      _ ≤ ringKrullDim (curveLocalRing I q) := ringKrullDim_curveNormalisation_le I q
      _ = 1 := by rw [hdim]

  have hO : ∀ a : curveLocalRing I q,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) := by
    intro a
    obtain ⟨f, hf⟩ := exists_ord_eq_ord_polynomial I q a
    rw [hf P, hf P', hord f]
  by_contra hne
  obtain ⟨x, hxP, hxP'⟩ : ∃ x, x ∈ P.asIdeal ∧ x ∉ P'.asIdeal := by
    by_contra! H
    exact hne (MaximalSpectrum.ext (P.isMaximal.eq_of_le P'.isMaximal.ne_top H))

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (curveLocalRing I q))
    (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
  have hax : algebraMap (curveLocalRing I q) (curveNormalisation I q) a =
      algebraMap (curveLocalRing I q) (curveNormalisation I q) s * x := by
    apply Subtype.ext
    change algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) a =
      algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s * (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
    rw [← hs, IsLocalization.mk'_spec']

  have hsN : algebraMap (curveLocalRing I q) (curveNormalisation I q) s ∈ nonZeroDivisors (curveNormalisation I q) := by
    have hu : IsUnit (algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s) :=
      IsLocalization.map_units _ s
    exact mem_nonZeroDivisors_of_injective (f := (integralClosure (curveLocalRing I q)
      (FractionRing (curveLocalRing I q))).val) Subtype.val_injective hu.mem_nonZeroDivisors
  have hsP : ∀ Q : MaximalSpectrum (curveNormalisation I q),
      algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s) ∈
        nonZeroDivisors (Localization.AtPrime Q.asIdeal) := fun Q ↦
    IsLocalization.nonZeroDivisors_le_comap Q.asIdeal.primeCompl _ hsN

  have h' : Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) := by
    rw [hax, map_mul, Ring.ord_mul_of_isUnit_right]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P'.asIdeal x).2 hxP'

  have hP : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) +
      Ring.ord (Localization.AtPrime P.asIdeal)
        (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) := by
    rw [hax, map_mul, Ring.ord_mul' _ (hsP P)]
  have hfin' : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) ≠ ⊤ := by
    have := hdimP P
    exact Ring.ord_ne_top (hsP P)
  rw [hO a, h', ← hO s] at hP
  have hx0 : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = 0 := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hfin'
    rw [← hk] at hP
    generalize Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = y at hP ⊢
    induction y using ENat.recTopCoe with
    | top => simp at hP
    | coe m => norm_cast at hP ⊢; omega

  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hx0
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P.asIdeal x).1 hx0 hxP

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk J y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)
      rw [Ideal.mem_quotient_iff_mem hJM]
      exact hz
    · intro h
      change Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h
      rw [Ideal.mem_quotient_iff_mem hJM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def radialTransform (d : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * t ^ d - ∫ τ in (0 : ℝ)..t, a τ * ((d : ℝ) * τ ^ (d - 1))

theorem radialTransform_zero (a : ℝ → ℝ) : radialTransform 0 a = a := by
  funext t
  simp [radialTransform]

theorem integral_const_mul_dpow (e : ℕ) (c t : ℝ) :
    ∫ τ in (0 : ℝ)..t, c * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) = c * t ^ (e + 1) := by
  simp only [Nat.add_sub_cancel]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

theorem radialTransform_eq_zero_of_const (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by
  have hint : ∫ τ in (0 : ℝ)..t, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ∫ τ in (0 : ℝ)..t, a 0 * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    rw [ha τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  rw [radialTransform, hint, integral_const_mul_dpow, ha t ht]
  ring

def RegRadialWeight.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * ((d : ℝ) * τ ^ (d - 1))) = 0 →
      ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => radialTransform d a (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

variable {σ : Type*}

theorem pointLocalRing_exists_mul_eq (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (x : pointLocalRing I w) :
    ∃ a s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧
      x * algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) s = algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl y
  refine ⟨a, s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have h := congrArg (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ)
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) a s)
  rw [map_mul] at h
  exact h

theorem pointLocalRing_exists_mul_mem (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈
      I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hg
  obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem
  refine ⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have : (s : MvPolynomial σ ℂ) * g = j := hinj (by rw [map_mul, mul_comm]; exact hjs)
  rw [this]
  exact j.2

theorem pointLocalRing_eval_ne_zero_of_isUnit (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by
  intro h0
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  have hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)))
      (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, map_one]
    exact hv
  have hd := hle (Ideal.Quotient.eq.1 hv')
  have h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    have := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem
      (Ideal.mul_mem_right z _ hum) hd
    simp at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem ord_zero_eq_top_of_dvr (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by
  rw [Ring.ord_zero]
  by_contra h
  have hfin := Module.length_ne_top_iff.1 h
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem ord_pow_irreducible_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

theorem differentiable_eval_pointLocal [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem analyticAt_eval_disc [Fintype σ] {r : ℝ} (hr : 0 < r) {φ : (Fin 1 → ℂ) → σ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) (g : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 := by
  have hc : DifferentiableOn ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) :=
    (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn
  have hmaps : Set.MapsTo (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) (Metric.ball 0 r) := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) (Metric.ball 0 r) :=
    (differentiable_eval_pointLocal g).comp_differentiableOn (hφ.comp hc hmaps)
  exact hd.analyticAt (Metric.ball_mem_nhds 0 hr)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelPointOfPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ∀ P : MaximalSpectrum (curveNormalisation J q),
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
            Ring.ord (pointLocalRing M.ideal w)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end
