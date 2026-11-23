module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle058
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle055
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatIffMemLocP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle059
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  first | exact @GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | exact GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | (intros; apply GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocCongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem approx_int (A : Places F E sig) (g : ℕ) (hg : 0 < g) (p : HeightOneSpectrum (𝓞 F))
    (z : (A.loc p).Ep) (hz : z ∈ (A.L p).O) :
    ∃ x : 𝓞 E, ∃ o ∈ (A.L p).O, z - (A.loc p).ιE (x : E) = (A.loc p).ιE (g : E) * o := by
  have hgF : ((g : ℤ) : F) ≠ 0 := by exact_mod_cast hg.ne'
  let c : ∀ q, ((A.loc q).Fp)ˣ := fun q => Units.mk0 ((g : ℤ) : (A.loc q).Fp) (by
    rw [← map_intCast (A.loc q).ιF]; exact (map_ne_zero _).2 hgF)
  have hc := PlacesInt.intCast_isUnit_almost_all A (g : ℤ) (by exact_mod_cast hg.ne')
  have hcE : ∀ q, algebraMap (A.loc q).Fp (A.loc q).Ep (c q) = (A.loc q).ιE (g : E) := by
    intro q
    change algebraMap (A.loc q).Fp (A.loc q).Ep ((g : ℤ) : (A.loc q).Fp) = _
    rw [map_intCast, map_natCast, Int.cast_natCast]
  have hgO : ∀ q, (A.loc q).ιE (g : E) ∈ (A.L q).O := fun q => by
    rw [map_natCast]; exact natCast_mem (A.L q).O g
  let y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p z
  have hy : {q | y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  obtain ⟨-, hE, -⟩ := StrongApprox.strong_approx_additive A c hc
  obtain ⟨x, hx⟩ := hE y hy
  have hint : ∀ q, (A.loc q).ιE x ∈ (A.L q).O := by
    intro q
    obtain ⟨o, ho, he⟩ := hx q
    have hyq : y q ∈ (A.L q).O := by
      by_cases h : q = p
      · subst h
        change Pi.single (M := fun q => (A.loc q).Ep) q z q ∈ (A.L q).O
        rw [Pi.single_eq_same]; exact hz
      · change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
        rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : (A.loc q).ιE x = y q + algebraMap (A.loc q).Fp (A.loc q).Ep (c q) * o := by
      rw [← he]; ring
    rw [e, hcE]
    exact add_mem hyq (mul_mem (hgO q) ho)
  obtain ⟨xo, hxo⟩ := ((PlacesInt.integers_local A).1 x).1 hint
  obtain ⟨o, ho, he⟩ := hx p
  refine ⟨xo, -o, neg_mem ho, ?_⟩
  have hyp : y p = z := by
    change Pi.single (M := fun q => (A.loc q).Ep) p z p = z
    exact Pi.single_eq_same _ _
  rw [hyp, hcE] at he
  rw [hxo]
  linear_combination -he

section
variable (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}

theorem bc_sub (u v : Fin N → E) : A.bc p (u - v) = A.bc p u - A.bc p v := by
  funext i; simp [Places.bc]

theorem bc_smul (t : E) (u : Fin N → E) : A.bc p (t • u) = (A.loc p).ιE t • A.bc p u := by
  funext i; simp [Places.bc]

theorem bc_sum {ι : Type} (s : Finset ι) (f : ι → Fin N → E) :
    A.bc p (∑ i ∈ s, f i) = ∑ i ∈ s, A.bc p (f i) := by
  funext j; simp [Places.bc, Finset.sum_apply, map_sum]

theorem lat_smul (Λ : Submodule (𝓞 E) (Fin N → E)) (t : 𝓞 E) (v : Fin N → (A.loc p).Ep)
    (hv : v ∈ A.lat p Λ) : (A.loc p).ιE (t : E) • v ∈ A.lat p (Ideal.span {t} • Λ) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, hu, rfl⟩ := hw
    have e : (A.loc p).ιE (t : E) • A.bc p u = A.bc p (t • u) := by
      funext i
      change (A.loc p).ιE (t : E) * (A.loc p).ιE (u i) = (A.loc p).ιE (t • u i)
      rw [Algebra.smul_def, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hu, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o a _ ha =>
    have e : (A.loc p).ιE (t : E) • (o • a) = o • ((A.loc p).ιE (t : E) • a) := by
      change (A.loc p).ιE (t : E) • ((o : (A.loc p).Ep) • a) = (o : (A.loc p).Ep) • ((A.loc p).ιE (t : E) • a)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ o ha

end

theorem loc_cong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  intro F E _ _ _ _ _ sig A N r Λ hΛ g hg p y x ξp hO hlow hdiag hy hx
  choose ξ0 o ho hξ0 using fun a b => approx_int A g hg p (ξp a b) (hO a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else ξ0 a b
  have hd : ∀ a b, ∃ o ∈ (A.L p).O,
      ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E) = (A.loc p).ιE (g : E) * o := by
    intro a b
    by_cases h1 : b < a
    · refine ⟨0, zero_mem _, ?_⟩
      simp [ξ, h1, hlow a b h1]
    · by_cases h2 : a = b
      · subst h2
        refine ⟨0, zero_mem _, ?_⟩
        simp [ξ, hdiag]
      · refine ⟨o a b, ho a b, ?_⟩
        simp only [ξ, h1, h2, if_false]
        exact hξ0 a b
  have hFG : (Ideal.span {(g : 𝓞 E)} • Λ).FG := Submodule.FG.smul (Submodule.fg_span_singleton _) hΛ
  have hmem : ∀ b, A.bc p (x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a) ∈
      A.lat p (Ideal.span {(g : 𝓞 E)} • Λ) := by
    intro b
    rw [bc_sub, bc_sum]
    simp only [bc_smul]
    have e : A.bc p (x b) - ∑ a, (A.loc p).ιE ((ξ a b : 𝓞 E) : E) • A.bc p (y a) =
        (A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a)) +
          ∑ a, (ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E)) • A.bc p (y a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]; abel
    rw [e]
    refine add_mem (hx b) (Submodule.sum_mem _ fun a _ => ?_)
    obtain ⟨o', ho', he⟩ := hd a b
    rw [he, mul_smul]
    have h1 : (⟨o', ho'⟩ : (A.L p).O) • A.bc p (y a) ∈ A.lat p Λ := Submodule.smul_mem _ _ (hy a)
    have h2 := lat_smul A p Λ (g : 𝓞 E) _ h1
    have e2 : (((g : 𝓞 E) : E)) = (g : E) := by simp
    rw [e2] at h2
    exact h2
  refine ⟨ξ, fun a b h => by simp [ξ, h], fun a => by simp [ξ], fun P hP b => ?_⟩
  exact (LocDict.mem_lat_iff_mem_locP A N _ hFG p _).1 (hmem b) P hP

end GlobalTheory.HL.LocCongApprox
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramifiedConj

theorem exists_of_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (y : 𝓞 E)
    (hy : RingOfIntegers.mapRingHom (starRingEnd E) y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hfix : star (y : E) = (y : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) hy
    simpa only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply] using h
  obtain ⟨b, hb⟩ := (hc.fixed (y : E)).1 hfix

  have hint : IsIntegral ℤ b := by
    have hy' : IsIntegral ℤ (algebraMap F E b) := by
      rw [hb]
      exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hy'
  refine ⟨⟨b, hint⟩, ?_⟩
  ext
  exact hb

private lemma mem_map_comap_of_star_fixed {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : Ideal (𝓞 E))
    (z : 𝓞 E) (hz : RingOfIntegers.mapRingHom (starRingEnd E) z = z) (hzQ : z ∈ Q) :
    z ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  obtain ⟨a, ha⟩ := exists_of_fixed hc z hz
  rw [← ha]
  apply Ideal.mem_map_of_mem
  rw [Ideal.mem_comap, ha]
  exact hzQ

theorem le_map_comap_of_le_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (P Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (h1 : P ≤ Q) (h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E))) :
    P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  have hinv : ∀ z : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) z) = z := by
    intro z
    ext
    simp only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply, star_star]

  have hD : Ideal.span (Set.range fun θ : 𝓞 E => θ - RingOfIntegers.mapRingHom (starRingEnd E) θ)
      = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨_, _, hU⟩ := hc.cmUnram
    obtain ⟨θ, t, ht, hθ⟩ := hU M hM
    have htθ : t = RingOfIntegers.mapRingHom (starRingEnd E) θ := by
      ext
      rw [RingOfIntegers.mapRingHom_apply, starRingEnd_apply]
      exact ht
    subst htθ
    exact hθ (hDM (Ideal.subset_span ⟨θ, rfl⟩))
  intro x hx
  have hxQ : x ∈ Q := h1 hx
  have hsxQ : RingOfIntegers.mapRingHom (starRingEnd E) x ∈ Q := h2 hx

  have hgen : ∀ θ : 𝓞 E,
      x * (θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) ∈
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro θ
    set s := RingOfIntegers.mapRingHom (starRingEnd E) with hs
    have e : x * (θ - s θ) = (x + s x) * θ - (x * s θ + s x * θ) := by ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · refine mem_map_comap_of_star_fixed hc Q _ ?_ (Q.add_mem hxQ hsxQ)
      rw [map_add (f := _), hinv]
      ring
    · refine mem_map_comap_of_star_fixed hc Q _ ?_
        (Q.add_mem (Q.mul_mem_right _ hxQ) (Q.mul_mem_right _ hsxQ))
      rw [map_add (f := _), map_mul, map_mul, hinv, hinv]
      ring
  have key : ∀ d ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ),
      x * d ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨θ, rfl⟩ := hd
      exact hgen θ
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha
  have h1 : (1 : 𝓞 E) ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) := by
    rw [hD]
    exact Submodule.mem_top
  simpa using key 1 h1

end GlobalTheory.UnramifiedConj
end

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.CMDiscrSq

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
private lemma sub_mem_differentIdeal_of_eq_star (h : _root_.Formalism.BasicNotions.CMData F E) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  change (t : E) = star (θ : E) at ht
  have hst : star (t : E) = θ := by rw [ht, star_star]
  by_cases hθ : (θ : E) ∈ (algebraMap F E).range
  · have : t = θ := RingOfIntegers.coe_injective (by
      change (t : E) = θ
      rw [ht]
      exact (h.fixed _).2 hθ)
    rw [this, sub_self]
    exact zero_mem _
  have hF : ∀ x : 𝓞 E, star (x : E) = x → ∃ s : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) s = x := by
    intro x hx
    obtain ⟨a, ha⟩ := (h.fixed _).1 hx
    have hai : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1
        (by rw [IsScalarTower.coe_toAlgHom', ha]; exact x.isIntegral_coe)
    exact ⟨⟨a, hai⟩, RingOfIntegers.coe_injective ha⟩
  obtain ⟨s, hs⟩ := hF (θ + t) (by
    change star ((θ : E) + t) = (θ : E) + t
    rw [star_add, hst, ht, add_comm])
  obtain ⟨n, hn⟩ := hF (θ * t) (by
    change star ((θ : E) * t) = (θ : E) * t
    rw [star_mul, hst, ht])
  set p : (𝓞 F)[X] := X ^ 2 - C s * X + C n with hp_def
  have hpdeg : p.natDegree = 2 := by rw [hp_def]; compute_degree!
  have hpm : p.Monic := by rw [hp_def]; monicity!
  have hroot : aeval θ p = 0 := by
    simp only [hp_def, map_add (f := _), map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hroot
  have hmdeg : (minpoly (𝓞 F) θ).natDegree = 2 := by
    have hle : (minpoly (𝓞 F) θ).natDegree ≤ 2 := hpdeg ▸ natDegree_le_of_dvd hdvd hpm.ne_zero
    have hne1 : (minpoly (𝓞 F) θ).natDegree ≠ 1 := by
      intro h1
      obtain ⟨s', hs'⟩ := minpoly.natDegree_eq_one_iff.1 h1
      exact hθ ⟨(s' : F), by rw [← hs']; rfl⟩
    have hpos := minpoly.natDegree_pos hint
    omega
  have hmin : minpoly (𝓞 F) θ = p :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd (by omega)).symm
  have hint' : IsIntegral (𝓞 F) (θ : E) := hint.algebraMap
  have hFdeg : (minpoly F (θ : E)).natDegree = 2 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint',
      minpoly.algebraMap_eq RingOfIntegers.coe_injective, natDegree_map_eq_of_injective
        (IsFractionRing.injective (𝓞 F) F), hmdeg]
  have htop : IntermediateField.adjoin F {(θ : E)} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral _), hFdeg, h.deg2])
  have hgen : Algebra.adjoin F {algebraMap (𝓞 E) E θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
    change (IntermediateField.adjoin F {(θ : E)}).toSubalgebra = ⊤
    rw [htop, IntermediateField.top_toSubalgebra]
  have hd := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ hgen
  rw [hmin] at hd
  convert hd using 1
  simp [hp_def, hs]
  ring


open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
theorem _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top (h : _root_.Formalism.BasicNotions.CMData F E) : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := h.cmUnram.2.2 P hP
  exact hθt (hle (sub_mem_differentIdeal_of_eq_star h θ t ht))

end GlobalTheory.CMDiscrSq


open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.cm_discr_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by
  intro F E _ _ _ _ _ _ h
  have hd := _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h
  have hE := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, h.deg2] at hE
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs, hE]
    push_cast
    exact sq_abs _
  · have hmul := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [hd, Ideal.top_mul] at hmul
    rw [← hmul, absNorm_differentIdeal E (𝓞 E), hE]
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.iwasawaNMKIntegration_pi_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  first | exact @GlobalTheory.NMKProd.prod_formula | exact GlobalTheory.NMKProd.prod_formula | (intros; apply GlobalTheory.NMKProd.prod_formula <;> assumption)
end
