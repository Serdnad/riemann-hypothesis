module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace OrdZeroUnit

variable {E : Type} [Field E] [NumberField E]

theorem norm_modEq_one (a : ℕ) (y : 𝓞 E) :
    (((Algebra.norm ℤ (1 + (a : 𝓞 E) * y) : ℤ)) : ZMod a) = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod a)), RingHom.map_det]
  have : (Int.castRingHom (ZMod a)).mapMatrix (Algebra.leftMulMatrix b (1 + (a : 𝓞 E) * y)) = 1 := by
    rw [map_add (f := _), map_one, map_mul, map_natCast, map_add (f := _), map_one, map_mul, map_natCast,
      ← map_natCast (algebraMap (ZMod a) (Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (ZMod a))), ZMod.natCast_self, map_zero, zero_mul, add_zero]
  rw [this, Matrix.det_one]

theorem isUnit_of_valuation_eq_one (z : E) (hz : z ≠ 0) (h : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E z = 1) :
    ∃ u : 𝓞 E, IsUnit u ∧ algebraMap (𝓞 E) E u = z := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z (fun v => (h v).le)
  obtain ⟨y', hy'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z⁻¹
    (fun v => by rw [map_inv₀, h v, inv_one])
  have hyy : y * y' = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hy, hy', mul_inv_cancel₀ hz, map_one]
  exact ⟨y, ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩, hy⟩

end OrdZeroUnit
end GlobalTheory

namespace GlobalTheory
namespace OrdZeroUnit

theorem valuation_eq_one_of_approx : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E),
    x ≠ 0 → Valued.v x ≤ 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → Valued.v x = 1 := by
  intro E _ _ w x hx0 hx1 hyp
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have hxpos : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have ht0 : x * x ≠ 0 := mul_ne_zero hx0 hx0
  have htx : Valued.v (x * x) < Valued.v x := by
    rw [map_mul]
    calc Valued.v x * Valued.v x < 1 * Valued.v x := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hxpos)
      _ = Valued.v x := one_mul _

  have hw_eq : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k - x) ≤ Valued.v (x * x) →
      w.valuation E k = Valued.v x := by
    intro k hk
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hk htx)

  have hoff : ∀ (a : ℕ), 0 < a → ∀ (k : E), k ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 E),
      v.valuation E ((k - 1) / (a : E)) ≤ 1 → v.valuation E k⁻¹ ≤ 1 →
      v.valuation E k = 1 ∧ v.valuation E (k - 1) ≤ 1 := by
    intro a ha k hk0 v h1 h2
    have hva : v.valuation E (a : E) ≤ 1 := by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact v.valuation_le_one _
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
    have hk1 : v.valuation E (k - 1) ≤ 1 := by
      have : k - 1 = ((k - 1) / a) * a := by field_simp
      rw [this, map_mul]
      calc v.valuation E ((k - 1) / a) * v.valuation E (a : E) ≤ 1 * 1 := mul_le_mul' h1 hva
        _ = 1 := one_mul _
    have hk : v.valuation E k ≤ 1 := by
      have : k = (k - 1) + 1 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le hk1 (by rw [map_one]))
    refine ⟨le_antisymm hk ?_, hk1⟩
    calc 1 = v.valuation E (k * k⁻¹) := by rw [mul_inv_cancel₀ hk0, map_one]
      _ = v.valuation E k * v.valuation E k⁻¹ := map_mul _ _ _
      _ ≤ v.valuation E k * 1 := mul_le_mul' le_rfl h2
      _ = v.valuation E k := mul_one _

  obtain ⟨k₀, hk₀off, hk₀w⟩ := hyp 1 one_pos (x * x) ht0
  have hw0 := hw_eq _ hk₀w
  have hk₀0 : (k₀ : E) ≠ 0 := k₀.ne_zero
  have hoff0 : ∀ v, v ≠ w → v.valuation E (k₀ : E) = 1 := fun v hv =>
    (hoff 1 one_pos _ hk₀0 v (hk₀off v hv).1 (hk₀off v hv).2).1
  obtain ⟨k₀', hk₀'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k₀ : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hw0]; exact hx1
    · exact (hoff0 v hv).le)
  set R : ℕ := (Algebra.norm ℤ k₀').natAbs with hR
  set q : ℕ := Ideal.absNorm w.asIdeal with hq
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set a : ℕ := q * (R + 1) + 1 with ha
  have hapos : 0 < a := Nat.succ_pos _
  have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
    intro h
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem h (w.asIdeal.mul_mem_right (((R + 1 : ℕ)) : 𝓞 E) hqmem)
      rw [ha] at this; push_cast at this; simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hwa : w.valuation E (a : E) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) a]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hanot

  obtain ⟨k, hkoff, hkw⟩ := hyp a hapos (x * x) ht0
  have hwk := hw_eq _ hkw
  have hk0 : (k : E) ≠ 0 := k.ne_zero
  have hoffk : ∀ v, v ≠ w → v.valuation E (k : E) = 1 ∧ v.valuation E ((k : E) - 1) ≤ 1 :=
    fun v hv => hoff a hapos _ hk0 v (hkoff v hv).1 (hkoff v hv).2
  obtain ⟨kk, hkk⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hwk]; exact hx1
    · exact (hoffk v hv).1.le)

  obtain ⟨u, hu, hue⟩ := isUnit_of_valuation_eq_one ((k : E) / k₀) (div_ne_zero hk0 hk₀0) (fun v => by
    rw [map_div₀]
    by_cases hv : v = w
    · subst hv; rw [hw0, hwk, div_self hxpos]
    · rw [(hoffk v hv).1, hoff0 v hv, div_one])
  have hkku : kk = u * k₀' := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hkk, hue, hk₀', div_mul_cancel₀ _ hk₀0]
  have hNk : (Algebra.norm ℤ kk).natAbs = R := by
    rw [hkku, map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 (hu.map _), one_mul]

  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (((k : E) - 1) / (a : E))
    (fun v => by
      by_cases hv : v = w
      · subst hv
        rw [map_div₀, hwa, div_one, ← hkk, ← map_one (algebraMap (𝓞 E) E), ← map_sub]
        exact v.valuation_le_one _
      · exact (hkoff v hv).1)
  have hkky : kk = 1 + (a : 𝓞 E) * y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 hapos.ne'
    rw [map_add (f := _), map_one, map_mul, map_natCast, hy, hkk]
    field_simp
    ring
  have hcong := norm_modEq_one a y
  rw [← hkky] at hcong
  have hdvd : (a : ℤ) ∣ Algebra.norm ℤ kk - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ a).1 (by rw [hcong, Int.cast_one])
  have hN1 : Algebra.norm ℤ kk = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    have hA : ((R : ℤ) + 2) ≤ (a : ℤ) := by
      rw [ha]; push_cast
      nlinarith [(Nat.one_le_cast (α := ℤ)).2 hqpos, (Nat.cast_nonneg R : (0 : ℤ) ≤ R)]
    have hR0 : (0 : ℤ) ≤ R := Nat.cast_nonneg R
    rcases Int.natAbs_eq (Algebra.norm ℤ kk) with h | h <;> rw [hNk] at h <;> rw [h] at hc ⊢
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith

  have hunit : IsUnit kk := by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton, hN1]
    rfl
  have hmem : kk ∈ w.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E kk) < 1
    rw [hkk, hwk]; exact hlt
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

end OrdZeroUnit
end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompositumCompletion

theorem exists_completion_map {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    (jL : L →+* L') (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L'))
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) :
    ∃ μ : v.adicCompletion L →+* v'.adicCompletion L', Continuous μ ∧
      ∀ x, μ (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  letI : Algebra L L' := jL.toAlgebra
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨by ext x; exact (h x).symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver L L' v v').continuous
  let φ : v.adicCompletion L →+* v'.adicCompletion L' :=
    ((HeightOneSpectrum.adicCompletion.equiv L' v').symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L'))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  refine ⟨φ, ?_, fun x => ?_⟩
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' v').comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L')))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  · apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)

theorem exists_ringEquiv_completion : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  intro E L E' L' _ _ _ _ _ _ _ _ _ _ w v w' v' j jL i hv hv' hjv hjL hadj hic hij
  obtain ⟨κ, hκc, hκ⟩ := exists_completion_map (algebraMap E L) w v (fun x => hv x)
  obtain ⟨κ', hκ'c, hκ'⟩ := exists_completion_map (algebraMap E' L') w' v' (fun x => hv' x)
  obtain ⟨μ, hμc, hμ⟩ := exists_completion_map jL v v' hjv
  have hcomm : ∀ a, μ (κ a) = κ' (i a) := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (hμc.comp hκc) (hκ'c.comp hic)
      (funext fun x => by simp only [Function.comp_apply, hκ, hμ, hjL, hij, hκ'])) a
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := E) (M := L)
  have hrange : Set.range jL ⊆ Submodule.span E' (jL '' (s : Set L)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span E (s : Set L) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul, hjL, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha
  have htop : Submodule.span E' (Set.range jL) = ⊤ := by
    have h1 := Algebra.adjoin_eq_span E' (Set.range jL)
    rw [hadj, Algebra.top_toSubmodule] at h1
    have hcl : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL :=
      congrArg SetLike.coe (Submonoid.closure_eq (MonoidHom.mrange jL))
    rw [h1, hcl]
  have hspan : ∀ y : L', y ∈ Submodule.span E' (jL '' (s : Set L)) := fun y => by
    have hy : y ∈ Submodule.span E' (Set.range jL) := htop ▸ Submodule.mem_top
    exact (Submodule.span_le.2 hrange) hy
  letI : Algebra (w'.adicCompletion E') (v'.adicCompletion L') := κ'.toAlgebra
  haveI : ContinuousSMul (w'.adicCompletion E') (v'.adicCompletion L') :=
    continuousSMul_of_algebraMap _ _ hκ'c
  letI : NontriviallyNormedField (w'.adicCompletion E') := Valued.toNontriviallyNormedField _ _
  let M : Submodule (w'.adicCompletion E') (v'.adicCompletion L') :=
    Submodule.span _ ((fun y => algebraMap L' (v'.adicCompletion L') (jL y)) '' (s : Set L))
  haveI : FiniteDimensional (w'.adicCompletion E') M :=
    FiniteDimensional.span_of_finite _ (s.finite_toSet.image _)
  have hcl : IsClosed (M : Set (v'.adicCompletion L')) := Submodule.closed_of_finiteDimensional _
  have hM : ∀ y : L', algebraMap L' (v'.adicCompletion L') y ∈ M := fun y => by
    induction hspan y using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : algebraMap L' (v'.adicCompletion L') (c • a) =
          (algebraMap E' (w'.adicCompletion E') c) • algebraMap L' (v'.adicCompletion L') a := by
        rw [Algebra.smul_def c a, map_mul, ← hκ']; rfl
      rw [e]; exact Submodule.smul_mem _ _ ha
  have hMμ : ∀ z ∈ M, z ∈ Set.range μ := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, _, rfl⟩ := hz
      exact ⟨algebraMap L _ x, hμ x⟩
    | zero => exact ⟨0, map_zero μ⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' + b', map_add μ a' b'⟩
    | smul c a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨κ (i.symm c) * a', by rw [map_mul, hcomm, i.apply_symm_apply]; rfl⟩
  have hsurj : Function.Surjective μ := fun y => by
    have hy : y ∈ (M : Set (v'.adicCompletion L')) :=
      (HeightOneSpectrum.denseRange_algebraMap L' v').induction_on
        (p := fun y => y ∈ (M : Set (v'.adicCompletion L'))) y hcl hM
    exact hMμ y hy
  exact ⟨RingEquiv.ofBijective μ ⟨μ.injective, hsurj⟩, hμc, fun x => hμ x⟩

end GlobalTheory.CompositumCompletion
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem trace_map_of_adjoin_range_eq_top_of_finrank_eq : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  intro E L E' L' _ _ _ _ _ _ _ j jL hcomp hadj hrank z
  classical
  set n := Module.finrank E L
  let b : Module.Basis (Fin n) E L := Module.finBasis E L
  have hpos : 0 < Module.finrank E' L' := by rw [hrank]; exact Module.finrank_pos
  haveI : FiniteDimensional E' L' := Module.finite_of_finrank_pos hpos
  let v : Fin n → L' := fun k => jL (b k)
  have hexp : ∀ w : L, jL w = ∑ k, j (b.repr w k) • v k := by
    intro w
    conv_lhs => rw [← b.sum_repr w]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hcomp, ← Algebra.smul_def]
  have hspan : Submodule.span E' (Set.range jL) ≤ Submodule.span E' (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [hexp w]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hadj' : Subalgebra.toSubmodule (Algebra.adjoin E' (Set.range jL)) = Submodule.span E' (Set.range jL) := by
    apply Algebra.adjoin_eq_span_of_subset
    have : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL := by
      have := Submonoid.closure_eq (MonoidHom.mrange (jL : L →* L'))
      simpa using congrArg (fun S : Submonoid L' => (S : Set L')) this
    rw [this]; exact Submodule.subset_span
  have htop : (⊤ : Submodule E' L') ≤ Submodule.span E' (Set.range v) := by
    rw [hadj, Algebra.top_toSubmodule] at hadj'
    rw [hadj']; exact hspan
  let b' : Module.Basis (Fin n) E' L' := basisOfTopLeSpanOfCardEqFinrank v htop (by simp [hrank, n])
  have hb' : ∀ k, b' k = v k := fun k => by simp [b']
  have hrepr : ∀ w : L, ∀ i, b'.repr (jL w) i = j (b.repr w i) := by
    intro w i
    have : jL w = b'.equivFun.symm (fun k => j (b.repr w k)) := by
      rw [Module.Basis.equivFun_symm_apply, hexp w]
      simp [hb']
    rw [← b'.equivFun_apply, this, LinearEquiv.apply_symm_apply]

  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', v, ← map_mul, hrepr]

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixApprox

theorem val_lt_map {K : Type} [Field K] (B : ValuationSubring K) (τ : K ≃+* K)
    (hB : ∀ z, τ z ∈ B ↔ z ∈ B) (a b : K) (h : B.valuation a < B.valuation b) :
    B.valuation (τ a) < B.valuation (τ b) := by
  have hb : b ≠ 0 := by
    rintro rfl; simp at h
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero]
    exact (Valuation.pos_iff _).2 (by simpa using hb)
  · have hta : τ a ≠ 0 := by simpa using ha
    rw [← not_le] at h ⊢
    intro h'
    apply h
    have h1 : B.valuation (τ b / τ a) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hta)]; exact h'
    rw [ValuationSubring.valuation_le_one_iff, ← map_div₀, hB] at h1
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 ha)] at h1
    exact h1

theorem fix_of_approx : ∀ (K : Type) [Field K] [CharZero K] (B : ValuationSubring K) (τ : K ≃+* K), (∀ z, τ z ∈ B ↔ z ∈ B) → ∀ y : K, IsAlgebraic ℚ y → (∀ δ : K, δ ≠ 0 → ∃ u : K, τ u = u ∧ B.valuation (y - u) < B.valuation δ) → τ y = y := by
  intro K _ _ B τ hB y _ happ
  by_contra hne
  set m := τ y with hm
  set s := τ.symm y with hs
  have hym : y - m ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hys : y - s ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg τ (sub_eq_zero.1 h)
    rw [hs, RingEquiv.apply_symm_apply] at h'
    exact h'
  obtain ⟨u, hu, hlt⟩ := happ (if B.valuation (y - m) ≤ B.valuation (y - s) then y - m else y - s)
    (by split_ifs <;> assumption)
  have h1 : B.valuation (y - u) < B.valuation (y - m) := by
    split_ifs at hlt with hc
    · exact hlt
    · exact lt_of_lt_of_le hlt (le_of_lt (not_le.1 hc))
  have h2 : B.valuation (y - u) < B.valuation (y - s) := by
    split_ifs at hlt with hc
    · exact lt_of_lt_of_le hlt hc
    · exact hlt
  have h3 := val_lt_map B τ hB _ _ h2
  have e1 : τ (y - u) = m - u := by rw [map_sub, hu]
  have e2 : τ (y - s) = m - y := by rw [map_sub, hs, RingEquiv.apply_symm_apply]
  rw [e1, e2] at h3
  have h4 : B.valuation (m - y) = B.valuation (y - m) := Valuation.map_sub_swap _ _ _
  have h5 : m - y = (m - u) - (y - u) := by ring
  have h6 : B.valuation (m - y) < B.valuation (m - y) := by
    calc B.valuation (m - y) = B.valuation ((m - u) - (y - u)) := by rw [← h5]
      _ < B.valuation (m - y) := Valuation.map_sub_lt _ h3 (h4 ▸ h1)
  exact lt_irrefl _ h6

end GlobalTheory.FixApprox
end
