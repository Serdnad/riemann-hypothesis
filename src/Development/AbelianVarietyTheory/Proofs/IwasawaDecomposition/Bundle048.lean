module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameEis

open Polynomial

theorem two_le_normV (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')
  omega

theorem minpoly_and_norm_of_pow_eq_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E)) (ϖ : 𝓞 E),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
      minpoly E π = Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E) ∧
      Algebra.norm E (IntermediateField.AdjoinSimple.gen E π) = (-1) ^ normV v * (ϖ : E) := by
  intro E Ω _ _ _ _ v ϖ hmem hnot π hπ
  have hq := two_le_normV E v
  set n := normV v - 1 with hn
  have hn1 : 0 < n := by omega
  have hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hn1.ne'
  have hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n := natDegree_X_pow_sub_C _
  have hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using v.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)
  have hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  have hirrE : Irreducible (X ^ n - C (ϖ : E)) := by
    rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr
  have hmonE : (X ^ n - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hn1.ne'
  have hroot : aeval π (X ^ n - C (ϖ : E)) = 0 := by
    simp [hπ]
  have hmin : minpoly E π = X ^ n - C (ϖ : E) :=
    (minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm
  refine ⟨hmin, ?_⟩
  have hx : IsIntegral E π := ⟨_, hmonE, hroot⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C _]
  rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
  have : normV v = n + 1 := by omega
  rw [this, pow_succ]; ring

end GlobalTheory.TameEis
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRatio

theorem ratio_cong : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ v A hA u hu π t hπ ht τ τ' _hτ hτ' h1 h2
  have hq1 : 1 < normV v := by
    unfold normV
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have : Finite (𝓞 E ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    exact Finite.one_lt_card
  set U : Ω := algebraMap E Ω (u : E) with hUdef
  have hint : IsIntegral ℤ U := (RingOfIntegers.isIntegral_coe u).map ((algebraMap E Ω).toIntAlgHom)
  have hUle : A.valuation U ≤ 1 :=
    (Valuation.valuationSubring.integers A.valuation).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top hint)
  have hU1 : A.valuation U = 1 := le_antisymm hUle (not_lt.mp fun h => hu ((hA u).mp h))
  set s : Ω := τ'⁻¹ t with hsdef
  have hs : τ' s = t := by
    show τ' (τ'⁻¹ t) = t
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hsn : s ^ (normV v - 1) = U := by
    show (τ'⁻¹ t) ^ (normV v - 1) = U
    rw [← map_pow, ht, hUdef, AlgEquiv.commutes]
  have hvs : A.valuation s = 1 := by
    have h : A.valuation s ^ (normV v - 1) = 1 := by rw [← map_pow, hsn, hU1]
    exact (pow_eq_one_iff.mp h).resolve_right (by omega)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hF : A.valuation (t - s ^ normV v) < 1 := by
    have := hτ'.2 s hvs.le
    rwa [hs] at this
  have hinv : τ'⁻¹ π * s = π * t := by
    rw [hsdef, ← map_mul]
    calc τ'⁻¹ (π * t) = τ'⁻¹ (τ' (π * t)) := by rw [h2]
      _ = π * t := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hrat : (τ'⁻¹ * τ) π = τ'⁻¹ π := by rw [AlgEquiv.mul_apply, h1]
  have hqs : s ^ normV v = U * s := by
    rw [← hsn, ← pow_succ]; congr 1; omega
  have key : (τ'⁻¹ * τ) π / π - U = (t - s ^ normV v) / s := by
    rw [hrat, hqs]
    have e : τ'⁻¹ π = π * t / s := by rw [eq_div_iff hs0, hinv]
    rw [e]
    field_simp
  rw [key, map_div₀, hvs, div_one]
  exact hF

end GlobalTheory.TameRatio
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.exists_continuous_extension_adicCompletion (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (v : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1) :
    ∃ j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l, Continuous j ∧
      j.comp (algebraMap E (v.adicCompletion E)) = τ := by
  unfold _root_.Formalism.ConjugateSelfDual.Qbar at τ h ⊢

  let b := Module.finBasis ℚ E
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => τ (b i))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  have hmem : ∀ x, τ x ∈ K := by
    intro x

    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

  let g : WithVal (v.valuation E) →+* PadicAlgCl l := τ.comp (WithVal.equiv (v.valuation E)).toRingHom
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hπ1 : ‖τ π‖ < 1 := (h π).1 (by rw [hπ]; decide)
  have hπpos : 0 < ‖τ π‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hπ0)
  have hg : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    let y : WithVal (v.valuation E) := (WithVal.equiv (v.valuation E)).symm (π ^ n)
    have hy : Valued.v.restrict y ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero _).2 (pow_ne_zero n hπ0)
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 _ hy, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx ⊢
    have hz : v.valuation E (WithVal.equiv (v.valuation E) x) < v.valuation E (π ^ n) := hx
    have hπn : v.valuation E (π ^ n) ≠ 0 := by
      rw [map_pow, hπ]; exact pow_ne_zero _ (WithZero.coe_ne_zero)
    have hq : v.valuation E (WithVal.equiv (v.valuation E) x / π ^ n) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 hπn)).2 hz
    have hτq := (h _).1 hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (pow_pos hπpos n)] at hτq
    rw [dist_zero_right]
    exact lt_trans hτq hn
  let τ' : WithVal (v.valuation E) →+* K :=
    (τ.codRestrict K hmem).comp (WithVal.equiv (v.valuation E)).toRingHom
  have hτ' : Continuous τ' := continuous_induced_rng.2 hg
  let ext : (v.valuation E).Completion →+* K := UniformSpace.Completion.extensionHom τ' hτ'
  let φ : v.adicCompletion E →+* (v.valuation E).Completion :=
    { toFun := HeightOneSpectrum.adicCompletion.toCompletion
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Continuous φ := uniformContinuous_comap.continuous
  refine ⟨(algebraMap K (PadicAlgCl l)).comp (ext.comp φ), ?_, ?_⟩
  · exact continuous_subtype_val.comp (UniformSpace.Completion.continuous_extension.comp hφ)
  · ext x
    simp only [RingHom.comp_apply, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
    change ((ext ((WithVal.equiv (v.valuation E)).symm (algebraMap E E x) : (v.valuation E).Completion) : K) :
      PadicAlgCl l) = τ x
    rw [UniformSpace.Completion.extensionHom_coe]
    rfl

end GlobalTheory
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb {E : Type} [Field E] [NumberField E]
    {l : ℕ} [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (hj : Continuous j)
    (a : 𝓞 E) (ha : a ∈ v.asIdeal) :
    ‖j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a))‖ < 1 := by
  set x := algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a) with hx
  have hx1 : ‖x‖ < 1 := by
    rw [hx, Valued.toNormedField.norm_lt_one_iff]
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) v a
    erw [h]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact ha
  have hlim : Filter.Tendsto (fun n : ℕ => j x ^ n) Filter.atTop (nhds 0) := by
    have h0 := (hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1)
    simpa [Function.comp_def, map_pow] using h0
  by_contra hge
  push_neg at hge
  have hball : ∀ᶠ n : ℕ in Filter.atTop, ‖j x ^ n‖ < 1 :=
    (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hball.exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hge))


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (v v' : HeightOneSpectrum (𝓞 E))
      (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (j' : v'.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l),
      Continuous j → Continuous j' →
      j.comp (algebraMap E (v.adicCompletion E)) = j'.comp (algebraMap E (v'.adicCompletion E)) →
      v = v' := by
  intro E _ _ l _ v v' j j' hj hj' hcomp
  by_contra hne
  have hideal : v.asIdeal ≠ v'.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : v.asIdeal ⊔ v'.asIdeal = ⊤ := v.isMaximal.coprime_of_ne v'.isMaximal hideal
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have hna := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v j hj a ha
  have hnb := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v' j' hj' b hb
  have hb' : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) =
      j' (algebraMap E (v'.adicCompletion E) (algebraMap (𝓞 E) E b)) :=
    RingHom.congr_fun hcomp _
  rw [← hb'] at hnb
  have hsum : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)) +
      j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), ← map_add (f := _), hab, map_one, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)))
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)))
  rw [hsum, norm_one] at hle
  exact absurd (hle.trans_lt (max_lt hna hnb)) (lt_irrefl 1)

end GlobalTheory.HeckeGal
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.LadicPlace

theorem norm_embedding_integer_le_one {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (a : E)) := by
    have := (RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h
  by_contra hlt
  push_neg at hlt
  set y := τ (a : E)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i := by
    linear_combination hp0
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℤ (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) (p.coeff i)
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2

theorem exists_place_of_embedding :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l),
      ∃ v : HeightOneSpectrum (𝓞 E), ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1 := by
  intro E _ _ l hl τ
  have hle : ∀ a : 𝓞 E, ‖τ (a : E)‖ ≤ 1 := norm_embedding_integer_le_one τ
  let P : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, smul_eq_mul, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ a : 𝓞 E, a ∈ P ↔ ‖τ (algebraMap (𝓞 E) E a)‖ < 1 := fun a => Iff.rfl
  have hone : ∀ a : 𝓞 E, a ∉ P → ‖τ (algebraMap (𝓞 E) E a)‖ = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp (fun h => ha ((hP a).mpr h)))
  have hprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hP]; simp
    · intro a b hab
      by_contra hn
      rw [not_or] at hn
      rw [hP, map_mul, map_mul, norm_mul, hone a hn.1, hone b hn.2] at hab
      simp at hab
  have hlP : (l : 𝓞 E) ∈ P := by
    rw [hP, map_natCast, map_natCast]
    have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [h1, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.out.ne_zero (by exact_mod_cast hlP)
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hprime, hne⟩
  have key : ∀ x : E, v.valuation E x ≤ 1 → ∃ a s : 𝓞 E, s ∉ P ∧
      x * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    intro x hx
    obtain ⟨a, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨a, s, s.2, h⟩
  refine ⟨v, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, s, hs, h⟩ := key x hx.le
    have ha : a ∈ P := by
      have : v.valuation E (algebraMap (𝓞 E) E a) < 1 := by
        rw [← h, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (v.valuation_le_one s)) hx
      exact (v.valuation_lt_one_iff_mem a).mp this
    rw [hP, ← h, map_mul, norm_mul, hone s hs, mul_one] at ha
    exact ha
  · by_contra hn
    have hn' : 1 ≤ v.valuation E x := not_lt.mp hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hn'
    have hinv : v.valuation E x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
    obtain ⟨a, s, hs, h⟩ := key _ hinv
    have h2 : algebraMap (𝓞 E) E s = x * algebraMap (𝓞 E) E a := by
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    have h3 := hone s hs
    rw [h2, map_mul, norm_mul] at h3
    have h4 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hle a)
    exact absurd h3 h4.ne

end GlobalTheory.LadicPlace
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) {y : _root_.ReciprocityTheory.Aut.AL L} (hy : y ∈ _root_.ReciprocityTheory.Aut.ALint L) :
    SplitPlace.proj s y ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield L) := by
  have key : _root_.ReciprocityTheory.Aut.ALint L ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap (SplitPlace.proj s) := by
    unfold _root_.ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨a, ha, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact _root_.ReciprocityTheory.Aut.SplitPlace.split_le_one s b
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  exact key hy


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_loc_congr_one :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (N : ℕ) (x : _root_.Formalism.AUTREP.GAf L n),
    _root_.Formalism.L2.NG.Cong L n N x →
    ∀ i j, Valued.v (((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L))) := by
  intro L _ _ _ n s N x hx i j
  obtain ⟨y, hy, hxy⟩ := hx.2 i j
  have hentry : ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j
      = (N : s.v.adicCompletion (maximalRealSubfield L)) * SplitPlace.proj s y := by
    have h1 : SplitPlace.proj s ((1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    rw [← h1, ← map_natCast (SplitPlace.proj s) N, ← map_mul, ← hxy, map_sub]
    rfl
  rw [hentry, map_mul]
  have hle : Valued.v (SplitPlace.proj s y) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      (_root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral s hy)
  exact mul_le_of_le_one_right' hle

end GlobalTheory
end
