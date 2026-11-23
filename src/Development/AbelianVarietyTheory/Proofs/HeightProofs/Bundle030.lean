module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle012
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle011
import Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  change (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
    ((algebraMap F (InfiniteAdeleRing F) t) _) = σ t
  rw [InfiniteAdeleRing.algebraMap_apply]
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp


open Classical in
noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open IsLocalRing

section
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem mem_maximalIdeal_iff (x : la.adicCompletionIntegers K) :
    x ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      Valued.v (x : la.adicCompletion K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h1 : Valued.v (x : la.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K la).1 x.2
  constructor
  · intro h
    have h2 := lt_of_le_of_ne h1 h
    rcases eq_or_ne (Valued.v (x : la.adicCompletion K)) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
  · intro h h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega

theorem algebraMap_injective :
    Function.Injective (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) := by
  intro a b h
  have h1 := congrArg (fun x : la.adicCompletionIntegers K => (x : la.adicCompletion K)) h
  simp only [Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K (la.adicCompletion K)).injective h1)

theorem map_asIdeal :
    Ideal.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) la.asIdeal =
      maximalIdeal (la.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff, Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO, Formalism.MainNotions.Gaps.LocalGlobalPassage.val_alg,
      HeightOneSpectrum.valuation_of_algebraMap, la.intValuation_le_pow_iff_mem, pow_one]
    exact ha
  · intro x hx
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    obtain ⟨d, hd⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_factor (K := K) la hπ 1 x
      ((mem_maximalIdeal_iff la x).1 hx)
    rw [hd, pow_one]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem exists_sub_mem (x : la.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, x - algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈
      maximalIdeal (la.adicCompletionIntegers K) := by
  obtain ⟨r, hr⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.approx (K := K) la x 1
  exact ⟨r, (mem_maximalIdeal_iff la _).2 hr⟩

end

theorem isLocalization_rename {σ τ O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] (I : Ideal O₁)
    (e : σ ≃ τ) (Q : Ideal (MvPolynomial τ O₁)) [Q.IsPrime] (hQ : Q = Ideal.map MvPolynomial.C I)
    (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime] (hP : P = Ideal.map MvPolynomial.C I)
    [Algebra (MvPolynomial τ O₁) O₂] [IsLocalization.AtPrime O₂ Q] :
    letI : Algebra (MvPolynomial σ O₁) O₂ :=
      ((algebraMap (MvPolynomial τ O₁) O₂).comp
        (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom).toAlgebra
    IsLocalization.AtPrime O₂ P := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv Q.primeCompl O₂
    (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm
  have hmap : Ideal.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom P = Q := by
    rw [hP, hQ, Ideal.map_map]
    congr 1
    ext a
    simp
  have hmem : ∀ x, (MvPolynomial.renameEquiv O₁ e).toRingEquiv x ∈ Q ↔ x ∈ P := by
    intro x
    have hb := Ideal.comap_map_of_bijective (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom
      (MvPolynomial.renameEquiv O₁ e).toRingEquiv.bijective (I := P)
    rw [hmap] at hb
    rw [← hb]
    exact Iff.rfl
  have hM : Q.primeCompl.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      apply hy
      have := (hmem _).2 hx
      rwa [RingEquiv.apply_symm_apply] at this
    · intro hx
      exact ⟨_, fun hy => hx ((hmem x).1 hy), RingEquiv.symm_apply_apply _ _⟩
  rw [hM] at h
  exact h

theorem gaussRing_completion_rename :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (e : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) ∧ (∀ x : Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) ∧ (∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r)) ∧ (∀ a : B.KO, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.C a)) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ p, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X p)) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (e p)) := by
  intro D B P j X la N D' N' e
  letI alg : Algebra (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) :=
    ((algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) e).toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) p =
      algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (MvPolynomial.rename e p) := fun _ => rfl
  haveI hprime := Formalism.DV.GaussP.gaussIdeal_isPrime (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)
  haveI hloc : IsLocalization.AtPrime (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) :=
    isLocalization_rename (maximalIdeal (X.Ol la)) e (gI X la N) rfl
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl
  obtain ⟨-, f, hf, hflat, hloc', hmax, hres⟩ := GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
    (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la)
    (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
  have hinj₂ : Function.Injective (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (ReciprocityTheory.ChartRestriction.G.T0.laT D' N' la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at h1
    have h2 : p = 0 := by
      have h3 := hinj₂ (h1.symm.trans (map_zero _).symm)
      have h4 := MvPolynomial.rename_injective e e.injective (h3.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (h4.trans (map_zero _).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) s).mul_left_eq_zero.mp h
  letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) D' N' la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) D' N' la
  have hg : Function.Injective
      ((@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _).comp f) :=
    (IsFractionRing.injective (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)).comp hfinj
  let φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg
  have hφ : ∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r) := fun r =>
    IsFractionRing.lift_algebraMap (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg r
  have hφp : ∀ p : ReciprocityTheory.ChartRestriction.G.T0.OT B.KO D' N',
      φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _
        (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
          (MvPolynomial.rename e (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    intro p
    rw [← halg, ← hf, ← hφ, ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hloc', hmax, hres, hφ, ?_, ?_⟩
  · have key : (φ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
        (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')).comp MvPolynomial.C)) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h1 := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h1
      simp only [RingHom.comp_apply]
      rw [h1, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change _ = algebraMap (X.Kl la) (Kp X la N)
        (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun key a
  · intro p
    have h1 := hφp (MvPolynomial.X p)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h1
    exact h1

end GlobalTheory.GaussCompletion
end
