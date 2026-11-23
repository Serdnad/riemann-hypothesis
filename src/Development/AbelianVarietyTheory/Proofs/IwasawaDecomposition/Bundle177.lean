module

public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plc_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) (h : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have := v.isPrime
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  unfold Formalism.EigenvalueLevelCeiling.plc
  apply CharP.ringChar_of_prime_eq_zero h
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem absNorm_map (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_under_dvd (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl).toAddMonoidHom Ideal.quotientMap_injective

theorem of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.L2.DIV.DegOne v)
    {Q Q' : HeightOneSpectrum (𝓞 E)} (hne : Q ≠ Q')
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal) (hQ : Q.under (𝓞 F) = v) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, absNorm_map h2]
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  refine ⟨((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1, ?_⟩
  intro hmem
  have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
    Ideal.dvd_span_singleton.2 hqv
  have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_span_singleton.2 hmem
  rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
  rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
  · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  · have hle : I ≤ v.asIdeal := by
      rw [← hQ]
      exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hv.2
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
    exact Ideal.mul_mono_right hle

theorem under_eq_of_map_eq {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} {J : Ideal (𝓞 E)}
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * J) : Q.under (𝓞 F) = v := by
  refine (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top ?_)).symm
  exact Ideal.map_le_iff_le_comap.1 (hm ▸ Ideal.mul_le_left)

theorem map_eq_mul (h2 : Module.finrank F E = 2) {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hu : P'.under (𝓞 F) = P.under (𝓞 F)) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal * P'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_isCoprime (HeightOneSpectrum.isCoprime_of_ne P P' hne)]
    refine le_inf Ideal.map_comap_le ?_
    rw [← hu]
    exact Ideal.map_comap_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := absNorm_map h2 (P.under (𝓞 F)).asIdeal
  obtain ⟨a, ha⟩ := absNorm_under_dvd (F := F) P
  obtain ⟨b, hb⟩ := absNorm_under_dvd (F := F) P'
  rw [hu] at hb
  have h0 : Ideal.absNorm (P.under (𝓞 F)).asIdeal ≠ 0 := fun h => (P.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [hJ, map_mul, map_mul, ha, hb] at hN
  have h3 : (a * b) * Ideal.absNorm J = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 h0)
    rw [mul_one]
    refine Eq.trans ?_ hN
    ring
  rw [hJ, Ideal.absNorm_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h3), Ideal.mul_top]

theorem goodPl_iff (h2 : Module.finrank F E = 2) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.GoodPl E S (P.under (𝓞 F)) ↔ ((∃ P', P ≠ P' ∧ P'.under (𝓞 F) = P.under (𝓞 F)) ∧
      (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      Ideal.absNorm P.asIdeal ∉ S) := by
  constructor
  · rintro ⟨⟨Q, Q', hne, hm⟩, hv, hS⟩
    obtain ⟨P', hne', hm'⟩ : ∃ P', P ≠ P' ∧
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
      have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
        rw [← hm]
        exact Ideal.map_comap_le
      rcases P.isPrime.mul_le.1 hle with h | h
      · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q', hne, hm⟩
      · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q, hne.symm, by rw [hm, mul_comm]⟩
    obtain ⟨e, hn⟩ := of_split h2 hv hne' hm' rfl
    rw [plc_eq_absNorm _ hv.1] at hS
    rw [e]
    exact ⟨⟨P', hne', under_eq_of_map_eq (hm'.trans (mul_comm _ _))⟩, hv.1, hn, hS⟩
  · rintro ⟨⟨P', hne, hu⟩, hp, hn, hS⟩
    have e : Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
      ((Nat.dvd_prime hp).1 (absNorm_under_dvd P)).resolve_left fun h =>
        (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    refine ⟨⟨P, P', hne, map_eq_mul h2 hne hu⟩, ⟨e ▸ hp, fun h => hn ?_⟩, ?_⟩
    · rw [e] at h
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
      rw [map_natCast, Ideal.map_pow] at h3
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 h3
    · rw [plc_eq_absNorm _ (e ▸ hp), e]
      exact hS

end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP


open Classical in
theorem goodPl_under_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 H.E)), Formalism.L2.DIV.GoodPl H.E S (P.under (𝓞 H.F)) ↔ (IsSplitPl H P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2 ∧ Ideal.absNorm P.asIdeal ∉ S) := by
  intro R H S P
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [isSplitPl_iff]
  exact goodPl_iff hcm.rank S P

end GlobalTheory.Mem.GoodPlace
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ExtendLineBundleComponents

theorem exists_integral_components (X : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    ∃ (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) ∧ (∀ x, ∃ a, x ∈ V a) ∧
      ∀ a, IsIntegral (V a).toScheme ∧ CompactSpace (V a).toScheme := by
  have : IsNoetherian X := {}
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))
  have heq : ∀ (x : X) (Z W : Set X), Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
      x ∈ Z → x ∈ W → Z = W := by
    intro x Z W hZ hW hxZ hxW
    have := hX x
    exact GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
  have hopen : ∀ Z ∈ irreducibleComponents X, IsOpen Z := fun Z hZ => by
    have e : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
      · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
        exact hne (heq x W Z hW hZ hxW hxZ)
    rw [← isClosed_compl_iff, e]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have : IsReduced X := isReduced_of_isReduced_stalk _
  let V : irreducibleComponents X → X.Opens := fun Z => ⟨Z.1, hopen Z.1 Z.2⟩
  refine ⟨irreducibleComponents X, V, fun a b x ha hb => Subtype.ext (heq x a b a.2 b.2 ha hb),
    fun x => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩,
    fun a => ?_⟩
  have : IrreducibleSpace (V a).toScheme := Subtype.irreducibleSpace a.2.1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  exact isCompact_iff_compactSpace.mp (isClosed_of_mem_irreducibleComponents a.1 a.2).isCompact

theorem uniqueFactorizationMonoid_stalk_toScheme (X : Scheme.{0}) (U : X.Opens)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (y : U.toScheme) :
    UniqueFactorizationMonoid (U.toScheme.presheaf.stalk y) :=
  MulEquiv.uniqueFactorizationMonoid
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv (hX _)

end GlobalTheory.ExtendLineBundleComponents


open GlobalTheory.ExtendLineBundleComponents GlobalTheory.GenSpread in
theorem GlobalTheory.exists_lineBundle_extension_of_isDomain : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) →
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB →
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  intro X Y _ _ j hj hdom hufm L hL
  obtain ⟨A, V, hd, hc, hV⟩ := exists_integral_components X hdom
  have key : ∀ a, ∃ M : LB (V a).toScheme, M.IsLB ∧
      LBIso (M.pull (j ∣_ V a)) (L.pull (j ⁻¹ᵁ V a).ι) := by
    intro a
    have := (hV a).1
    have := (hV a).2
    obtain ⟨M, hM, φ, hφ⟩ := GlobalTheory.exists_lineBundle_extension (V a).toScheme (j ⁻¹ᵁ V a).toScheme
      (j ∣_ V a) inferInstance (uniqueFactorizationMonoid_stalk_toScheme X (V a) hufm)
      (L.pull (j ⁻¹ᵁ V a).ι) (pull_isLB hL _)
    exact ⟨M, hM, φ, hφ⟩
  choose M hM hML using key
  obtain ⟨N, hN, hNM⟩ := GlobalTheory.T.exists_lineBundle_glue_disjoint_cover X A V hd hc M hM
  refine ⟨N, hN, GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover Y A (fun a => j ⁻¹ᵁ V a) (fun a b y ha hb => hd a b _ ha hb)
    (fun y => hc (j y)) _ _ (pull_isLB hN j) hL fun a => ?_⟩
  have e1 : LBIso ((N.pull j).pull (j ⁻¹ᵁ V a).ι) ((N.pull (V a).ι).pull (j ∣_ V a)) :=
    LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hN _ rfl).symm (lbIso_pull_pull hN _ (morphismRestrict_ι j (V a)).symm)
  have e2 : LBIso ((N.pull (V a).ι).pull (j ∣_ V a)) ((M a).pull (j ∣_ V a)) :=
    lbIso_pullback (hNM a) _
  exact LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hL _) e1
    (LBIso.trans (pull_isLB (pull_isLB hN _) _) (pull_isLB (hM a) _) (pull_isLB hL _) e2 (hML a))
end
end
