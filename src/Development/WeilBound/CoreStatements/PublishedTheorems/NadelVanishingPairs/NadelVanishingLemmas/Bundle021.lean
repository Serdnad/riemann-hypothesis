module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle015
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle012
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Domin

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

end GlobalTheory.Domin

private theorem exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ringKrullDim R ≤ 1) (a p : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hp : p ≠ 0) :
    ∃ N : ℕ, ∃ b : R, a ^ N = p * b := by
  by_cases hpu : IsUnit p
  · exact ⟨0, ↑hpu.unit⁻¹, by simp⟩
  · haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast hR)
    have hmax : ∀ P : Ideal R, P.IsPrime → p ∈ P → P = IsLocalRing.maximalIdeal R := by
      intro P hP hpP
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP⟩ : PrimeSpectrum R) with h | h
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simp at h'
        rw [h'] at hpP
        exact absurd ((Submodule.mem_bot R).1 hpP) hp
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simpa using h'
    have hrad : a ∈ (Ideal.span {p}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hPp, hP⟩
      rw [hmax P hP (hPp (Ideal.mem_span_singleton_self p))]
      exact ha
    have hle : Ideal.span {a} ≤ (Ideal.span {p}).radical := (Ideal.span_singleton_le_iff_mem _).2 hrad
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (Submodule.fg_span_singleton a)
    have : a ^ N ∈ Ideal.span {p} := hN (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨N, b, by rw [← hb, mul_comm]⟩

private theorem exists_nsmul_sub_regularAt_of_supp_le {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D E : CartierDiv X) (hE : E.Eff)
    (hsupp : D.supp ≤ E.supp) (z : X) (hz : Order.coheight z = 1) :
    ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → (c • E - D).RegularAt z 1 := by
  obtain ⟨gD, hgD⟩ := D.exists_isEqn z
  obtain ⟨gE, hgE⟩ := E.exists_isEqn z
  have hEq : ∀ c : ℕ, (c • E - D).IsEqn z (gE ^ c / gD) := fun c => (hgE.nsmul c).sub hgD
  obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hE z gE hgE
  suffices key : ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → RegAt z ((gE ^ c / gD : (X.functionField)ˣ) : X.functionField) by
    obtain ⟨c0, h0, hc0⟩ := key
    exact ⟨c0, h0, fun c hc => (hEq c).regularAt_iff.2 (by rw [one_mul]; exact hc0 c hc)⟩
  by_cases hzD : z ∈ D.supp
  · have ha' : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hau
      exact (hgE.mem_supp_iff.1 (hsupp hzD)) ⟨a, hau, ha⟩
    obtain ⟨⟨q, ⟨p, hp⟩⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk z))
      ((gD⁻¹ : (X.functionField)ˣ) : X.functionField)
    dsimp only at hpq
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1 := (ringKrullDim_stalk_le_one_iff z).2 hz.le
    obtain ⟨N, b, hab⟩ := exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one hdim a p ha' hp0
    refine ⟨N, fun h => absurd hzD h, fun c hc => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    refine ⟨b * q * a ^ d, ?_⟩
    have hpK : algebraMap (X.presheaf.stalk z) X.functionField p ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, div_eq_mul_inv,
      ← Units.val_inv_eq_inv_val, ← hpq, IsFractionRing.mk'_eq_div, ← map_pow, pow_add, hab]
    simp only [map_mul]
    field_simp
  · have hu : UnitAt z (gD : X.functionField) := by
      by_contra h
      exact hzD (hgD.mem_supp_iff.2 h)
    obtain ⟨u, hu, hugD⟩ := hu
    refine ⟨0, fun _ => rfl, fun c _ => ⟨a ^ c * ↑hu.unit⁻¹, ?_⟩⟩
    have h1 : algebraMap (X.presheaf.stalk z) X.functionField u *
        algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹) = 1 := by
      rw [← map_mul]; simp
    have hne := left_ne_zero_of_mul_eq_one h1
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, ← hugD, map_mul, map_pow,
      eq_div_iff hne, mul_assoc, mul_comm (algebraMap _ _ _) (algebraMap _ _ u), h1, mul_one]

private theorem eq_of_mem_supp_specializes_coheight_one {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (y z : X) (hy : y ∈ D.supp) (h : y ⤳ z)
    (hz : Order.coheight z = 1) : y = z := by
  by_contra hne
  have hzy : z ≤ y := h
  have hnot : ¬ y ≤ z := fun h' => hne (h.antisymm h').eq
  have hlt : z < y := lt_of_le_not_ge hzy hnot
  have hfin : Order.coheight y < ⊤ := lt_of_le_of_lt (Order.coheight_anti hzy) (by simp [hz])
  have h1 := Order.coheight_strictAnti hlt hfin
  rw [hz] at h1
  have h0 : Order.coheight y = 0 := ENat.lt_one_iff_eq_zero.1 h1
  have hη : genericPoint X ⤳ y := genericPoint_specializes y
  by_cases hyη : genericPoint X ≤ y
  · have hyeq : y = genericPoint X := (Specializes.antisymm hyη hη).eq
    exact D.genericPoint_notMem_supp (hyeq ▸ hy)
  · have hlt2 : y < genericPoint X := lt_of_le_not_ge hη hyη
    have h2 := Order.coheight_strictAnti hlt2 (lt_of_le_of_lt (Order.coheight_anti (show y ≤ genericPoint X from hη)) (by simp [h0]))
    rw [h0] at h2
    exact absurd h2 (by simp)

private theorem finite_coheight_one_inter_supp {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (D : CartierDiv X) :
    {z : X | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨S, hSirr, hSeq⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible D.supp
  refine Set.Finite.subset (S.finite_toSet.biUnion fun k _ => (show {x : X | IsGenericPoint x (k : Set X)}.Subsingleton
    from fun x hx y hy => hx.eq hy).finite) ?_
  rintro z ⟨hz, hzD⟩
  have hzS : z ∈ (S.sup id : TopologicalSpace.Closeds X) := by rw [← hSeq]; exact hzD
  have hex : z ∈ (S.sup id : TopologicalSpace.Closeds X) → ∃ k ∈ S, z ∈ k :=
    Finset.sup_induction (p := fun C : TopologicalSpace.Closeds X => z ∈ C → ∃ k ∈ S, z ∈ k)
      (fun h => by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h; exact absurd h (Set.notMem_empty z))
      (fun a ha b hb h => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup] at h
        rcases h with h | h
        exacts [ha h, hb h])
      (fun k hk h => ⟨k, hk, h⟩)
  obtain ⟨k, hkS, hzk⟩ := hex hzS
  have hirr := hSirr ⟨k, hkS⟩
  have ht : IsGenericPoint hirr.genericPoint (k : Set X) := hirr.isGenericPoint_genericPoint k.isClosed
  have hkD : (k : Set X) ⊆ D.supp := by
    have : k ≤ D.supp := by rw [hSeq]; exact Finset.le_sup (f := id) hkS
    exact this
  have hteq := eq_of_mem_supp_specializes_coheight_one D _ z (hkD ht.mem) (ht.specializes hzk) hz
  exact Set.mem_biUnion hkS (show IsGenericPoint z (k : Set X) from hteq ▸ ht)


open GlobalTheory.Domin in
theorem GlobalTheory.effDominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  intro X _ _ _ _ D E hE hsupp
  classical
  have hfin := finite_coheight_one_inter_supp D
  let c0 : X → ℕ := fun z =>
    if hz : Order.coheight z = 1 then Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) else 0
  refine ⟨hfin.toFinset.sup c0, ?_⟩
  have hreg : ∀ z : X, Order.coheight z = 1 → (hfin.toFinset.sup c0 • E - D).RegularAt z 1 := by
    intro z hz
    have hspec := Classical.choose_spec (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz)
    apply hspec.2
    have hc0 : c0 z = Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) := by simp [c0, hz]
    rw [← hc0]
    by_cases hzD : z ∈ D.supp
    · exact Finset.le_sup (f := c0) (hfin.mem_toFinset.2 ⟨hz, hzD⟩)
    · rw [hc0, hspec.1 hzD]
      exact Nat.zero_le _
  intro x
  obtain ⟨g, hg⟩ := (hfin.toFinset.sup c0 • E - D).exists_isEqn x
  rw [hg.regularAt_iff, one_mul]
  apply regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz := hU z (hzx.mem_open U.isOpen hxU)
  have h1 := hgz.regularAt_iff.1 (hreg z hz)
  rwa [one_mul] at h1
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem spanForms_eq_bot_of_isCoord {K : Type} [Field K] {n : ℕ} {x : Fin n → Kˣ} (hx : IsCoord x)
    (M : Set K) (H : Set Ω[K⁄ℤ]) {a : ℕ} (ha : n < a) : spanForms M H a = ⊥ := by
  let bs : Module.Basis (Fin n) K Ω[K⁄ℤ] := Module.Basis.mk hx.1 hx.2.ge
  haveI : Module.Finite K Ω[K⁄ℤ] := Module.Finite.of_basis bs
  have hfr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  refine eq_bot_iff.2 ((AddSubgroup.closure_le _).2 ?_)
  rintro η ⟨c, -, v, -, rfl⟩
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ v hv, smul_zero]
  exact AddSubgroup.zero_mem _

theorem logAt_eq_bot_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (Z : Set X) (G : CartierDiv X) {a : ℕ} (ha : n < a) (y : X) :
    logAt Z G a y = ⊥ := by
  have hg : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, -⟩ := (Opens.mem_iSup).1 hg
  exact spanForms_eq_bot_of_isCoord ((𝒜.chart i).chart _ (𝒜.gen i)).coord _ _ ha

theorem cechFam_eq_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) :
    cechFam 𝒜 G a = cechFam 𝒜 G (n + 1) := by
  funext s
  simp only [cechFam, logSec, latSec, logAt_eq_bot_of_lt 𝒜 _ G ha,
    logAt_eq_bot_of_lt 𝒜 _ G (Nat.lt_succ_self n)]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem exists_cechZero_cechFam_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  intro k _ X _ f hf C _ E n ι _ _ 𝒜 H B R hH
  haveI : IsProper f := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  haveI : X.IsSeparated := by
    constructor
    rw [show terminal.from X = f ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  letI := algebraΓOfHom f
  have key : ∀ (j : Fin B) (a : Fin (n + 2)), ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ b : ℕ, 0 < b →
      DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
    intro j a
    obtain ⟨F, ⟨lm⟩⟩ := GlobalTheory.T.exists_lattice_model X (logAt (suppAll E) (R j) a)
      (fun y g v hg hv => logAt_smul_mem X _ _ _ y g v hg hv)
    haveI : IsFiniteQC F := GlobalTheory.T.log_forms_lattice_finite X E 𝒜 (R j) a F lm
    have hev := eventually_subsingleton_coh_twistZ_of_isProjOver (f := f) (fun _ => rfl) F hf hH
    obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
    refine ⟨q₀, fun q hq b hb => ?_⟩
    obtain ⟨lm'⟩ := nonempty_latModel_twist X (logAt (suppAll E) (R j) a)
      (logAt (suppAll E) (q • H + R j) a) F (q • H) (toLB (q • H)) _ (presents_toLB _)
      (fun y g v hD => by rw [add_comm]; exact logtwist X _ _ _ _ y g v hD) lm
    haveI : IsFiniteQC (twist F (toLB (q • H))) := isFiniteQC_twist (isLB_toLB _)
    have hc := GlobalTheory.T.cech_lattice_cohomology_vanish X (logAt (suppAll E) (q • H + R j) a) (twist F (toLB (q • H))) 𝒜.U lm'
      𝒜.affine 𝒜.gen 𝒜.cover b hb
    refine hc.2 ?_
    haveI hs : Subsingleton (coh (twist F (lbZPow (toLB H) (q : ℤ))) b) := hq₀ q hq b hb
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F (isLB_toLB (q • H)) (isLB_lbZPow (isLB_toLB H) q)
      (by rw [cls_lbZPow (isLB_toLB H), ← toPic_apply, ← toPic_apply, map_nsmul, natCast_zsmul])
    exact (cohOn.mapIso k ⊤ b e).injective.subsingleton
  choose q₁ hq₁ using key
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun p : Fin B × Fin (n + 2) => q₁ p.1 p.2)
  refine ⟨Q, fun q hq j a b hb => ?_⟩
  by_cases ha : a ≤ n + 1
  · exact hq₁ j ⟨a, by omega⟩ q ((hQ (j, ⟨a, by omega⟩)).trans hq) b hb
  · rw [cechFam_eq_of_lt 𝒜 _ (by omega : n < a)]
    exact hq₁ j ⟨n + 1, by omega⟩ q ((hQ (j, ⟨n + 1, by omega⟩)).trans hq) b hb

end GlobalTheory.LogDR
end
