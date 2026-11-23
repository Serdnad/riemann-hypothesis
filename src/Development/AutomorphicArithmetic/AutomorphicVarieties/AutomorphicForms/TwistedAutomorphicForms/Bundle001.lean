module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

private noncomputable def UpperTheory.V.Af.Tw.compAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def UpperTheory.V.Af.Tw.infPart (K : Type) [Field K] [NumberField K] :
    AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem UpperTheory.V.Af.Tw.loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_same _ _ _

private theorem UpperTheory.V.Af.Tw.loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

theorem UpperTheory.V.Af.Tw.locProd :
    UpperTheory.V.Af.Tw.LocProd := by
  unfold UpperTheory.V.Af.Tw.LocProd
  intro F L _ _ _ _ _ v x
  classical
  let y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    Units.map (finiteCompletionMap F L w).toMonoidHom
      (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))
  have hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w)) :=
    fun w => rfl
  have hmem : ∀ w : HeightOneSpectrum (𝓞 L),
      w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v :=
    fun w => by
      unfold aboveF
      simp
  have key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b →
      (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b :=
    fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod]
    apply key
    · rw [map_prod]
      have h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1 := fun w => rfl
      simp only [h1, Finset.prod_const_one]
      show infiniteAdeleMap F L 1 = 1
      exact map_one _
    · intro w'
      rw [map_prod]
      show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) =
        ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'
      by_cases hw' : HeightOneSpectrum.under (𝓞 F) w' = v
      · rw [Finset.prod_eq_single w']
        · rw [UpperTheory.V.Af.Tw.loc_same, hy]
        · intro b _ hb
          exact UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _
        · intro h
          exact absurd ((hmem w').mpr hw') h
      · rw [UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]
        intro b hb
        exact UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _
  · intro hunr hx w hw
    subst hw
    unfold IsUnifAt at hx ⊢
    rw [hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]
    exact hx
end

section

open NumberField IsDedekindDomain in
theorem UpperTheory.V.Af.Tw.kron :
    UpperTheory.V.Af.Tw.Kron := by
  intro K _ _
  refine ⟨NumberField.Units.torsionOrder K, ?_, ?_⟩
  · intro l hl hno
    haveI : Fact (Nat.Prime l) := ⟨hl⟩
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd
    have h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact IsPrimitiveRoot.orderOf _
    have h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l := IsPrimitiveRoot.coe_units_iff.mpr h1
    have h3 := h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)
    exact hno ⟨_, h3⟩
  · intro y hy hnorm
    have hy' : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by
      rw [← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]
      exact le_of_eq (hy' v))
    have hI : IsIntegral ℤ (y : K) := by
      have := NumberField.RingOfIntegers.isIntegral_coe r
      rwa [hr] at this
    obtain ⟨m, hm, hym⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm
    have hrm : r ^ m = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_pow, hr, hym, map_one]
    let u : (𝓞 K)ˣ := Units.ofPowEqOne r m hrm hm.ne'
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨m, hm, Units.ext (by simp [u, hrm])⟩
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]
    have hu' := congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu'
    change (u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'
    have hur : (u : 𝓞 K) = r := Units.val_ofPowEqOne r m hrm hm.ne'
    rw [hur] at hu'
    rw [hu', map_one]
end

section

open NumberField IsDedekindDomain Neutral.B1

theorem UpperTheory.V.Af.Tw.awayTriv :
    UpperTheory.V.Af.Tw.AwayTriv := by
  intro F B _ _ _ _ _ _ N S hN hinf hS b hbS hbin
  classical
  have k1 : (b : AdeleRing (𝓞 F) F).1 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.mul_inv b)
  have k2 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 * (b : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul b)
  have k3 : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv b)
  have k4 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul b)
  let binf : Ideles F := ⟨((b : AdeleRing (𝓞 F) F).1, 1), (((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1, 1),
    Prod.ext k1 (mul_one 1), Prod.ext k2 (mul_one 1)⟩
  let bfin : Ideles F := ⟨(1, (b : AdeleRing (𝓞 F) F).2), (1, ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2),
    Prod.ext (mul_one 1) k3, Prod.ext (mul_one 1) k4⟩
  have hb : b = binf * bfin := by
    apply Units.ext
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  have hfin2 : (↑bfin : AdeleRing (𝓞 F) F).2 = (↑b : AdeleRing (𝓞 F) F).2 := rfl
  have h1 : N binf = 1 := hinf binf rfl
  have h2 : N bfin = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local N hN bfin rfl ?_
    intro v
    by_cases hv : v ∈ S
    · have hone : Units.map (GlobalTheory.Mem.LocTriv.ev v) bfin = 1 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_one]
        change (↑bfin : AdeleRing (𝓞 F) F).2 v = 1
        rw [hfin2]
        exact hbin v hv
      rw [hone, map_one, map_one]
    · apply hS v hv
      change Valued.v ((↑bfin : AdeleRing (𝓞 F) F).2 v) = 1
      rw [hfin2]
      exact hbS v hv
  rw [hb, map_mul, h1, h2, one_mul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Tw

private theorem int_mem {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω x ∈ A := by
  have hi : IsIntegral ℤ (algebraMap L Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [← hy]
  exact y.2

private theorem exists_above {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ IsPlaceOver A w := by
  let φ : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (int_mem A)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap φ :=
    fun x => (A.valuation_lt_one_iff (φ x)).symm
  have hu : ((IsLocalRing.maximalIdeal A).comap φ).under (𝓞 F) = v.asIdeal := by
    ext x
    rw [← hA x, IsScalarTower.algebraMap_apply F L Ω]
    exact (hP (algebraMap (𝓞 F) (𝓞 L) x)).symm
  haveI : ((IsLocalRing.maximalIdeal A).comap φ).LiesOver v.asIdeal := ⟨hu.symm⟩
  exact ⟨⟨(IsLocalRing.maximalIdeal A).comap φ, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩,
    HeightOneSpectrum.ext hu, hP⟩

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [show normV w = Ideal.absNorm w.asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply],
      show normV (w.under (𝓞 K)) = Ideal.absNorm (w.under (𝓞 K)).asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := Nat.card_eq_fintype_card
  rw [e]
  by_contra hlt
  refine Polynomial.X_pow_sub_X_ne_zero (R := 𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [Polynomial.natDegree_X_pow_sub_X hq, Finset.card_univ]
    exact not_le.1 hlt

private theorem two_of_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hs : ∑ i, f i = 2) (a : ι)
    (ha : f a = 1) : ∃ b, b ≠ a ∧ f b = 1 ∧ ∀ c, c = a ∨ c = b := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hs
  have h1 : ∑ i ∈ Finset.univ.erase a, f i = 1 := by omega
  obtain ⟨b, hb⟩ : (Finset.univ.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at h1
    simp at h1
  rw [← Finset.add_sum_erase _ _ hb] at h1
  have := hf b
  refine ⟨b, Finset.ne_of_mem_erase hb, by omega, fun c => ?_⟩
  by_contra hc
  rw [not_or] at hc
  have h2 : f c ≤ ∑ i ∈ (Finset.univ.erase a).erase b, f i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hc.1, hc.2])
  have := hf c
  omega

theorem UpperTheory.V.Af.Tw.frobSplit :
    UpperTheory.V.Af.Tw.FrobSplit := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hur hA s hs
  classical
  obtain ⟨w, hwv, hw⟩ := exists_above (L := L) hA
  have hq : 1 < normV v := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hle : normV w ≤ normV v := by
    refine normV_le w hq fun x => ?_
    rw [← hw]
    have h3 := hs.2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    have h4 : resG F L Ω s (algebraMap L Ω x) = algebraMap L Ω x := s.commutes x
    rw [h4] at h3
    simpa using h3
  haveI := v.isMaximal
  haveI := w.isPrime
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    rw [normV_under' (K := F) w, hwv] at hle
    have h5 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos _ _
    have h6 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 1 :=
      (Nat.pow_le_pow_iff_right hq).1 (by rwa [pow_one])
    omega
  have hl : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v → u.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) :=
    fun u hu => ⟨u.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]
    exact hur w hwv
  haveI := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L, h2] at hsum
  obtain ⟨⟨Q, hQ, hQv⟩, hne, h1, hall⟩ := two_of_sum _
    (fun P => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)) hsum
    ⟨w.asIdeal, hl w hwv⟩ (by simp only [he, hf])
  let w' : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw' : w'.under (𝓞 F) = v := HeightOneSpectrum.ext hQv.over.symm
  have hf' : w'.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨w, w', fun h => hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), fun u => ⟨fun hu => ?_, ?_⟩,
    hw, ?_, ?_⟩
  · rcases hall ⟨u.asIdeal, hl u hu⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro (rfl | rfl)
    exacts [hwv, hw']
  · rw [normV_under' (K := F) w, hwv, hf, pow_one]
  · rw [normV_under' (K := F) w', hw', hf', pow_one]
end

section

open NumberField IsDedekindDomain

theorem UpperTheory.V.Af.Tw.unrAE :
    UpperTheory.V.Af.Tw.UnrAE := by
  unfold UpperTheory.V.Af.Tw.UnrAE
  intro F L _ _ _ _ _
  letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  have hD0 : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 L)
  have hfin := Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 F) (𝓞 L)) hD0
  rw [Filter.eventually_cofinite]
  refine (hfin.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  unfold UpperTheory.V.Af.Tw.Unr at hv
  push_neg at hv
  obtain ⟨w, rfl, he⟩ := hv
  refine ⟨w, ?_, rfl⟩
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal := Ideal.map_comap_le
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal ^ 2 := by
    by_contra h
    exact he (Ideal.ramificationIdx'_spec (by rwa [pow_one]) h)
  haveI := (HeightOneSpectrum.under (𝓞 F) w).isMaximal
  have hdvd := pow_sub_one_dvd_differentIdeal (A := 𝓞 F) (P := w.asIdeal) (e := 2)
    (hp := (HeightOneSpectrum.under (𝓞 F) w).ne_bot) (hP := Ideal.dvd_iff_le.mpr h2)
  simpa using hdvd
end

section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.Tw.descend :
    UpperTheory.V.Af.Tw.Descend := by
  unfold UpperTheory.V.Af.Tw.Descend
  intro F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin
  have hq := hart.quot
  have hker : art.ker ≤ ψ.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · refine sup_le ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hdiag k
      · intro z hz
        unfold infConn at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact hfin _ rfl
    · exact isClosed_singleton.preimage hψc
  let fC : C(Ideles F, Gab F Ω) := ⟨art, hq.continuous⟩
  let gC : C(Ideles F, B) := ⟨ψ, hψc⟩
  have hfact : Function.FactorsThrough gC fC := by
    intro a b hab
    have hab' : a / b ∈ art.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.2 hab
    have := hker hab'
    rw [MonoidHom.mem_ker, map_div] at this
    exact div_eq_one.1 this
  have hQ : Topology.IsQuotientMap fC := hq.isQuotientMap
  let κC := hQ.lift gC hfact
  have hκ : ∀ x, κC (art x) = ψ x := fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x
  let κ₀ : Gab F Ω →* B := MonoidHom.mk' κC (by
    intro a b
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    rw [← map_mul, hκ, hκ, hκ, map_mul])
  refine ⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩
  · exact κC.continuous.comp (by
      first
        | exact QuotientGroup.continuous_mk
        | exact continuous_quot_mk)
  · intro x σ h
    show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x
    rw [← h, hκ]
end

section

open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal

theorem UpperTheory.V.Af.Tw.splitIso :
    UpperTheory.V.Af.Tw.SplitIso := by
  intro F L _ _ _ _ _ h2 w w' hne hunder
  classical
  set v := HeightOneSpectrum.under (𝓞 F) w with hv
  haveI hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  haveI hw' : w'.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩
  have hsum := sum_ramificationIdx_mul_inertiaDeg L v
  rw [h2] at hsum
  have hpos : ∀ u : PlacesOver L v, 1 ≤ (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F) := fun u =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  let a : PlacesOver L v := ⟨w, hw⟩
  let b : PlacesOver L v := ⟨w', hw'⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h).symm
  have hle := Finset.add_le_sum (s := Finset.univ)
    (f := fun u : PlacesOver L v => (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hle2 := hle.trans_eq hsum
  have ha1 := hpos a
  have hb1 := hpos b
  have h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    change _ + _ ≤ 2 at hle2
    change 1 ≤ w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) at ha1
    change 1 ≤ w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) at hb1
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) +
      w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle2
    omega
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hfin : Module.finrank (v.adicCompletion F) (w.adicCompletion L) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w, h1]
  have hbij : Function.Bijective (completionMap v w) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  let e := RingEquiv.ofBijective (completionMap v w) hbij
  refine ⟨(e.symm : w.adicCompletion L →+* v.adicCompletion F), ?_, ?_⟩
  · refine GlobalTheory.DenseCompl.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective L w) _ ?_
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    have hx : (e.symm : w.adicCompletion L →+* v.adicCompletion F) (completionMap v w x) = x :=
      e.symm_apply_apply x
    rw [hx, valued_completionMap, he, pow_one]
  · intro x
    exact e.symm_apply_apply x
end

section

open ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Af.Tw.resOpen :
    UpperTheory.V.Af.Tw.ResOpen := by
  unfold UpperTheory.V.Af.Tw.ResOpen
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _
  have hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω := rfl
  obtain ⟨hemb, hop, hidx⟩ := UpperTheory.V.Base.galEmbTop F L Ω
  rw [hre]
  refine ⟨⟨hemb, ?_⟩, ?_⟩
  · rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hop
  · rw [UpperTheory.V.Base.range_galEmb]
    exact hidx
end
