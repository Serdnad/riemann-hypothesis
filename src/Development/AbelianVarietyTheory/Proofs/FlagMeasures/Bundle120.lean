module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.NormOneCount

theorem le_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 := hp.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hP : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, Nat.add_sub_cancel]
    generalize (q + 1) ^ k = P at hP ⊢
    have hPP : P ≤ P ^ 2 := by nlinarith
    refine ⟨?_, fun ho => ?_⟩
    · have h1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * (2 * q ^ 2) := Nat.mul_le_mul hPP h1
        _ = _ := by ring
    · have ho' : Odd (q + 1) := (Nat.odd_mul.1 ho).2
      have hq2 : 2 ≤ q := by
        obtain ⟨m, hm⟩ := ho'
        omega
      have h1 : q + 1 ≤ q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * q ^ 2 := Nat.mul_le_mul hPP h1
        _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    refine ⟨?_, fun ho => ?_⟩
    · rcases Nat.even_or_odd a with hea | hoa
      · have hob : Odd b := by
          rcases Nat.even_or_odd b with heb | hob
          · have := Nat.dvd_gcd hea.two_dvd heb.two_dvd
            rw [hab.gcd_eq_one] at this
            omega
          · exact hob
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hob)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hoa) ihb.1
          _ = _ := by ring
    · obtain ⟨h1, h2⟩ := Nat.odd_mul.1 ho
      calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)
        _ = _ := by ring

theorem card_torsion_le (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K)) := hg ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K)) :=
    h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective
  have h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K)) :=
    IsPrimitiveRoot.coe_units_iff.2 h2
  have h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K)) :=
    h3.map_of_injective (RingOfIntegers.coe_injective)
  have hpos : 0 < Nat.card (Units.torsion K) := Nat.card_pos
  have h5 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4
    (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self] at h5
  exact (le_totient_sq _).1.trans (by gcongr)

variable {K : Type} [Field K] [NumberField K]

theorem isIntegral_of_mul_mem {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by
  have hne : ipow 𝔞 1 ≠ ⊥ := by
    unfold ipow
    rw [zpow_one]
    intro h0
    exact (FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  have hfg : (ipow 𝔞 1).FG := by
    unfold ipow
    exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : IsIntegral (𝓞 K) u :=
    isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)
  exact isIntegral_trans u h1

theorem exists_torsion [StarRing K] (hK : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    {𝔞 𝔞' : Ideal (𝓞 K)} (h : 𝔞' ≠ ⊥) {c d : K} (hc : c * star c = 1) (hd : d * star d = 1)
    (h1 : ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) (h2 : ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) :
    ∃ ζ : Units.torsion K, c = algebraMap (𝓞 K) K ((ζ : (𝓞 K)ˣ) : 𝓞 K) * d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have i1 : IsIntegral ℤ (c / d) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht
  have i2 : IsIntegral ℤ (d / c) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d := ⟨⟨c / d, i1⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c := ⟨⟨d / c, i2⟩, rfl⟩
  have hm : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, ha, hb]
    field_simp
  have hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1 := fun φ e he => by
    have h3 := congrArg (fun z => ‖φ z‖) he
    simp only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3
    nlinarith [norm_nonneg (φ e)]
  refine ⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩
  · show w (algebraMap (𝓞 K) K a) = 1
    rw [ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]
  · show c = algebraMap (𝓞 K) K a * d
    rw [ha]
    field_simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ x : ℝ, 1 ≤ x → ((({c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * x ^ (2 * (2 + cf K))) := by
  intro K _ _ _ hK x hx
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K x hx
  set A := {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} with hA
  let c0 : Ideal (𝓞 K) × Ideal (𝓞 K) → K := fun p =>
    if h : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow p.1 1 ↔ t ∈ ipow p.2 1 then h.choose else 0
  let g : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Units.torsion K → K := fun q =>
    algebraMap (𝓞 K) K ((q.2 : (𝓞 K)ˣ) : 𝓞 K) * c0 q.1
  have hB : ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))).Finite :=
    (hfin.prod hfin).prod Set.finite_univ
  have hsub : {c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧
      (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1} ⊆
      g '' ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))) := by
    rintro c ⟨hc, 𝔞, 𝔞', h1, h2, h3, h4, h5⟩
    have hex : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := ⟨c, hc, h5⟩
    obtain ⟨ζ, hζ⟩ := exists_torsion hK.2.1 h2 hc hex.choose_spec.1 h5 hex.choose_spec.2
    refine ⟨((𝔞, 𝔞'), ζ), ⟨⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, trivial⟩, ?_⟩
    simp only [g, c0, dif_pos hex]
    exact hζ.symm
  have henc := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  rw [← hB.cast_ncard_eq, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ] at henc
  refine (ENat.toENNReal_le.2 henc).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hw : (Nat.card (Units.torsion K) : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 := by
    have h1 := card_torsion_le K
    rw [hd] at h1
    have h2 : (Nat.card (Units.torsion K) : ℝ) ≤ 2 * (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) ^ 2 := by
      exact_mod_cast h1
    linarith
  have hA' : (A.ncard : ℝ) ≤ x ^ (2 + cf K) :=
    hle.trans (Real.rpow_le_rpow_of_exponent_le hx (by unfold cf; linarith))
  have hx0 : 0 < x := by linarith
  push_cast
  calc (A.ncard : ℝ) * A.ncard * Nat.card (Units.torsion K)
      ≤ x ^ (2 + cf K) * x ^ (2 + cf K) * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hx0, two_mul (2 + cf K)]; ring

end GlobalTheory.DegCnt.NormOneCount
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeRightInv

open Topology

theorem map_mul_right_of_conj_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : ν B ≠ 0) (ht : ν B ≠ ⊤) (l : G) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    ν.map (fun g => g * l) = ν := by
  have hU : (interior B).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hB⟩
  have hmeas : Measurable (fun g : G => g * l) := measurable_mul_const l
  haveI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩

  have hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B) :=
    isOpen_interior.preimage (continuous_mul_const l⁻¹)
  have hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B) := by
    rw [Measure.map_apply hmeas hVo.measurableSet]
    congr 1
    ext g
    simp [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo
      ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩
      (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩

  obtain ⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  obtain ⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩

  have hBB : ν.map (fun g => g * l) B = ν B := by
    rw [Measure.map_apply hmeas hBm,
      show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]
    exact measure_preimage_mul ν l B
  have hpos : (Measure.haar : Measure G) B ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hB).ne'
  have hc₁ : (c₁ : ENNReal) ≠ 0 := by
    rintro h
    apply h0
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]
  have hfin : (Measure.haar : Measure G) B ≠ ⊤ := by
    intro h
    apply ht
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]
  rw [e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin] at hBB
  rw [e₂, e₁, ENNReal.coe_injective hBB]

theorem map_mul_right_of_conj_nhds_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) (hM : IsClosed (M : Set G)) (μ : Measure G) (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) (l : G) (hlM : l ∈ M) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    μ.map (fun g => g * l) = μ := by
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))
  haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))
  have emb : MeasurableEmbedding (Subtype.val : M → G) :=
    MeasurableEmbedding.subtype_coe hM.measurableSet

  set ν : Measure M := μ.comap Subtype.val with hν
  have hμν : ν.map Subtype.val = μ := by
    rw [hν, emb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  haveI : ν.IsMulLeftInvariant := ⟨fun s => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]
    have himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) =
        (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨s * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ M := by
          have : x = (s : G)⁻¹ * y := by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact M.mul_mem (M.inv_mem s.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        show s * (⟨x, hx⟩ : M) ∈ A
        rw [show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA),
      hinv s s.2]⟩
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by
    conv_rhs => rw [← hμν]
    rw [Measure.map_apply measurable_subtype_coe hBm]
  have key := map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B)
    (hBm.preimage measurable_subtype_coe)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hB)
    (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)
  rw [← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe,
    show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]

theorem hs_eq_re_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs X = (trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_mul_mul_conjTranspose_of_unitary {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * M * Lᴴ) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc trace (L * M * Lᴴ * (L * (Mᴴ * Lᴴ))) = trace (L * (M * Mᴴ) * Lᴴ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
    _ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _
    _ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem hs_conj {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * X - 1) = Formalism.REAL.hs (X * L - 1) := by
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL

  have h : L * X - 1 = L * (X * L - 1) * Lᴴ := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hL']
  rw [h, hs_mul_mul_conjTranspose_of_unitary L _ hL]

theorem isGaugeSub_map_mul_right (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) (l : Formalism.REAL.UJ ε) (hlM : l ∈ M) (hlK : l ∈ maxK ε) :
    μ.map (fun g => g * l) = μ := by
  unfold IsGaugeSub at hμ
  obtain ⟨hμc, hinv, hlim⟩ := hμ
  have hlU : (uMat l)ᴴ * uMat l = 1 := by unfold maxK at hlK; exact hlK

  obtain ⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ,
      μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by
    refine ((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists
    · exact Metric.measure_ball_pos _ _ one_pos
    · exact measure_ball_lt_top
  have hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_div] at h1
    exact lt_irrefl _ h1
  have hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h2
    exact lt_irrefl _ h2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g := by
    unfold uMat
    fun_prop
  have hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    fun_prop
  have hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r := by
      rw [show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]
      simp [Formalism.REAL.hs, hr]
    exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg =>
      show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg

  have hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔
      l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro g
    show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r
    rw [show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl,
      hs_conj (uMat l) (uMat g) hlU]
  exact map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _
    (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm

end GlobalTheory.GaugeRightInv
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_E_eq_F (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.E) = Fintype.card (InfinitePlace I.F) := by
  have hsurj : Function.Surjective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) :=
    fun v => InfinitePlace.comap_surjective v
  have hinj : Function.Injective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
    intro w₁ w₂ h
    have key : ∀ w : InfinitePlace I.E,
        w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases _root_.GlobalTheory.Count.Test.embedding_cases I w with hw | hw
      · rw [← hw, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← hw, InfinitePlace.mk_embedding]
    rw [key w₁, key w₂]
    simp only at h
    rw [h]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩

open MeasureTheory NumberField Matrix Finset in
private theorem card_infinitePlace_F_eq_finrank (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.F) = Module.finrank ℚ I.F := by
  haveI := I.cm.totReal
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero] at *
  omega

open MeasureTheory NumberField Matrix Finset in
private theorem one_le_abs_discr_E (I : _root_.Formalism.MainNotions.S.AutInst) : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
  have h := discr_ne_zero I.E
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.instance_numbers : ∀ I : _root_.Formalism.MainNotions.S.AutInst, _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * _root_.Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, _root_.GlobalTheory.FlagMeas.HasSig I p q → p + q = I.n := by
  intro I
  have hdeg : _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [card_infinitePlace_E_eq_F, card_infinitePlace_F_eq_finrank]
  have hcardF : Fintype.card (InfinitePlace I.F) = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact card_infinitePlace_F_eq_finrank I
  have hfpos : 1 ≤ I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact Module.finrank_pos
  refine ⟨hdeg, ?_, ?_, hfpos, hcardF, ?_⟩
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd _root_.Formalism.HermitianLatticesTheory.vInv
    rw [hdeg]
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    ring
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd
    apply Real.one_le_rpow (one_le_abs_discr_E I)
    positivity
  · intro p q h
    unfold _root_.GlobalTheory.FlagMeas.HasSig at h
    have hne : Nonempty (InfinitePlace I.F) := by
      apply Fintype.card_pos_iff.mp
      omega
    obtain ⟨v⟩ := hne
    obtain ⟨hp, hq⟩ := h v
    rw [← hp, ← hq]
    unfold _root_.Formalism.MainNotions.S.AutInst.pAt _root_.Formalism.MainNotions.S.AutInst.qAt
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin I.n))) (fun a => I.ε v a = true)
    simpa using this

end GlobalTheory.FlagMeas
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.autPoint_rational_equivariance : ∀ (I : AutInst) (x : I.GA) (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → lamX I (a * x) = (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ (∀ w y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (a * x)) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y) ∧ least I (a * x) = least I x ∧ (∀ t, stepLe I (a * x) t = (stepLe I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ stepLt I (a * x) t = (stepLt I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E))) ∧ (∀ (m : ℕ) (j : Fin m → ℕ) (τ : Fin m → ℝ), HasType I (a * x) j τ ↔ HasType I x j τ) ∧ ((x⁻¹ * a * x).2 ∈ I.Kset ↔ (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) = lamX I x) ∧ ∀ w, (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E))) ∨ (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = (uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PointEquivariance.equivariance | exact GlobalTheory.PointEquivariance.equivariance | (intros; apply GlobalTheory.PointEquivariance.equivariance <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselZhat_inv_and_regular_iff : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), γ ∈ GG k r → Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  first | exact @GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | exact GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | (intros; apply GlobalTheory.SgInf.RegInv.zhat_inv_and_reg <;> assumption)
end

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : Matrix (Fin n) (Fin n) ℂ → E), DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => F (Matrix.of y)) {y | Matrix.of y ∈ GlobalTheory.Dec.KC ε} → (∀ k ∈ Formalism.REAL.Kset ε, F k = 0) → ∀ y ∈ GlobalTheory.Dec.KC ε, F y = 0 := by
  first | exact @GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset | exact GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset | (intros; apply GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset <;> assumption)
end
