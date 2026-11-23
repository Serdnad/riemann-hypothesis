module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.LocalFields.Uniqueness
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.unitSB :
    UpperTheory.V.Z.Tf.Orb.UnitSB := by
  intro E _ _ _ _ n
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have ho : IsOpen (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isOpen_integralGL E n
  have hc : IsCompact (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isCompact_integralGL E n
  refine ⟨ho, hc, ?_, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    by_cases hx : x ∈ (unitGL (n := Fin n) E : Set (GL (Fin n) E))
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_mem hx, Set.indicator_of_mem hy, Pi.one_apply]
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
end

section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.placeUnit :
    UpperTheory.V.Z.Tf.Orb.UnitMatch → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.PlaceData → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal → UpperTheory.V.Z.Tf.Orb.PlaceInt → UpperTheory.V.Z.Tf.Orb.PlaceUnit := by
  intro hM hU hD hL hI hB F E _ _ _ _ _ _ σ hσ v w hw hur n _ _ _ _ mE mF hE hF vE vF
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := hD F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨hH, hP⟩ := @hL F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hm := @hM hB _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 hur) s hs n _ _ _ _ _ mF hH hF
    (by rw [Measure.map_apply hc.measurable (hU _ n).1.measurableSet, ← hI.2 F E v w hw n, vE])
    (by rw [hI.1 F v n, vF])
  have := hP _ (hU _ n).2.2 _ (hU _ n).2.2 hm
  rw [hI.2 F E v w hw n, ← hI.1 F v n]
  exact this
end

section

open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeData :
    UpperTheory.V.Z.Tf.Orb.PlaceData := by
  intro F E _ _ _ _ _ _ σ hσ v w hw
  have hfix : ∀ τ : E ≃ₐ[F] E, w.1 = τ • w.1 := fun τ => (congrArg Subtype.val (hw (τ • w))).symm
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  have hfin : FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E) :=
    Module.finite_of_finrank_pos (hrk ▸ Module.finrank_pos)
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'
  have hle : ∀ x y : w.1.adicCompletion E, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v x y
  have hlt : ∀ x : w.1.adicCompletion E, valuation _ x < 1 ↔ Valued.v x < 1 := fun x =>
    (ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v).lt_one_iff_lt_one
  have hval : ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E) := ⟨fun {a b} => by
    change Valued.v (completionMap v w.1 a) ≤ Valued.v (completionMap v w.1 b) ↔ Valued.v a ≤ Valued.v b
    rw [valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0⟩
  let Φ : (E ≃ₐ[F] E) →* (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) :=
    MonoidHom.mk' (fun τ => galEquiv v τ w.1 w.1 (hfix τ)) fun a b => AlgEquiv.ext fun y => by
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
        (continuous_galEquiv v (a * b) w.1 w.1 (hfix _))
        ((continuous_galEquiv v a w.1 w.1 (hfix _)).comp (continuous_galEquiv v b w.1 w.1 (hfix _))) ?_) y
      funext x
      simp only [Function.comp_apply, galEquiv_algebraMap, AlgEquiv.mul_apply]
  have hinj : Function.Injective Φ := fun a b h => AlgEquiv.ext fun x => by
    have h1 := DFunLike.congr_fun h (algebraMap E (w.1.adicCompletion E) x)
    change galEquiv v a w.1 w.1 (hfix _) _ = galEquiv v b w.1 w.1 (hfix _) _ at h1
    rw [galEquiv_algebraMap, galEquiv_algebraMap] at h1
    exact (algebraMap E (w.1.adicCompletion E)).injective h1
  have hc : Nat.card (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) = Nat.card (E ≃ₐ[F] E) := by
    refine le_antisymm ?_ (Nat.card_le_card_of_injective Φ hinj)
    rw [IsGalois.card_aut_eq_finrank F E, ← hrk, Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hgal : IsGalois (v.adicCompletion F) (w.1.adicCompletion E) :=
    IsGalois.of_card_aut_eq_finrank _ _ (by rw [hc, IsGalois.card_aut_eq_finrank F E, hrk])
  have hsurj : Function.Surjective Φ := ((Nat.bijective_iff_injective_and_card Φ).2 ⟨hinj, hc.symm⟩).2
  refine ⟨inferInstance, hval, hfin, hgal, Φ σ, fun τ => ?_, hrk, fun x => rfl, fun y => ?_, fun hu => ?_⟩
  · obtain ⟨a, rfl⟩ := hsurj τ
    obtain ⟨j, rfl⟩ := hσ a
    exact ⟨j, (map_zpow Φ σ j).symm⟩
  · obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 (hfix σ) x).symm
      · exact ((Φ σ).commutes a).symm
  · have := w.1.isPrime
    have he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hu
    obtain ⟨π, hπ⟩ := valued_adicCompletion_surjective (K := F) v (WithZero.exp (-1 : ℤ))
    have h1 : Valued.v (algebraMap (v.adicCompletion F) (w.1.adicCompletion E) π) = WithZero.exp (-1 : ℤ) := by
      rw [algebraMap_completion_eq, valued_completionMap, he, pow_one, hπ]
    refine ⟨π, (hlt _).2 (by rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega), fun x hx => (hle _ _).2 ?_⟩
    rw [h1]
    have h2 := (hlt x).1 hx
    by_cases h0 : Valued.v x = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
end

section

open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeUniq :
    UpperTheory.V.Z.Tf.Orb.PlaceUniq := by
  intro F E _ _ _ _ _ _ hp v hs
  obtain ⟨w, hw⟩ := not_forall.1 hs
  have hd : ∀ w' : PlacesOver E v, Module.finrank (v.adicCompletion F) (w'.1.adicCompletion E) =
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) := fun w' => by
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (E ≃ₐ[F] E) w w'
    exact (galEquiv v σ w.1 w'.1 (by rw [← hσ]; rfl)).toLinearEquiv.finrank_eq.symm
  have h := sum_finrank_eq E v
  rw [Finset.sum_congr rfl fun w' _ => hd w', Finset.sum_const, smul_eq_mul, Finset.card_univ] at h
  rcases (Nat.prime_mul_iff.1 (h ▸ hp)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact absurd (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2 hw
  · obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 h1
    exact ⟨u, hu⟩
end

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

private theorem UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG]
    (H : Subgroup G) (μ : Measure H) [SFinite μ] {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μ ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hset : MeasurableSet {p : G × H | ρ ((p.2 : G) * p.1) < ∞} :=
    measurableSet_lt (hρ.1.comp hmul) measurable_const
  have h1 : ∀ᵐ g ∂μG, ∀ᵐ h : H ∂μ, ρ ((h : G) * g) < ∞ := by
    refine Filter.Eventually.of_forall fun g => ?_
    refine ae_lt_top (hρ.1.comp (measurable_subtype_coe.mul_const g)) ?_
    rw [hρ.2 g]; exact ENNReal.one_ne_top
  have h2 : ∀ᵐ h : H ∂μ, ∀ᵐ g ∂μG, ρ ((h : G) * g) < ∞ :=
    (Measure.ae_ae_comm (p := fun (g : G) (h : H) => ρ ((h : G) * g) < ∞) hset).1 h1
  have hne : μ ≠ 0 := by
    intro h0
    have := hρ.2 1
    rw [h0, lintegral_zero_measure] at this
    exact zero_ne_one this
  haveI : (ae μ).NeBot := ae_neBot.2 hne
  obtain ⟨h, hh⟩ := h2.exists
  have h3 := (measurePreserving_mul_left μG ((h : G)⁻¹)).quasiMeasurePreserving.ae hh
  simpa using h3

theorem UpperTheory.V.Z.Tf.Orb.quotReal :
    UpperTheory.V.Z.Tf.Orb.QuotReal := by
  intro G _ _ _ _ μG _ _ H μ _ A hA
  unfold quotIntegral quotLIntegral
  split_ifs with hex
  · have hρ := hex.choose_spec
    set ρ := hex.choose
    have hfin := UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin μG H μ hρ
    have hm : Measurable fun g => A.indicator (1 : G → ℝ≥0∞) g * ρ g :=
      (measurable_one.indicator hA).mul hρ.1
    rw [← integral_toReal hm.aemeasurable, ← integral_complex_ofReal]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g ∈ A <;> simp [hg]
    · filter_upwards [hfin] with g hg
      by_cases hgA : g ∈ A <;> simp [hgA, hg]
  · simp
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

section Core

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group T] [MeasurableSpace T] [MeasurableInv T]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν] {j : T →* G}

omit [MeasurableInv G] [MeasurableInv T] in
private theorem ae_fin (hj : Measurable j) {ρ : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) :
    ∀ᵐ g ∂μ, ρ g < ∞ := by
  have hA : MeasurableSet {g | ρ g = ∞} := hm (measurableSet_singleton _)
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have h1 : ∫⁻ g, ∫⁻ t, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂ν ∂μ = 0 := by
    refine (lintegral_congr fun g => ?_).trans lintegral_zero
    have h2 : ∀ᵐ t ∂ν, ρ (j t * g) < ∞ := ae_lt_top (hm.comp (hj.mul_const g)) (by rw [h]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae (h2.mono fun t ht => ?_)).trans lintegral_zero
    exact Set.indicator_of_notMem (s := {g | ρ g = ∞}) ht.ne _
  rw [lintegral_lintegral_swap (f := fun g t => {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g))
    ((measurable_one.indicator hA).comp hmul).aemeasurable] at h1
  have h3 : ∀ t : T, ∫⁻ g, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂μ = μ {g | ρ g = ∞} := fun t => by
    rw [lintegral_mul_left_eq_self, lintegral_indicator_one hA]
  simp only [h3, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · rw [ae_iff]
    simpa using h1
  · have := h 1
    rw [Measure.measure_univ_eq_zero.1 h1] at this
    simp at this

private theorem lint_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫⁻ g, F g * ρ g ∂μ = ∫⁻ g, F g * ρ' g ∂μ := by
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => j p.2⁻¹ * p.1 := (hj.comp measurable_snd.inv).mul measurable_fst
  have a : ∀ g, F g * ρ g = ∫⁻ t, F g * ρ g * ρ' (j t * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ' (j t * g)) (hm'.comp (hj.mul_const g)), h', mul_one]
  have b : ∀ g, F g * ρ' g = ∫⁻ t, F g * ρ' g * ρ (j t⁻¹ * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ (j t⁻¹ * g)) (hm.comp ((hj.comp measurable_inv).mul_const g)),
      lintegral_inv_eq_self (fun t : T => ρ (j t * g)), h, mul_one]
  rw [lintegral_congr a, lintegral_congr b,
    lintegral_lintegral_swap (f := fun g t => F g * ρ g * ρ' (j t * g))
      (((hF.comp measurable_fst).mul (hm.comp measurable_fst)).mul (hm'.comp hmul)).aemeasurable,
    lintegral_lintegral_swap (f := fun g t => F g * ρ' g * ρ (j t⁻¹ * g))
      (((hF.comp measurable_fst).mul (hm'.comp measurable_fst)).mul (hm.comp hmul')).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_left_eq_self _ (j t⁻¹)]
  refine lintegral_congr fun g => ?_
  rw [hFH, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul]
  ring

private theorem wd_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℂ} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μ := by
  have key : ∀ {ρ : G → ℝ≥0∞}, Measurable ρ → (∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) →
      ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := fun {ρ} hm h => by
    rw [integral_map (f := fun z : ℂ => z) hF.aemeasurable aestronglyMeasurable_id, integral_withDensity_eq_integral_toReal_smul hm (ae_fin hj hm h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [mul_comm]
  rw [key hm h, key hm' h']
  congr 1
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA), withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), ← lintegral_indicator (hF hA)]
  have e : ∀ ρ : G → ℝ≥0∞, (F ⁻¹' A).indicator ρ = fun g => (F ⁻¹' A).indicator 1 g * ρ g := fun ρ => funext fun g => by
    by_cases hg : g ∈ F ⁻¹' A <;> simp [hg]
  rw [e, e ρ']
  refine lint_eq hj (measurable_one.indicator (hF hA)) (fun t g => ?_) hm h hm' h'
  by_cases hg : F g ∈ A <;> simp [Set.indicator, hFH, hg]

end Core

theorem UpperTheory.V.Z.Tf.Orb.alongIndep :
    UpperTheory.V.Z.Tf.Orb.AlongIndep := by
  intro G T _ _ _ _ _ _ _ μ _ _ ν _ _ j hj F hF hFH ρ hρ
  have hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t => j t) ν ρ := ⟨ρ, hρ⟩
  rw [PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_left hex]
  exact wd_eq hj hF hFH hex.choose_spec.1 hex.choose_spec.2 hρ.1 hρ.2
end

section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.placeInt :
    UpperTheory.V.Z.Tf.Orb.PlaceInt := by
  refine ⟨fun F _ _ v n => rfl, fun F E _ _ _ _ _ v w hw n => ?_⟩
  ext g
  refine ⟨fun h => h w, fun h w' => ?_⟩
  obtain rfl := hw w'
  exact h
end

section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem map_comp_apply {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (n : ℕ) (f : A →+* B) (g : B →+* C) (h : A →+* C)
    (e : ∀ x, g (f x) = h x) (x : GL (Fin n) A) : mapGL n g (mapGL n f x) = mapGL n h x :=
  Units.ext (Matrix.ext fun i j => e _)

private theorem cont_map {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] (n : ℕ) (f : A →+* B)
    (hf : Continuous f) : Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

private theorem twNorm_hom {G G' : Type} [Group G] [Group G'] (e : G →* G') (θ : Monoid.End G) (θ' : Monoid.End G')
    (h : ∀ x, e (θ x) = θ' (e x)) (l : ℕ) (δ : G) : e (twNorm θ l δ) = twNorm θ' l (e δ) := by
  have hp : ∀ m x, e ((θ ^ m) x) = (θ' ^ m) (e x) := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', pow_succ_apply', h, ih]
  induction l with
  | zero => simp
  | succ l ih => rw [twNorm_succ, twNorm_succ, map_mul, ih, hp]

theorem UpperTheory.V.Z.Tf.Orb.geoTransport :
    UpperTheory.V.Z.Tf.Orb.GeoTransport := by
  intro R S S' _ _ _ _ _ _ _ _ e he he' ι ι' s s' hι hs n l _ _ _ _ _ μ μR
  let ε : GL (Fin n) S ≃ₜ* GL (Fin n) S' :=
    { toFun := mapGL n (e : S →+* S')
      invFun := mapGL n (e.symm : S' →+* S)
      left_inv := fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
      right_inv := fun x => Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
      map_mul' := map_mul _
      continuous_toFun := cont_map n _ he
      continuous_invFun := cont_map n _ he' }
  have hε : ∀ x, mapGL n (e : S →+* S') x = ε x := fun _ => rfl
  have hi : ∀ t : GL (Fin n) R, ε (mapGL n ι t) = mapGL n ι' t := fun t => map_comp_apply n _ _ _ hι t
  refine ⟨fun hμ => ε.isHaarMeasure_map μ, fun γ => ⟨fun δ => ?_, fun ν ρ' => ⟨?_, fun Φ => ?_⟩⟩⟩
  · rw [← twNorm_hom (mapGL n (e : S →+* S')) (mapGL n s) (mapGL n s')
      (fun x => Units.ext (Matrix.ext fun i j => hs _)) l δ, ← hi, hε]
    exact ε.injective.eq_iff.symm
  · have hm : Measurable ε := ε.continuous.measurable
    have hm' : Measurable ε.symm := ε.symm.continuous.measurable
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1.comp hm, fun x => ?_⟩
      simp only [id, hε, map_mul, hi]
      exact h2 _
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun x => ?_⟩
      · have := h1.comp hm'
        convert this using 1
        funext x
        simp [hε]
      · have := h2 (ε.symm x)
        simp only [id, hε, map_mul, hi, ContinuousMulEquiv.apply_symm_apply] at this
        exact this
  · exact (ε.toHomeomorph.measurableEmbedding).integral_map _
end
