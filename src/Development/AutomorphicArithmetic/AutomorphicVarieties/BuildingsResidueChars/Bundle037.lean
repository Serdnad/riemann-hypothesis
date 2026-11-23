module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.GL2.GJUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (σ : Weil h),
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    ((cycBar F Ω p σ : (Qbar p)ˣ) : Qbar p) = GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w (a σ : w.adicCompletion F) := by
  intro hG F Ω _ _ _ _ _ w A h a ha p _ ι σ hv
  obtain ⟨art, hart⟩ := hG F Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1)
  have e := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hL
  have h1 := hL.loc (a σ) σ (ha.glob art hart σ)
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hu : Valued.v (a σ : w.adicCompletion F) = 1 := he.eq_one_iff_eq_one.1 hv
  have h2 : (GlobalTheory.HeckeGal.Model.absPow F ((1 : ℕ) : ℝ)).loc w (a σ) = 1 :=
    (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F ((1 : ℕ) : ℝ)).1 w _ hu
  rw [h2, e, pow_one, cyc_eq_map_cycZ] at h1
  simp only [Units.val_one, map_one, one_mul, Nat.cast_one] at h1
  exact h1
end

section

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem integral_iff_one (g : GL (Fin 1) F) :
    (∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j ∈ 𝒪[F]) ↔ 0 ≤ ordDet g := by
  constructor
  · exact ordDet_nonneg_of_integral
  · intro h i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    have hne : (g : Matrix (Fin 1) (Fin 1) F) 0 0 ≠ 0 := by
      simpa [Matrix.det_unique] using det_ne_zero g
    rw [← GroundTheory.LocalField.mem_valBall_zero_iff, GroundTheory.LocalField.mem_valBall_iff_le_ord hne]
    simpa [ordDet, Matrix.det_unique] using h

private theorem mem_tile_one (g : GL (Fin 1) F) : g ∈ tile F 1 0 ↔ ordDet g = 0 := by
  simp only [tile, Set.mem_ofPred_eq]
  push_cast
  omega

private theorem int_of_tile {g : GL (Fin 1) F} (hg : g ∈ tile F 1 0) : g ∈ integralGL F 1 := by
  have h0 := (mem_tile_one g).1 hg
  rw [mem_integralGL_iff]
  refine ⟨(integral_iff_one g).2 (by omega), (integral_iff_one g⁻¹).2 ?_⟩
  rw [ordDet_inv]
  omega

private theorem isCompact_tile_one : IsCompact (tile F 1 0) := by
  have h := isCompact_shell F 1 0 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, pow_zero, one_mul, mem_tile_one]
  exact ⟨fun h0 => ⟨(integral_iff_one g).2 h0.ge, h0⟩, fun h => h.2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.local_zeta_integral_tate_comparison :
    UpperTheory.V.Z.Gam.LdTate := by
  intro F _ _ _ _ _ _ μ _
  refine ⟨integralIndicator F 1, isSchwartzBruhat_integralIndicator, ((μ.real (tile F 1 0) : ℝ) : ℂ), ?_, ?_⟩
  · have hpos : 0 < μ (tile F 1 0) := (isOpen_tile 0).measure_pos μ ⟨1, (mem_tile_one 1).2 ordDet_one⟩
    have hfin : μ (tile F 1 0) < ⊤ := isCompact_tile_one.measure_lt_top
    show (((μ (tile F 1 0)).toReal : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  · intro α c hc hcK s hs
    have hs1 : ‖α * qs F s‖ < 1 := by simpa using hs
    have hint := hc.integrable_zeta μ (isSchwartzBruhat_integralIndicator (F := F) (n := 1)) hs
    have h1 := hasSum_integral_tile μ hint
    have hterm : ∀ j : ℤ, (∫ g in tile F 1 0, integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
        detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g) ∂μ) =
        if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0 := by
      intro j
      have hEq : Set.EqOn (fun g => integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
          detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g))
          (fun _ => if 0 ≤ j then (α * qs F s) ^ j * c 1 else 0) (tile F 1 0) := by
        intro g hg
        have hgK := int_of_tile hg
        have h0 := (mem_tile_one g).1 hg
        have hiff : ((↑(centralUnif F 1 ^ j * g) : Matrix (Fin 1) (Fin 1) F) ∈ integralMatrixSet F 1) ↔ 0 ≤ j := by
          rw [mem_integralMatrixSet, integral_iff_one, ordDet_centralUnif_zpow_mul, h0]
          push_cast
          omega
        have hind : integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) = if 0 ≤ j then 1 else 0 := by
          unfold integralIndicator
          by_cases hj : 0 ≤ j
          · rw [Set.indicator_of_mem (hiff.2 hj), if_pos hj]
            rfl
          · rw [Set.indicator_of_notMem (fun h => hj (hiff.1 h)), if_neg hj]
        simp only
        rw [hind, detPow_centralUnif_zpow_mul, detPow_of_mem_integralGL hgK, hc.zpow_mul, hcK g hgK]
        split_ifs
        · push_cast
          rw [mul_one, mul_zpow]
          ring_nf
        · simp
      rw [setIntegral_congr_fun (measurableSet_tile 0) hEq, setIntegral_const, Complex.real_smul]
      split_ifs <;> ring
    have h2 := h1
    simp only [hterm] at h2
    have hgeo : HasSum (fun j : ℤ => if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0)
        ((1 - α * qs F s)⁻¹ * (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))) := by
      have hn := (hasSum_geometric_of_norm_lt_one hs1).mul_right (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))
      rw [← Nat.cast_injective.hasSum_iff]
      · simpa [Function.comp_def, zpow_natCast, mul_assoc] using hn
      · intro j hj
        have hn' : ¬ 0 ≤ j := fun h => hj ⟨j.toNat, Int.toNat_of_nonneg h⟩
        simp [hn']
    rw [h2.unique hgeo, div_eq_mul_inv]
    ring
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing UpperTheory.V
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ec_le {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) : ‖j.1 (x : w.adicCompletion L)‖ ≤ 1 := by
  have hc : Continuous fun y : 𝒪[w.adicCompletion L] => ‖j.1 (y : w.adicCompletion L)‖ :=
    (j.2.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hc).bddAbove
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hx)
  have h := hB ⟨x ^ n, rfl⟩
  simp only [SubmonoidClass.coe_pow, map_pow, norm_pow] at h
  exact absurd h (not_le.2 hn)

private theorem ec_lt {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) (hx : x ∈ maximalIdeal 𝒪[w.adicCompletion L]) :
    ‖j.1 (x : w.adicCompletion L)‖ < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 : valuation (w.adicCompletion L) (x : w.adicCompletion L) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have h2 : Valued.v (x : w.adicCompletion L) < 1 :=
    (ValuativeRel.isEquiv (valuation (w.adicCompletion L))
      (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.1 h1
  have ht : Filter.Tendsto (fun k : ℕ => (x : w.adicCompletion L) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one h2
  have ht2 := (j.2.tendsto 0).comp ht
  rw [map_zero] at ht2
  refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (ht2.congr fun k => ?_)
  simp

private theorem ec_field {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, j.1 x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Qh13.ec_field j

theorem UpperTheory.expChar_integrality_criterion :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (w : W.Plc L) (j : W.Emb l w), (∀ c : Coef l, ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x : 𝒪[w.adicCompletion L], j.1 (x : w.adicCompletion L) ∈ c'.O) ∧ ∀ (c' : Coef l), ∀ x ∈ maximalIdeal 𝒪[w.adicCompletion L], ∀ h : j.1 (x : w.adicCompletion L) ∈ c'.O, (⟨_, h⟩ : c'.O) ∈ maximalIdeal c'.O := by
  intro L _ _ l _ w j
  refine ⟨fun c => ?_, fun c' x hx h hu => ?_⟩
  · obtain ⟨K, hK, hj⟩ := ec_field j
    obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
    let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
    have hf : Function.Injective f := Subtype.val_injective
    let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
    let d : Coef l := ⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
      Module.Finite.equiv e.toLinearEquiv⟩
    obtain ⟨c', hc, hd⟩ := (HV.coefSup l).1 c d
    refine ⟨c', hc, fun x => hd ?_⟩
    exact ⟨⟨_, hj x⟩, (isIntegral_algHom_iff f hf).1 ((ec_intIff _).2 (ec_le j x)), rfl⟩
  · obtain ⟨y, hy⟩ := hu.exists_left_inv
    have hy' : (y : PadicAlgCl l) * j.1 (x : w.adicCompletion L) = 1 := congrArg Subtype.val hy
    have h1 : ‖(y : PadicAlgCl l)‖ ≤ 1 :=
      (ec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c'.O.val)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_right h1 (norm_nonneg _) (ec_lt j x hx)
    rw [← norm_mul, hy', norm_one] at h2
    exact lt_irrefl _ h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)
open scoped Pointwise

section SlopeTestRemainingChoices

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

private theorem place_conj {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v := fun x => by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  have hv : ∀ y, (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]
  rw [hv, AlgEquiv.commutes]
  exact h x

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsPlaceOver A w ∧ w.under (𝓞 F) = v := by
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap E Ω (x : E)) := (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint
  let P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.isSplitAt_of_decomposition_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Dec (F := Lp L) A ≤ (resP L Ω).range → ∀ w : Plc L, w.under (𝓞 (Lp L)) = v → IsSplitAt w := by
  intro L Ω _ _ _ _ _ _ A v hA hD w hw
  by_contra hs
  have huniq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = v → u = w := fun u hu => by
    by_contra h
    exact hs ⟨u, h, hu.trans hw.symm⟩
  haveI : Normal (Lp L) Ω := IsAlgClosure.normal _ _
  let t : G (Lp L) Ω := (IsCMField.complexConj L).liftNormal Ω
  have ht : ∀ y : L, t (algebraMap L Ω y) = algebraMap L Ω (IsCMField.complexConj L y) := fun y =>
    AlgEquiv.liftNormal_commutes _ Ω y
  obtain ⟨u, hu, hu'⟩ := place_between (E := L) hA
  obtain ⟨u', hu1, hu1'⟩ := place_between (E := L) (place_conj hA t)
  rw [huniq u hu'] at hu
  rw [huniq u' hu1'] at hu1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hu hu1
  have hg' : resP L Ω g • A = t⁻¹ • A := hg
  have hm : t * resP L Ω g ∈ Dec (F := Lp L) A := by
    show (t * resP L Ω g) • A = A
    rw [mul_smul, hg', smul_inv_smul]
  obtain ⟨k, hk⟩ := (Subgroup.mul_mem_cancel_right _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD hm)
  apply IsCMField.complexConj_ne_one L
  ext y
  apply (algebraMap L Ω).injective
  rw [← ht, ← hk]
  exact k.commutes y
end
