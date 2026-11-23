module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle293
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxLevi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle003
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.GL2.GJFEInduced
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
import GroundTheory.AutomorphicForms.GL2.GJFELevi
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.UnramifiedHensel
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))

private theorem absPow_one_unif :
    ((absPow k 1 (unif k) : ℂˣ) : ℂ) * (resCard k : ℂ) = 1 := by
  have hq : (resCard k : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
    exact_mod_cast this.ne'
  rw [val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif valuation_unif]
  push_cast
  exact inv_mul_cancel₀ hq

private theorem link_iff {ξ ξ' : kˣ →* ℂˣ} (hξ : IsSmoothChar ξ) (hξ' : IsSmoothChar ξ') :
    IrrGL.ofChar ξ hξ = (IrrGL.ofChar ξ' hξ').nu 1 ↔
      IsUnram (ξ' * ξ⁻¹) ∧ (((ξ' * ξ⁻¹) (unif k) : ℂˣ) : ℂ) = (resCard k : ℂ) := by
  have hA := absPow_one_unif (k := k)
  have hA0 : ((absPow k 1 (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
  constructor
  · rintro rfl
    have e : ξ' * (ξ' * absPow k 1)⁻¹ = (absPow k 1)⁻¹ := by
      rw [mul_inv, mul_inv_cancel_left]
    rw [e]
    refine ⟨isUnram_inv (isUnram_absPow k 1), ?_⟩
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have hq : (resCard k : ℂ) = ((absPow k 1 (unif k) : ℂˣ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hA
    rw [hq]
  · rintro ⟨hu, hv⟩
    obtain ⟨-, h2, -⟩ := polFacts k
    refine h2 ξ (ξ' * absPow k 1) ?_ ?_
    · have e : ξ * (ξ' * absPow k 1)⁻¹ = (ξ' * ξ⁻¹)⁻¹ * (absPow k 1)⁻¹ := by
        simp only [mul_inv, inv_inv]
        ac_rfl
      rw [e]
      exact isUnram_mul (isUnram_inv hu) (isUnram_inv (isUnram_absPow k 1))
    · refine Units.ext ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      rw [← hv] at hA
      rw [MonoidHom.mul_apply, Units.val_mul]
      have h0 : ((ξ (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at hA
      rw [mul_comm, hA]

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PlainIff := by
  intro K _ _ _ n hn π v
  obtain ⟨-, huniq, -, -, -⟩ := suppFacts K n hn π v
  have hq : (Ideal.absNorm v.asIdeal : ℂ) = (resCard (v.adicCompletion K) : ℂ) := by
    have h : GroundTheory.LocalField.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
      GroundTheory.Global.residueCard_adicCompletion
    rw [← h]
    rfl
  constructor
  · intro h
    refine ⟨fun σ hσ => ?_, fun s hs ξ hξ ξ' hξ' hu e => ?_⟩
    · obtain ⟨s, h1, h2, -⟩ := h σ hσ
      exact ⟨s, h1, h2⟩
    · obtain ⟨σ, hσ, -⟩ := id hs
      obtain ⟨t, ht, -, hl⟩ := h σ hσ
      obtain rfl : s = t := huniq s t hs ⟨σ, hσ, ht.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
      obtain ⟨a, ha⟩ := hξ
      obtain ⟨b, hb⟩ := hξ'
      exact hl _ hb _ ha ((link_iff b a).2 ⟨hu, e.trans hq⟩)
  · rintro ⟨ht, hu⟩ σ hσ
    obtain ⟨s, hs, h1⟩ := ht σ hσ
    refine ⟨s, hs, h1, fun y hy z hz e => ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (h1 y hy)
    obtain ⟨ξ', hξ', rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z (h1 z hz)
    obtain ⟨h2, h3⟩ := (link_iff hξ hξ').1 e
    exact hu s ⟨σ, hσ, hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩ ξ' ⟨hξ', hz⟩ ξ ⟨hξ, hy⟩ h2 (h3.trans hq.symm)
end

section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  have h := Classical.epsilon_spec (p := fun p : kˣ => valuation k (p : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k))
    ⟨Units.mk0 p hp0, by rw [Units.val_mk0, hp]; exact uniformizer_lt_one,
      fun x hx => by rw [Units.val_mk0, hp]; exact le_uniformizer_iff.2 hx⟩
  exact le_antisymm (le_uniformizer_iff.2 h.1) (hp ▸ h.2 p (hp ▸ uniformizer_lt_one))

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SphUnl := by
  intro K _ _ _ n hn π v B hB
  obtain ⟨⟨s₀, hs₀⟩, huniq, htor, hunr, -⟩ := suppFacts K n hn π v
  refine ⟨(htor s₀ hs₀).1.2 fun y hy => ?_, fun s hs => ?_⟩
  · obtain ⟨μ, hμ, rfl⟩ := hunr s₀ B hs₀ hB y hy
    rfl
  · obtain ⟨σ, hσ, -⟩ := id hs
    obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π v B).1 hB) hσ
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (v.adicCompletion K) n (fun i => unrChar _ (α i))
      (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hS.2.2
    have key : ∀ ξ ∈ chars s, ξ (unif _) ∈ B := by
      rintro ξ ⟨hξ, hm⟩
      rw [huniq s _ hs ⟨σ, hσ, h⟩] at hm
      obtain ⟨i, hi, e⟩ := Multiset.mem_map.1 hm
      rw [← IrrGL.ofChar_inj.1 e, unrChar_uniformizer _ _ (val_unif _), ← hα]
      exact Multiset.mem_map_of_mem _ hi
    intro ξ hξ ξ' hξ' _ e
    refine UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v B hB _ (key ξ hξ) _ (key ξ' hξ') ?_
    rw [← e, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel_right]
end

section

open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL

private theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.kappa_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ} (a : Set.range β) (ha : blockSize β a = 1) :
    inducedChar β (blockUnif F a) = 1 := by
  have hML : leviModulus β (blockUnif F a) = leviAbsDet β (blockUnif F a) := by
    rw [← leviEquivPi_symm_mulSingle (F := F) a]
    set x : (b : Set.range β) → GL (Fin (blockSize β b)) F := Pi.mulSingle a (centralUnif F (blockSize β a)) with hx
    have hC : ((leviAbsDet β ((leviEquivPi F β).symm x) : ℝ≥0) : ℂ) = ∏ b, detPow (x b) 1 := by
      rw [← detPow_leviEquivPi_symm, detPow_eq_cpow, Complex.cpow_one]
      rfl
    rw [Finset.prod_eq_single a (fun b _ hb => by
        rw [hx, Pi.mulSingle_eq_of_ne hb]
        exact detPow_of_mem_integralGL (one_mem _) 1) (by simp), detPow_eq_cpow, Complex.cpow_one] at hC
    rw [leviModulus_leviEquivPi_symm, Finset.prod_eq_single a]
    · rw [detModulusPow]
      conv_lhs => arg 2; rw [ha]
      rw [pow_one]
      exact_mod_cast hC.symm
    · intro b _ hb
      rw [hx, Pi.mulSingle_eq_of_ne hb, detModulusPow]
      simp
    · simp
  set m := blockUnif F a
  have key := leviRatio_sq_mul_modular_mul_det m
  rw [hML] at key
  have hD : 0 < leviAbsDet β m := modulus_det_pos _
  have hsq : inducedChar β m ^ 2 = 1 := by
    have e : inducedChar β m = leviRatio β m * NNReal.sqrt (MeasureTheory.Measure.modularCharacter (leviIncl m)) *
        leviAbsDet β m ^ (((n : ℝ) - 1) / 2) := rfl
    rw [e, mul_pow, mul_pow, NNReal.sq_sqrt, ← NNReal.rpow_natCast (leviAbsDet β m ^ (((n : ℝ) - 1) / 2)),
      ← NNReal.rpow_mul]
    have h2 : ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
    rw [h2]
    apply mul_right_cancel₀ hD.ne'
    rw [one_mul]
    conv_rhs => rw [← key]
    rw [mul_assoc, ← NNReal.rpow_add_one hD.ne', sub_add_cancel, NNReal.rpow_natCast]
  exact (pow_left_inj₀ (by positivity) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.gamLocX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.GamLocX := by
  intro K _ _ n hn v V _ _ π s hs
  haveI := hs.isIrreducible
  obtain ⟨β, W, _, _, σ, hirr, hsm, hcusp, hadm, Φ, hinj⟩ := exists_embedding_parabolicInd hs.isSmooth
  letI : MeasurableSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := borel _
  haveI : BorelSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := ⟨rfl⟩
  haveI := hirr
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := σ) hsm
  have hB := gxBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  have hψc := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨γ, hshape, hFE⟩ := gxLevi hB hadm hcusp (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψc hψ1 hω
  have hInd := inducedFE_of_leviFE (localHaar n v) hψc hψ1 hFE
  have hG := coefInd _ n V π hs.isSmooth β W σ hsm Φ hinj (localHaar n v) _ hψc hψ1 γ hInd
  have hpolF : polF σ (fun a => ((inducedChar β (blockUnif (HeightOneSpectrum.adicCompletion K v) a) : ℝ≥0) : ℂ) * ω a)
      = polF σ ω := by
    unfold polF
    refine Finset.prod_congr rfl (fun a _ => ?_)
    split_ifs with h
    · beta_reduce
      rw [kappa_one a h.1]
      simp
    · rfl
  have hpol := gxSupp hs hirr hcusp Φ hinj hω
  rw [hpolF, GroundTheory.Global.residueCard_adicCompletion] at hshape
  obtain ⟨c, j, hc, hγ⟩ := hshape
  refine ⟨c, j, hc, ?_⟩
  rw [hpol, ← hγ]
  exact hG
end

section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private lemma window_mul (q : ℕ) (hq : q ≠ 0) (t a : ℝ) (x y : ℂ)
    (hy : ‖y‖ = (q : ℝ) ^ a)
    (hx : (q : ℝ) ^ (t - 1 / 2) < ‖x‖ ∧ ‖x‖ < (q : ℝ) ^ (t + 1 / 2)) :
    (q : ℝ) ^ (t + a - 1 / 2) < ‖x * y‖ ∧ ‖x * y‖ < (q : ℝ) ^ (t + a + 1 / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have ha : (0 : ℝ) < (q : ℝ) ^ a := Real.rpow_pos_of_pos hq0 a
  rw [norm_mul, hy, show t + a - 1 / 2 = (t - 1 / 2) + a by ring,
    show t + a + 1 / 2 = (t + 1 / 2) + a by ring, Real.rpow_add hq0, Real.rpow_add hq0]
  exact ⟨mul_lt_mul_of_pos_right hx.1 ha, mul_lt_mul_of_pos_right hx.2 ha⟩

theorem winTw : WinTw := by
  intro K _ _ _ χ
  obtain ⟨a, ha⟩ := charAbs K χ
  refine ⟨a, fun n hn π t v hw => ?_⟩
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨⟨s, hs⟩, -, hπ, -, -⟩ := suppFacts K n hn π v
  obtain ⟨⟨s₁, hs₁⟩, huniq, hπ', -, -⟩ := suppFacts K n hn (π.twist χ) v
  obtain ⟨s₂, hs₂, -, hchars, hmap⟩ := suppTw K n hn π v χ s hs
  refine ⟨?_, fun s' hs' ζ hζ => ?_⟩
  · refine ((hπ' s₂ hs₂).1).2 fun y hy => ?_
    have hy' : y.1 ∈ s₂.map Sigma.fst := Multiset.mem_map_of_mem _ hy
    rw [hmap] at hy'
    obtain ⟨x, hx, hxy⟩ := Multiset.mem_map.1 hy'
    rw [← hxy]
    exact ((hπ s hs).1).1 hw.1 x hx
  · rw [huniq s' s₂ hs' hs₂] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := (hchars ζ).1 hζ
    simpa [MonoidHom.mul_apply, Units.val_mul] using
      window_mul _ hq t a _ _ (ha v).2 (hw.2 s hs ξ hξ)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end
