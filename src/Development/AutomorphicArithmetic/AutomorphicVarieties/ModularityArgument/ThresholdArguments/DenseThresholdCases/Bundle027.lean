module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle017
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndGlue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd
private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))
theorem central_character_of_regular_cusp (hP : _root_.UpperTheory.V.Af.Hypotheses') {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    (hreg : π.IsRegAlg) (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B) :
    ∃ ω : HChar F, (∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w) ∧ ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt hP F π
  have hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := fun w α β h => by
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec h
    have hZ := (UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2
    have h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))
  refine ⟨ω, hv, fun v => ?_⟩
  have hiso : π.Iso (π.dual.twist ω) := by
    refine hP.smoR F 2 one_le_two _ _ ?_
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
      rw [← hv w α β hB, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
  obtain ⟨m, hm, -, hz⟩ := hreg v
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
  obtain ⟨i, hi⟩ := hz x (by simp)
  obtain ⟨j, hj⟩ := hz y (by simp)
  have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at h
  refine ⟨i + j + 1, ?_⟩
  push_cast at hi hj ⊢
  linear_combination hi + hj - h / 2
end
end

section




section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e
theorem UpperTheory.V.Br.cardP_of_prints :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.CardP := by
  intro P K _ _ _ n hn
  obtain ⟨c₁, A₁, hW⟩ := _root_.UpperTheory.V.Af.weyl_complex_of_printed_results P K n
  obtain ⟨c₂, A₂, hC⟩ := UpperTheory.V.Af.cohBoundFree K (Or.inl inferInstance) n ⊤ inferInstance
  refine ⟨c₂ * c₁, A₁ + A₂, fun m hm H hH M hM S hS hiso => ?_⟩
  obtain ⟨Ξ, hΞ, hd⟩ := hW m hm H hH
  have h3 : 1 ≤ 3 * M := by omega
  have hB := P.borelC K n (by omega) (UpperTheory.V.Af.KLev K n (3 * M)) (by apply UpperTheory.V.Af.isOpen_KLev; exact h3)
    (by apply UpperTheory.V.Af.isCompact_KLev; exact h3) Ξ S hiso fun π hπ =>
      ⟨P.cohC K n (by omega) π Ξ fun τ => ⟨_, (hS π hπ).1 τ, hΞ τ⟩,
        (hS π hπ).2.2.imp fun _ hv => ⟨hv.1, fun u hu => hv.2 u (klev_three K n M hu)⟩⟩
  have h1 : S.card ≤ c₂ * M ^ A₂ * Ξ.d := Nat.cast_le.1 (hB.trans (hC M hM _ _))
  have h2 : M ^ A₂ ≤ M ^ (A₁ + A₂) := Nat.pow_le_pow_right hM (by omega)
  have h4 : (H + 1) ^ A₁ ≤ (H + 1) ^ (A₁ + A₂) := Nat.pow_le_pow_right (by omega) (by omega)
  calc S.card ≤ c₂ * M ^ A₂ * Ξ.d := h1
    _ ≤ c₂ * M ^ (A₁ + A₂) * (c₁ * (H + 1) ^ (A₁ + A₂)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (hd.trans (Nat.mul_le_mul_left _ h4))
    _ = c₂ * c₁ * (M * (H + 1)) ^ (A₁ + A₂) := by rw [mul_pow]; ring
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]
theorem UpperTheory.V.Sd.self_twist_galois_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.SelfTwGal := by
  intro P F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := P.litN.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (_root_.Formalism.ConjugateSelfDual.G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (tendsto_under' (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normV_under (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s
end
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing



section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
structure AdmKNAlt [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
  level : Level l M m r
  odd : _root_.UpperTheory.V.Keep.OddA l r
structure AdmRNAlt [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : _root_.UpperTheory.V.Z.Win.IsAutQA ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : _root_.UpperTheory.V.Z.Win.A4.SafeRA l M m r
structure AdmPNAlt [IsCMField F] [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π
  unl : _root_.UpperTheory.V.Z.Win.WitA ι r
  level : Lev.LevelF l M m r
  safe : _root_.UpperTheory.V.Z.Win.A4.SafePA l M m r
theorem csdN'_alt [IsCMField F] [IsAlgClosure F Ω] (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := h
end
section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
theorem autQN'_alt (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {r : G ℚ Ω →* GL (Fin n) (Qbar l)} {wt : ℤ}
    (_ : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ) (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r := h
variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]
omit [IsAlgClosure ℚ Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] in
structure Adm3NAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
  unl : _root_.UpperTheory.V.Keep.OddA l ρ
end
def LevelKNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Level l M m r → _root_.UpperTheory.V.Keep.OddA l r → _root_.UpperTheory.V.Z.Win.WitA ι r → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)
def LevelPNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Lev.LevelF l M m r → _root_.UpperTheory.V.Z.Win.A4.SafePA l M m r → _root_.UpperTheory.V.Z.Win.WitA ι r →
      (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
      π ∈ Br.SigP K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)
def AdmResNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ),
    StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r → IsIrr (r.comp (res ℚ Ω K)) → _root_.UpperTheory.GalN.V.AdmPNAlt ι M m (r.comp (res ℚ Ω K))
end UpperTheory.GalN.V
end
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl
private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩
private theorem tw_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (R : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin 4) (Qbar l)) : R = tw (tw R (cycBar F Ω l)⁻¹) (cycBar F Ω l ^ (1 : ℤ) * 1) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : IndCs) : IndAutCs := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ h2 l _ ι π r hatt hm hb R hR H
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨P, hfin, hinf⟩ := h K M h2 π hm hb
  have key : IsAutC ι (tw R (cycBar K Ω l)⁻¹) := by
    refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => ?_, attInd K M Ω h2 l ι r R (CG.mk π).HasSat (CG.mk P).HasSat (fun _ _ _ h h' => h.unique h') (fun _ _ _ h h' => h.unique h') hatt hfin hR H⟩
    obtain ⟨m, m', τ, τ', hne, rfl, e, hv, hv', hinj⟩ := hm φ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ τ' _ _ hne e.symm hv hv')]
    exact infOf_add hinj
  rw [tw_back R]
  exact _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hP K Ω l ι 4 _ _ ((_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP K Ω l ι).1 1 1 (by simp)) key
end
end

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.GalN.V.aut_csd_zero_of_complex_conj_pair_automorphic :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G L Ω →* GL (Fin n) (Qbar l)) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω), Sd.IsCC c →
    (∃ P, Sd.IsPair c r (cycBar L Ω l ^ (1 - (n : ℤ))) P) → Sd.IsAutC ι r → AutCsd0 ι r := by
  intro hP F Ω _ _ _ _ _ _ _ l _ ι n hn r c hc ⟨P, hpair⟩ ⟨π, hreg, hatt⟩
  haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := _root_.selfDual_of_automorphic_inputs hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)
theorem tauEx' (h1 : _root_.UpperTheory.V.Cu2.KapExAlt) (h2 : TauOf) : _root_.UpperTheory.V.Cu.TauExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK hTC hdisc hdec hcc g0 hg0
  obtain ⟨m, κ, hκ⟩ := h1 hP Ω l ι K' hl2 hK hTC hdisc hdec hcc
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  haveI : CompactSpace (_root_.Formalism.ConjugateSelfDual.G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  haveI : T2Space (_root_.Formalism.ConjugateSelfDual.G K' Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[K'] Ω))
  have hc : Continuous κ := by simpa using (hκ 1 le_rfl).cont
  obtain ⟨E, hE, hmE⟩ := ce_char (_root_.Formalism.ConjugateSelfDual.G K' Ω) κ hc
  haveI := hE
  obtain ⟨c₁, hc₁⟩ := UpperTheory.V.X.So.coefOf l E
  refine ⟨m, c₁, κ, fun c₂ hc₂ j hj => ?_⟩
  refine h2 Ω l ι K' hl2 hK hdec g0 hg0 (m * j) (κ ^ j) (hκ j hj) c₂ fun h => ?_
  have e : (((κ ^ j) h : (Qbar l)ˣ) : Qbar l) = ((κ h : (Qbar l)ˣ) : Qbar l) ^ j := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  rw [e]
  exact pow_mem (hc₂ ((hc₁ _).2 (hmE h))) j
end UpperTheory.V.Cu2
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne GlobalTheory.LFun GlobalTheory.PRep UpperTheory.V.Af.Gu
private theorem sat_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv ρ') {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' B := by
  have he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    e.toIntertwiningMap.isIntertwining _ _ g v
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    have h1 := hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    refine (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map
      e.toLinearEquiv.toLinearMap he h0
    rw [he]
    exact GlobalTheory.LGrp.mem_fixed.1 hy k hk
theorem UpperTheory.V.Z.Desc.W.splitSat_alt :
    _root_.UpperTheory.V.Z.Desc.W.SplitSatAlt := by
  rintro - E _ _ n c a d hn w ρ σ had hsp S hS τ ⟨e⟩ B hB
  obtain ⟨S', s1, s2⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d hn ρ σ (fun i => (had i).2) hsp B (sat_of_equiv e hB)
  obtain rfl : S = S' := funext fun i => (hS i).unique (s1 i)
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] at s2
  apply Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective
  rw [← s2]
  unfold satTot

  rw [← Multiset.coe_mapAddMonoidHom (fun z : ℂˣ => (z : ℂ)), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  have hq : Ideal.absNorm w.asIdeal = normV w := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  simp only [Function.comp_apply, Units.val_mul, coe_qPow, Fin.revPerm_apply, Fin.val_rev, hq]
  congr 2
  rw [Nat.cast_sub k.2]
  push_cast
  ring
end
end
