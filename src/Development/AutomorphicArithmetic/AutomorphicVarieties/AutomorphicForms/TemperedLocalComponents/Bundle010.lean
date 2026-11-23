module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix

private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm

private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {θ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    {c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem UpperTheory.V.Af.selfDualC :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.SelfDualC := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ χ μ hμ c P hc hP
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk F n hn π _ ?_
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have h2 := (conjSrc_injective (IsCMField.complexConj F).toRingEquiv).tendsto_cofinite.eventually hπ.2
  filter_upwards [Bc.normGal F Ω l ι χ μ hμ, hπ.2, h2, hl] with w ⟨hu, he⟩ ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩ hw
  exact ⟨hu, B, B', hB, hB', frob_dual hc hP hw hF hF' he⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem galRepOfR_iso (P : Hypotheses₂) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {π : TR.CuspSub F n}
    {r r' : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRepOfR π ι r wt HT)
    (hs : IsSSRep r') (hi : RepIso r r') : IsGalRepOfR π ι r' wt HT := by
  obtain ⟨p, hp⟩ := id hi
  refine ⟨continuous_of_iso H.cont hi, hs, fun w hw A h rc hrc σ hσ => ?_, fun w hw A h => ?_, H.weights, H.weights_sym,
    fun Q AI hT w A h O _ _ _ Bw hj => ?_⟩
  · exact (H.away w hw A h rc hrc σ hσ).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right]
  · obtain ⟨x, h1, h2⟩ := H.pure w hw A h
    exact ⟨x, h1.of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := H.above Q AI hT w A h O Bw hj
    have hc : ∀ g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A), r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype g =
        p * r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype g * p⁻¹ := fun g => hp g
    obtain ⟨k1, k2, -, k4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l Q F Ω O _ Bw n _ _ p hc
    refine ⟨k1 h1, fun τ LL' τ' hτ => k4 τ _ (h2 τ LL' τ' hτ), fun σ hσ hI => ⟨isSstAt_conj Q Bw p hc (h3 σ hσ hI).1,
      fun rc hrc => ?_⟩, fun σ hσ hS => k2 (h4 σ hσ hS)⟩
    obtain ⟨T⟩ := hT
    exact (GlobalTheory.PstConj.main F Ω l ι n Q AI ⟨T⟩ w A h O Bw hj _ _ p hc
      (P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val)) h1)).2.trans
      ((h3 σ hσ hI).2 rc hrc)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.realExistence_from_published :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.ExR := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := P.galR F Ω l ι n hn π χ hreg hpol
  have key : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι r w (algSat n (normV w) B) := fun w hw B hB => by
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
    exact satFrob P F Ω l ι n r H.cont w hw σ B (((satLoc P F n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc σ hσ
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRepOfR_iso P H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (satLoc P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine isoOfFrob P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩

theorem UpperTheory.V.Af.exR :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.ExR := fun PH => UpperTheory.V.Af.realExistence_from_published PH.toClassicalTheorems

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp

theorem UpperTheory.V.Af.intK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, hdual, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hdual⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
end
