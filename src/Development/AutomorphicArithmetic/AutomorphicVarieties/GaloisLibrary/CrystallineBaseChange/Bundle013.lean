module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle005
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle490
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 E), normV v = Ideal.absNorm v.asIdeal := by
    intro v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [e]
  exact (Ideal.map_symm _).symm

private theorem eventually_unr {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (χ : HChar F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

private theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ) {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ}
    (hz : (z' : ℂ) = σ z) (h : B₁.map (·⁻¹) = B.map (· * z⁻¹)) (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) : B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn,
      Real.rpow_natCast]
    push_cast
    rfl
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  have ae : ∀ B : Multiset ℂˣ, algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) :=
    fun B => by simp [algSat]
  simp only [ae] at e e₁
  clear ae
  generalize (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *
  have hs : σ c * σ c = c * c := by rw [← map_mul, hc, map_pow, map_natCast]
  have h1 : σ c ≠ 0 := (map_ne_zero σ).2 h0
  apply Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ))
    (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))
  have k1 := congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁
  have k2 := congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e
  have k3 := congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h
  simp only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k3.trans
    ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans (Multiset.map_congr rfl fun x _ => ?_))))))
  · simp [mul_comm]
  · simp [mul_comm]
  · rw [← hs]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz]
    field_simp

theorem UpperTheory.V.Br.conjPrime₂ :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.ConjP := by
  intro P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩
  have hreg := regAlg_of_infOf hm hinf
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π hreg σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hsat : ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ :=
    fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB
  refine ⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨r, wt, HT, H⟩ := P.litN.aut.gal K (AlgebraicClosure K) 2 ι n (by omega) π _ hreg hpol
  obtain ⟨μ, ⟨-, art, a, -, ha, -⟩, -⟩ := H.pol
  have hF : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h1 := (letI : Module.Free (maximalRealSubfield K) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
    omega
  obtain ⟨χ', hsg, hv⟩ := UpperTheory.V.Br.charConj _ hF χ a ha σ
  refine ⟨χ', fun v => (hsg v).trans (hpol.sign v),
    UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩
  have hM1 := eventually_notMem (K := K) hM
  filter_upwards [eventually_unr (K := K) χ, hM1,
    (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2
  obtain ⟨B, hB⟩ := satK P K n M π hfix w a1
  obtain ⟨B₁, hB₁⟩ := satK P K n M π hfix (cPl w) a2
  obtain ⟨B', hB', e⟩ := hsat w B hB
  obtain ⟨B₁', hB₁', e₁⟩ := hsat _ B₁ hB₁
  rw [normV_cPl] at e₁
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw
  obtain ⟨e5, e6⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1
  refine ⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_
    (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩
  rw [e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.V.Br.intP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, ⟨χ, hpol⟩, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (UpperTheory.V.Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open Filter Topology

private theorem lt_one_of_tendsto {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ] {x : R}
    (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) : (Valued.v x : Γ) < 1 := by
  by_contra hx
  have hx' : 1 ≤ (Valued.v x : Γ) := not_lt.1 hx
  have ho : {y : R | (Valued.v y : Γ) < 1} ∈ 𝓝 (0 : R) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨1, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hy
    simpa using hy
  obtain ⟨n, hn⟩ := (h.eventually ho).exists
  rw [map_pow] at hn
  exact absurd hn (not_lt.2 (one_le_pow₀ hx'))

theorem UpperTheory.V.Br.placeOf :
    UpperTheory.V.Br.PlaceOf := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ v w i hi hx
  have hle : v.asIdeal ≤ (w.under (𝓞 F)).asIdeal := by
    intro y hy
    have h1 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) < 1 := by
      have h3 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) =
        v.valuation F (y : F) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      rw [h3]
      exact (v.valuation_lt_one_iff_mem y).2 hy
    have h2 : Tendsto (fun n : ℕ => (algebraMap F (v.adicCompletion F) (y : F)) ^ n) atTop (𝓝 0) :=
      Valued.tendsto_zero_pow_of_v_lt_one h1
    have h4 : Tendsto (fun n : ℕ => (i (algebraMap F (v.adicCompletion F) (y : F))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      rw [map_zero] at this
      refine this.congr fun n => ?_
      simp
    have h5 := lt_one_of_tendsto (Γ := WithZero (Multiplicative ℤ)) h4
    rw [hx] at h5
    have h6 : (Valued.v (algebraMap K (w.adicCompletion K) (algebraMap F K y)) : WithZero (Multiplicative ℤ)) =
        w.valuation K (algebraMap F K y) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h6] at h5
    exact (w.valuation_lt_one_iff_mem (K := K) (algebraMap (𝓞 F) (𝓞 K) y)).1 h5
  have hv : w.under (𝓞 F) = v :=
    HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hle).symm
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w := exists_isPlaceOver Ω w
  refine ⟨hv, A, fun y => ?_, hA, fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, hi, hx⟩
  rw [← hv, IsScalarTower.algebraMap_apply F K Ω]
  exact hA (algebraMap (𝓞 F) (𝓞 K) y)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Br.recInv :
    UpperTheory.V.Br.RecInv := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' rc rc' hrc hrc' hy
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.matrix_map P.cont)
    · exact (Units.continuous_coe_inv.matrix_map P.cont)
  have hs : Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
    intro g
    refine ⟨Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom g, ?_⟩
    ext a b
    simp
  let τ : SmIrr (GL (Fin n) (v.adicCompletion F)) :=
    { V := σ'.V
      ρ := σ'.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)
      smooth := fun x => (σ'.smooth x).preimage hc
      irred := GlobalTheory.WDTransport.isIrreducible_comp σ'.ρ _ hs σ'.irred }
  have h1 : rc (algNorm σ) = rc (algNorm τ) :=
    Cq.recTransport hL F K Ω A v w h h' j i P n τ σ' (LinearEquiv.refl ℂ _) (fun _ _ => rfl) rc rc' hrc hrc' _ hy
  obtain ⟨_, _, _, -, HL⟩ := hrc
  have h2 := congrArg (fun x => IrrGL.nu x (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))) (HL.bij.1 h1)
  simp only [algNorm, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h2
  refine ⟨φ.toLinearEquiv, fun g x => ?_⟩
  exact LinearMap.congr_fun (φ.isIntertwining' g) x
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Br.wdAway :
    UpperTheory.V.Br.WdAway := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι A v w h h' i hP hl hl' n r x y hx hy
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have hd1 : ∀ σ, deg (c.symm σ) = deg σ := fun σ => by
    rw [← hdegc, MulEquiv.apply_symm_apply]
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have key : ∀ σ : Weil h', ((c.symm σ : Weil h) : G F Ω) = Bc.res F Ω K (σ : G K Ω) := fun σ =>
    AlgEquiv.ext fun z => (hc (c.symm σ) σ).mpr (c.apply_symm_apply σ) z
  have hres : Continuous (Bc.res F Ω K : G K Ω →* G F Ω) := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro U' hU'
    obtain ⟨U, hU, hU1, H⟩ := GlobalTheory.WeilTransport.conj_nhds K Ω F Ω (RingEquiv.refl Ω) U' hU'
    exact Filter.mem_map.mpr (Filter.mem_of_superset (hU.mem_nhds hU1) fun σ hσ => H σ hσ _ fun z => rfl)
  have hmem : ∀ σ : Ine (F := K) A, Bc.res F Ω K (σ : G K Ω) ∈ Ine (F := F) A := fun σ => by
    have h1 : ((c.symm (ineIncl h' σ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, hd1, deg_ineIncl]
    rwa [key] at h1
  let d : Ine (F := K) A →* Ine (F := F) A :=
    ((Bc.res F Ω K).comp (Ine (F := K) A).subtype).codRestrict _ hmem
  have hdc : Continuous d := (hres.comp continuous_subtype_val).subtype_mk _
  have hds : Function.Surjective d := fun τ => by
    have h1 : ((c (ineIncl h τ) : Weil h') : G K Ω) ∈ Ine (F := K) A := by
      rw [← deg_eq_zero_iff, hdegc, deg_ineIncl]
    refine ⟨⟨_, h1⟩, Subtype.ext ?_⟩
    have h2 := key (c (ineIncl h τ))
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx
  have hφ' : deg (c φ) = 1 := by rw [hdegc, hφ]
  have hine : ∀ g : Weil h', d (inePart hφ' g) = inePart hφ (c.symm g) := fun g => by
    refine Subtype.ext ?_
    have h2 := key (((c φ) ^ deg g)⁻¹ * g)
    rw [map_mul, map_inv, map_zpow, MulEquiv.symm_apply_apply, ← hd1] at h2
    refine Eq.trans ?_ h2.symm
    rw [hd1]; rfl
  have hmat : ∀ g : Weil h', wdMat (t.comp d) hφ' (r.comp (Bc.res F Ω K)) N g =
      wdMat t hφ r N (c.symm g) := fun g => by
    rw [wdMat, wdMat, key, ← hine]; rfl
  let b := GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 a
  have hb : IsWDOf ι (r.comp (Bc.res F Ω K)) (WD.mk b) := by
    refine ⟨t.comp d, ⟨ht.1.comp hdc, ht.2.comp hds⟩, c φ, hφ', N, b, ?_, ?_, rfl⟩
    · obtain ⟨h1, U, hU, H⟩ := hN
      exact ⟨h1, U.comap d, hU.preimage hdc, fun σ hσ => H (d σ) hσ⟩
    · refine ⟨ha.1, fun σ => ?_⟩
      simp only [hmat]
      exact ha.2 (c.symm σ)
  rw [hy.unique hl' hb]
  refine ⟨n, a, b, rfl, rfl, rfl, fun σ σ' hσ => ?_⟩
  rw [← (hc σ σ').mp hσ]
  exact congrArg a.ρ (c.symm_apply_apply σ).symm
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.selfIso :
    UpperTheory.V.Br.SelfIso := by
  intro H F _ _ _ a ha π η h2 h
  have hd : ∀ z, TR.dchi η z = 0 := fun z => by
    have e := TR.dchi_mul η η z
    rw [← pow_two, h2, TR.dchi_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  obtain ⟨S, hS⟩ : π.Iso (π.twist η) := H F a ha _ _ (by
    filter_upwards [h] with w ⟨hu, B, hB, hE⟩
    exact ⟨B, hB, hE ▸ hB.twist hu⟩)
  have key : ∀ o φ, (S.trans (π.toTwist η).symm) (π.op o φ) =
      ((TR.opMul η o : ℂˣ) : ℂ) • π.op o ((S.trans (π.toTwist η).symm) φ) +
        TR.opAdd η o • (S.trans (π.toTwist η).symm) φ := fun o φ => by
    apply (π.toTwist η).injective
    rw [← TR.CuspSub.op_toTwist]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hS]
  refine ⟨S.trans (π.toTwist η).symm, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  all_goals rw [key]; simp [TR.opMul, TR.opAdd, hd]
end
