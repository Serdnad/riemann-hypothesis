module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hn : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      normV v = Ideal.absNorm v.asIdeal := fun v => by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hn, hn]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

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

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

theorem UpperTheory.galois_norm_compatibility_of_frobenius_restriction :
    UpperTheory.V.Af.Bc.FrobRes → UpperTheory.V.Af.Bc.NormVal → UpperTheory.V.Af.Bc.NormGal := by
  intro hR hV E Ω _ _ _ _ _ _ l _ ι χ μ ⟨_, art, n, ha, _, h⟩
  filter_upwards [(tendsto_under' (K := maximalRealSubfield E) (K' := E)).eventually
    ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l))] with w ⟨hu, hl⟩
  have hf := normV_under (K := maximalRealSubfield E) w
  obtain ⟨h1, h2⟩ := hV E χ w _ hf hu
  refine ⟨h1, ?_⟩
  rw [h2, Units.val_pow_eq_pow_val]
  refine (hR (maximalRealSubfield E) E Ω l ι w _ hf).2 μ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
  rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Pointwise

private theorem frob_of_smul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g σ : _root_.Formalism.ConjugateSelfDual.G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem one_lt_normV' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 1 < normV w := by
  simpa only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] using
    NumberField.HeightOneSpectrum.one_lt_absNorm w

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := by
    rw [normV, Nat.card_eq_fintype_card]
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

theorem UpperTheory.frobenius_sign_compatibility :
    UpperTheory.V.Af.Bc.SignFrob := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι δ hδ w hur A' hA'
  refine ⟨hur A' hA', fun σ' hσ' => ?_⟩
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hv : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hv hA'
  have hσ := frob_of_smul hσ'
  have e : δ σ' = δ (g⁻¹ * σ' * g) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  rw [map_inv, e]
  generalize g⁻¹ * σ' * g = σ at hσ
  split_ifs with hq
  · obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (res F Ω E φ) := by
      rw [← hq]
      exact ⟨hφ.1, hφ.2⟩
    have h1 := hur A hv _ (inv_mul_mem_Ine_of_isFrob hσ hφ')
    rw [map_mul, (hδ.1 _).2 ⟨φ, rfl⟩, mul_one, map_inv] at h1
    rw [h1]; simp
  · rcases hδ.2 σ with h1 | h1
    · exfalso
      obtain ⟨ψ, rfl⟩ := (hδ.1 σ).1 h1
      have hle : normV w ≤ normV (w.under (𝓞 F)) := by
        refine normV_le w (one_lt_normV' _) fun x => ?_
        rw [← hA]
        have hx : A.valuation (algebraMap E Ω x) ≤ 1 := by
          rw [A.valuation_le_one_iff]
          have hi : IsIntegral ℤ (algebraMap E Ω x) := x.isIntegral_coe.algebraMap
          obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
          rw [← hy]
          exact y.2
        have h2 := hσ.2 _ hx
        have h3 : res F Ω E ψ (algebraMap E Ω x) = algebraMap E Ω x := ψ.commutes x
        rw [h3] at h2
        simpa using h2
      refine hq (le_antisymm hle ?_)
      have h4 := one_lt_normV' w
      rw [normV_under' (K := F) w] at h4 ⊢
      refine Nat.le_self_pow (fun h0 => ?_) _
      rw [h0] at h4
      simp at h4
    · rw [h1]; simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem charpoly_smul_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (hM : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  have hc : Multiset.card L = Fintype.card ι := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hM, natDegree_multiset_prod_X_sub_C_eq_card]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem UpperTheory.frobenius_eigenvalues_twist :
    UpperTheory.V.Af.Bc.FrobTw := by
  intro F Ω _ _ _ _ l _ ι n r δ w B z hr hδ A hA
  obtain ⟨h1, h2⟩ := hr A hA
  obtain ⟨h3, h4⟩ := hδ A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [tw_val, h1 s hs, h3 s hs]
    simp
  · have e1 := h2 σ hσ
    have e2 := h4 σ hσ
    rw [← Matrix.charpoly_map] at e1 ⊢
    rw [← charpoly_smul_prod _ z B e1, tw_val, ← e2]
    congr 1
    ext i j
    simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.galoisRep_irreducibility_criterion :
    UpperTheory.V.Af.Bc.IrrBasic := by
  refine ⟨fun Γ Γ' k _ _ _ n r => ⟨fun φ h => ?_, fun h => ?_, fun δ h => ?_⟩, fun Γ k _ _ _ _ _ n r δ hr hδ => ?_⟩
  · exact ⟨h.1, fun _ _ _ => Submodule.mem_top, fun W hW hinv => h.2.2 W hW fun g v hv => hinv (φ g) v hv⟩
  · intro W hW
    rcases h.2.2 W le_top hW with rfl | rfl
    · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : k)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    intro W hW
    obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
    exact ⟨W', (key W').2 hW', hc⟩
  · obtain ⟨hr1, hr2⟩ := Units.continuous_iff.1 hr
    obtain ⟨hd1, hd2⟩ := Units.continuous_iff.1 hδ
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine (hd1.smul hr1).congr fun g => ?_
      exact (tw_val r δ g).symm
    · refine (hd2.smul hr2).congr fun g => ?_
      have := tw_val r δ g⁻¹
      simp only [map_inv] at this
      exact this.symm
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem adeleMap_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := by
  ext a : 1
  apply Prod.ext
  · funext w
    open scoped NumberField.LiesOver in
    change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
    rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  · apply FiniteAdeleRing.ext
    intro w
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w _ =
      GroundTheory.Global.SemiLocal.completionMap _ w _
    rfl

open scoped GroundTheory.Global.AdeleBaseChange in
private theorem ideleNorm_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, GlobalTheory.UnitaryHeckeBaseChange.toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul,
        adeleMap_eq, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

private theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log, nsmul_eq_mul, h2]

theorem UpperTheory.ideleNorm_local_compatibility :
    UpperTheory.V.Af.Bc.NormLoc := by
  intro E _ _ _ w x
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := maximalRealSubfield E) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := maximalRealSubfield E)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  refine ⟨_, ?_, val_of_norm _ w _ x hm'⟩
  rw [ideleNorm_eq]
  exact h
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf13.pow_cong A ha hb h m

private theorem dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (hg : g ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g : _root_.Formalism.ConjugateSelfDual.G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) : IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

private theorem key {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (f : ℕ)
    (hf : normV w = normV (w.under (𝓞 F)) ^ f) (A : ValuationSubring Ω) (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) :
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 F)) ∧ (∀ s ∈ Ine (F := E) A, res F Ω E s ∈ Ine (F := F) A) ∧
      ∀ φ : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob A (normV w) φ → ∃ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, IsFrob A (normV (w.under (𝓞 F))) σ ∧
        ∀ (C : Type) [Group C] (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* C), (∀ s ∈ Ine (F := F) A, r s = 1) → r (res F Ω E φ⁻¹) = r σ⁻¹ ^ f := by
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have hv : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  refine ⟨hv, fun s hs => ⟨hs.1, hs.2⟩, fun φ hφ => ?_⟩
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hv
  refine ⟨σ, hσ, fun C _ r hr => ?_⟩
  have hφ' : IsFrob (F := F) A (normV w) (res F Ω E φ) := ⟨hφ.1, hφ.2⟩
  rw [hf] at hφ'
  have h := hr _ (inv_mul_mem_Ine_of_isFrob hφ' (isFrob_pow hσ f))
  rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h
  rw [map_inv, map_inv, map_inv, h, inv_pow]

theorem UpperTheory.frobenius_power_compatibility :
    UpperTheory.V.Af.Bc.FrobRes := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι w f hf
  refine ⟨fun n r B h A hA => ?_, fun δ z h A hA => ?_⟩
  · obtain ⟨hv, hI, hF⟩ := key w f hf A hA
    obtain ⟨h1, h2⟩ := h A hv
    refine ⟨fun s hs => h1 _ (hI s hs), fun φ hφ => ?_⟩
    obtain ⟨σ, hσ, e⟩ := hF φ hφ
    have e1 := h2 σ hσ
    rw [MonoidHom.comp_apply, e _ r h1, Units.val_pow_eq_pow_val, ← Matrix.charpoly_map, Matrix.map_pow]
    rw [← Matrix.charpoly_map] at e1
    generalize (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).map ι.toRingHom = M at e1 ⊢
    have e2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n f M
    rw [e1, roots_multiset_prod_X_sub_C] at e2
    rw [← e2]
    exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  · obtain ⟨hv, hI, hF⟩ := key w f hf A hA
    obtain ⟨h1, h2⟩ := h A hv
    refine ⟨fun s hs => h1 _ (hI s hs), fun φ hφ => ?_⟩
    obtain ⟨σ, hσ, e⟩ := hF φ hφ
    rw [MonoidHom.comp_apply, e _ δ h1, Units.val_pow_eq_pow_val, map_pow, h2 σ hσ]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

open scoped Matrix in
private theorem UpperTheory.V.Af.Bc.eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod) :
    S = S.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  have h2 := h
  rw [← Matrix.charpoly_map] at h2
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M) (φ t) _ h2
  have h4 : (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm

theorem UpperTheory.frobenius_eigenvalues_dual :
    UpperTheory.V.Af.Bc.FrobDual := by
  intro F Ω _ _ _ _ _ l _ ι n r θ ⟨P, hP⟩ w hw B z hB hz
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have h1 := UpperTheory.V.Af.Bc.eig_dual ι.toRingHom (r σ⁻¹) P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hqC : (normV w : ℂ) ≠ 0 := by exact_mod_cast hq0
  have h3 := (hz A hA).2 σ hσ
  rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast] at h3
  set c : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = z * (c * c) := by
    rw [hcc, ← h3, inv_zpow, inv_mul_cancel_right₀ (zpow_ne_zero _ hqC)]
    rfl
  have hS : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    simp only [algSat, ← hc, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => c * a⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    have := a.ne_zero
    have := z.ne_zero
    field_simp
end
