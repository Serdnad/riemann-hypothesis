module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.ContinuousKap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.IsFrobSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.QuadMu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChebQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle003
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
private theorem val_of_norm
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
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log hy,
    WithZero.toAdd_unzero_eq_log hx, h2]
variable [Algebra K L]
private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem tendsto_under' :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
omit [Algebra K L] in
private theorem ev_notMem (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
variable (L) in
private noncomputable def cN (χ : HChar K) : HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
private theorem cN_loc (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (cN L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩
private theorem cN_val (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (cN L χ).UnrAt w ∧ (cN L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3
private theorem norm_infDiag (k : Lˣ) :
    GroundTheory.Global.ideleNorm K L (infDiag k) = infDiag (Units.map (Algebra.norm K : L →* K) k) := by
  refine Units.ext (Prod.ext (funext fun v => ?_) (Subtype.ext (funext fun v => ?_)))
  · have h1 := GroundTheory.Global.ideleNorm_fst (K := K) (infDiag k) v
    have h2 := GroundTheory.Global.ideleNorm_fst (K := K) (GroundTheory.Global.IdeleGroup.diagonal L k) v
    rw [GroundTheory.Global.ideleNorm_diagonal] at h2
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    exact h1.trans h2.symm
  · have h1 := GroundTheory.Global.ideleNorm_snd (K := K) (infDiag k) v
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    refine h1.trans (Finset.prod_eq_one fun w _ => ?_)
    exact map_one _
open Classical in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem emb_norm (φ : K →+* ℂ) (x : L) :
    φ (Algebra.norm K x) = ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ, ψ x := by
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have h := Algebra.norm_eq_prod_embeddings K ℂ x
  refine h.trans ?_
  refine Finset.prod_bij (fun σ _ => (σ : L →+* ℂ)) (fun σ _ => ?_) (fun a _ b _ e => AlgHom.coe_ringHom_injective e)
    (fun ψ hψ => ⟨⟨ψ, fun r => DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext σ.commutes⟩
private theorem norm_pos (k : Lˣ) (hk : ∀ φ : L →+* ℝ, 0 < φ (k : L)) (φ : K →+* ℝ) : 0 < φ (Algebra.norm K (k : L)) := by
  classical
  have h := emb_norm (Complex.ofRealHom.comp φ) (k : L)
  have h0 : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0 := fun ψ => (map_ne_zero ψ).2 k.ne_zero
  have h1 : ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = Complex.ofRealHom.comp φ,
      (ψ (k : L) / ((‖ψ (k : L)‖ : ℝ) : ℂ)) = 1 := by
    refine Finset.prod_involution (fun ψ _ => ComplexEmbedding.conjugate ψ) (fun ψ _ => ?_) (fun ψ _ hne e => hne ?_)
      (fun ψ hψ => ?_) fun ψ _ => star_star ψ
    · have : ((‖ψ (k : L)‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0 ψ
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, div_eq_one_iff_eq (mul_ne_zero this this)]
      push_cast; ring
    · have hr : ComplexEmbedding.IsReal ψ := ComplexEmbedding.isReal_iff.2 e
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
      exact div_self (Complex.ofReal_ne_zero.2 this.ne')
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext fun r => ?_⟩
      have e : ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ) := DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r
      show ComplexEmbedding.conjugate ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ)
      rw [ComplexEmbedding.conjugate_coe_eq, e, Complex.conj_ofReal]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun ψ _ => by simpa using h0 ψ),
    ← Complex.ofReal_prod] at h1
  have h2 : ((φ (Algebra.norm K (k : L)) : ℝ) : ℂ) = _ := h.trans h1
  rw [Complex.ofReal_inj.1 h2]
  exact Finset.prod_pos fun ψ _ => norm_pos_iff.2 (h0 ψ)
private theorem cN_alg {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos (cN L χ) fun ψ => a (ψ.comp (algebraMap K L)) := by
  classical
  intro k hk
  have e : (cN L χ).inf k = χ.inf (Units.map (Algebra.norm K : L →* K) k) := congrArg χ.1 (norm_infDiag k)
  rw [e, h _ (norm_pos k hk), ← Finset.prod_fiberwise (s := Finset.univ) (g := fun ψ : L →+* ℂ => ψ.comp (algebraMap K L))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [Units.coe_map, emb_norm, ← Finset.prod_zpow]
  exact Finset.prod_congr (by convert rfl) fun ψ hψ => by simp only [(Finset.mem_filter.1 hψ).2]
end
theorem UpperTheory.V.Sd.alg_restriction_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgRes := by
  intro P F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι κ ⟨hc, art, χ, a, ha, h1, h⟩
  obtain ⟨art', ha'⟩ := P.litN.aut.art E Ω
  have h1' := cN_alg (L := E) h1
  obtain ⟨μ, hμ, hL⟩ := ha'.exists_isLAdicOf ι h1'
  have hc' : Continuous (κ.comp (galEmb F E Ω)) := hc.comp (continuous_restrictScalarsHom F E Ω)
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ (cN E χ).UnrAt w ∧
      CharEig ι (κ.comp (res F Ω E)) w ((cN E χ).val w : ℂˣ) := by
    filter_upwards [(tendsto_under' (K := F) (L := E)).eventually
      ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l)), ev_notMem (K := E) l]
      with w ⟨hu, hl⟩ hl'
    have hf := normV_under (K := F) w
    obtain ⟨k1, k2⟩ := cN_val χ w _ hf hu
    refine ⟨hl', k1, ?_⟩
    rw [k2, Units.val_pow_eq_pow_val]
    refine (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 κ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => κ.comp (galEmb F E Ω) s) (f' := fun s => μ s)
    hc' hμ fun v hv _ A hA σ hσ => by
      obtain ⟨hl, hu, hE⟩ := not_not.1 hv
      have e := (hE A hA).2 σ hσ
      refine Units.ext ?_
      rw [hL.frob_unr ha' (Or.inl hl) hu hA hσ, ← e, ι.symm_apply_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
  have e : κ.comp (galEmb F E Ω) = μ := MonoidHom.ext fun s => congrFun key s
  rw [e]
  exact ⟨hμ, art', _, _, ha', h1', hL⟩
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Sd
section Hecke
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm
private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
private theorem alg_mul {ι : Qbar l ≃+* ℂ} {κ κ' : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (h : IsAlgChar ι κ) (h' : IsAlgChar ι κ') :
    IsAlgChar ι (κ * κ') := by
  obtain ⟨hc, art, χ, a, ha, h1, h2⟩ := h
  obtain ⟨hc', art', χ', a', ha', h1', h2'⟩ := h'
  obtain rfl : art = art' := GlobalTheory.ArtinUniq.globalArtin_unique F Ω art art' ha ha'
  exact ⟨hc.mul hc', art, _, _, ha, isAlgPos_mul h1 h1', h2.mul h2'⟩
private theorem alg_fin (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {φ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    (ho : IsOpen (φ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω))) : IsAlgChar ι φ := by
  obtain ⟨art, ha⟩ := H F Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (_root_.Formalism.ConjugateSelfDual.G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨continuous_of_isOpen_ker' φ ho, art, χ, 0, ha, isAlgPos_zero_of_orderDvd hpos h1, h2⟩
private theorem alg_cyc (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    IsAlgChar ι (cycBar F Ω l ^ j) := by
  obtain ⟨hc, χ, art, a, h⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic H F Ω l ι j (cycBar F Ω l ^ j)
    ⟨1, 1, le_rfl, fun _ _ => rfl, (mul_one _).symm⟩
  exact ⟨hc, art, χ, a, h⟩
end Hecke
theorem UpperTheory.V.Sd.alg_cyclotomic_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgCyc := by
  intro P F Ω _ _ _ _ _ l _ ι
  refine ⟨fun j χ ho => alg_mul (alg_cyc P.litN.aut.art ι j) (alg_fin P.litN.aut.art ι ho),
    fun _ _ h h' => alg_mul h h', ?_⟩
  rintro κ ⟨hc, art, χ, a, ha, h1, h2⟩
  exact ⟨hc.inv, art, _, _, ha, isAlgPos_inv h1, h2.inv⟩
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base
namespace UpperTheory.V.Sd.Tw
section
variable {Ω : Type} [Field Ω]
private theorem not_lt_of_coprime (A : ValuationSubring Ω) {q n : ℕ} (hq : A.valuation (q : Ω) < 1) (h : q.Coprime n) :
    ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : Ω) = (a : Ω) * q + (b : Ω) * n := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 a _ hq) (h1 b _ hn)
  rw [← e, map_one] at this
  exact lt_irrefl _ this
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem cls_frob {A : ValuationSubring Ω} {q N : ℕ} [NeZero N] (hq : A.valuation (q : Ω) < 1) (h : q.Coprime N)
    {t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : Chr.cls ℚ Ω N t = ZMod.unitOfCoprime q h := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 t _ fun ζ hζ => ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  refine eq_of_pow_eq_one A (not_lt_of_coprime A hq h) ?_ ?_
    (ht.2 ζ (valuation_eq_one_of_pow_eq_one A (NeZero.ne N) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
private theorem cyc_frob {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {q : ℕ} (hp : q.Prime) (hq : A.valuation (q : Ω) < 1)
    (h : q.Coprime l) {t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) = q := by
  haveI : Fact q.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω q A).1 fun hA => ((places ℚ Ω q A).2.1 hA).2 hq
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun hm =>
    not_lt_of_coprime A hq h (((places ℚ Ω l A).2.2.1 v hv).2 hm)
  have e : ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp fun n => cycZ_toZModPow_eq hl hv ht.2 n
  change ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = _
  rw [e, map_natCast]
private theorem continuous_cyc (l : ℕ) [Fact l.Prime] :
    Continuous fun t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω => ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) :=
  ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))
variable (K : Type) [Field K] [NumberField K] [Algebra K Ω]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_notMem [_root_.NumberField.IsTotallyComplex K] {c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]
private theorem exists_chi [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) (N : ℕ) [NeZero N] (hN : N = (discr K).natAbs) :
    (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω ∧ ∃ χ : (ZMod N)ˣ →* ℂˣ, χ ^ 2 = 1 ∧
      ∀ t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, t ∉ galOf ℚ K Ω → χ (Chr.cls ℚ Ω N t) = -1 := by
  classical
  have hker : (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω := fun s hs => quadMu K Ω hK s fun ζ hζ => by
    rw [← hN] at hζ
    rw [Chr.cls_spec N s ζ hζ, MonoidHom.mem_ker.1 hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
  let δ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* ℂˣ := MonoidHom.mk' (fun s => if s ∈ galOf ℚ K Ω then 1 else -1) fun a b => by
    by_cases ha : a ∈ galOf ℚ K Ω <;> by_cases hb : b ∈ galOf ℚ K Ω <;>
      simp [Subgroup.mul_mem_iff_of_index_two hi, ha, hb]
  have hδ : (Chr.cls ℚ Ω N).ker ≤ δ.ker := fun s hs => if_pos (hker hs)
  have hs := (Chr.clsOnto Ω N).1
  have e : ∀ t, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩ (Chr.cls ℚ Ω N t) = δ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  refine ⟨hker, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩, MonoidHom.ext fun u => ?_, fun t ht => (e t).trans (if_neg ht)⟩
  obtain ⟨t, rfl⟩ := hs u
  rw [MonoidHom.pow_apply, e]
  change (if t ∈ galOf ℚ K Ω then (1 : ℂˣ) else -1) ^ 2 = 1
  split_ifs <;> simp
private theorem ver_of_frob [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] (κ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ)
    (hκ : Continuous κ) (T : ℕ) (hT : T ≠ 0)
    (H : ∀ (q : ℕ) (A : ValuationSubring Ω) (t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (s : _root_.Formalism.ConjugateSelfDual.G K Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 →
      IsFrob (F := ℚ) A q t → t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t →
      (κ s : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1)
    (s : _root_.Formalism.ConjugateSelfDual.G K Ω) (t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (ht : t ∉ galOf ℚ K Ω) (hs : galEmb ℚ K Ω s = t * t) : κ s = -(cycBar ℚ Ω l t)⁻¹ := by
  obtain ⟨hemb, hopen, hi⟩ := galEmbTop ℚ K Ω
  have hsq : ∀ t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, ∃ s, galEmb ℚ K Ω s = t * t := fun t => by
    have := Subgroup.mul_self_mem_of_index_two (hi.trans hK) t
    rw [← range_galEmb] at this
    exact this
  choose g hg using hsq
  have hgc : Continuous g := hemb.continuous_iff.2 ((continuous_id.mul continuous_id).congr fun t => (hg t).symm)
  have hcl : IsClosed {t : _root_.Formalism.ConjugateSelfDual.G ℚ Ω | (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1} :=
    isClosed_eq ((Units.continuous_val.comp (hκ.comp hgc)).mul (continuous_cyc l)) continuous_const
  have key : (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1 := by
    by_contra hne
    obtain ⟨q, A, φ, hq, hqT, hA, hφ, h1, h2⟩ := ML.chebQ Ω _
      (hcl.isOpen_compl.inter ((galOf ℚ K Ω).isClosed_of_isOpen hopen).isOpen_compl) ⟨t, hne, ht⟩ T hT
    exact h1 (H q A φ (g φ) hq hqT hA hφ h2 (hg φ))
  rw [hemb.injective ((hg t).trans hs.symm)] at key
  rw [← mul_left_inj (cycBar ℚ Ω l t), neg_mul, inv_mul_cancel]
  exact Units.ext key
end
end UpperTheory.V.Sd.Tw
open UpperTheory.V.Sd.Tw in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Sd.twist_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Twist := by
  intro hP K Ω _ _ _ _ _ _ _ hK l hl hl2 hld ι c hc
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  set N := (discr K).natAbs with hN
  have hN3 : 3 ≤ N := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [Int.abs_eq_natAbs] at this
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hker, χ, hχ2, hχ⟩ := exists_chi (Ω := Ω) K hK N hN
  have hχ1 : χ (-1) = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.2.2.1 c hc]
    exact hχ c (cc_notMem K hc)
  obtain ⟨Y, a, τ, hYa, ha1, ha0, hYu, ⟨m, hm0, hml, hm⟩, hYv⟩ := hecke K hK l hl.out hl2 hld N hN3 χ hχ2 hχ1
  obtain ⟨art, hart⟩ : ∃ art : Ideles K →* Gab K Ω, IsGlobalArtin art := hP.litN.aut.art K Ω
  obtain ⟨κ, hκ, hL⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hYa)
  have hNd : ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → (N : 𝓞 K) ∉ v.asIdeal := fun v hv h => by
    apply hv
    rcases Int.natAbs_eq (discr K) with e | e
    · rw [e, Int.cast_natCast]
      exact h
    · rw [e, Int.cast_neg, Int.cast_natCast]
      exact neg_mem h
  have hnat : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ n : ℤ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn h => by
    have := (hw (n : 𝓞 K)).2 h
    exact hn (by simpa using this)
  have hnat' : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ n : ℕ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn => by
    simpa using hnat A w hw n (by simpa using hn)
  have hver := ver_of_frob K hK κ hκ (l * N) (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) fun q A t s hq hqT hA ht htK hs => by
    have hc' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqT
    have hql := hc'.coprime_mul_right_right
    have hqN := hc'.coprime_mul_left_right
    have hAN := not_lt_of_coprime A hA hqN
    obtain ⟨w, hw, hwq, hfr⟩ := inert K Ω hK q hq A hA (((Chr.clsFacts ℚ Ω N).2.2.2.2 A hAN).trans hker) t ht htK
    rw [hL.frob_unr hart (Or.inl (hnat' A w hw l (not_lt_of_coprime A hA hql))) (hYu w (hnat' A w hw N hAN)) hw (hfr s hs),
      hYv q hqN w hwq, ← cls_frob hA hqN ht, hχ t htK, cyc_frob hq hA hql ht]
    have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    simp [hq0]
  refine ⟨κ, hκ, ⟨art, Y, a, τ, hart, isAlgPos_of_isAlg hYa, hL, ha1, ha0, fun v hv => hYu v (hNd v hv)⟩,
    fun s s' h => ?_, hver, fun A hAl hAd s hs => ?_, m, hm0, hml, fun A hAl s hs => ?_⟩
  · have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
    have h1 : galEmb ℚ K Ω s * c ∉ galOf ℚ K Ω := fun h' =>
      cc_notMem K hc (((galOf ℚ K Ω).mul_mem_cancel_left (galEmb_mem ℚ K Ω s)).1 h')
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (cc_sq hc)
    have h3 : cycBar ℚ Ω l c = -1 := by
      have h4 : cycZ ℚ Ω l c = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm c.toRingEquiv from hc)
      change Units.map _ (cycZ ℚ Ω l c) = -1
      rw [h4]
      exact Units.ext (by simp)
    rw [← map_mul, hver (s * s') _ h1 (by rw [map_mul, h, h2]; simp only [mul_assoc]), map_mul, h3, mul_neg_one, inv_neg, neg_neg]
    rfl
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      exact (hL.unr_iff hart (Or.inl (hnat' A w hw l hAl)) hw).2 (hYu w (hNd w (hnat A w hw _ hAd))) s hs
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one, one_pow]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inl (hnat' A w hw l hAl)) hw _).1 ⟨s, hs, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, hm w x hx]
      simp
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
abbrev _root_.UpperTheory.V.Lev.fixedUnr_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedUnrAlt
end
end
