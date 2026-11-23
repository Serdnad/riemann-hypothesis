module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle084
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle090
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    simp
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]

end Real

private theorem expo_intC {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (τ : E →+* ℂ) : expo χ τ = n τ := by
  refine (GlobalTheory.CuspRep.InfType.expo_of_infType E χ).1 n (fun k => h k fun φ => ?_) τ
  exact absurd (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (_root_.Formalism.ConjugateSelfDual.G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]

private theorem reg_shift {n : ℕ} {m : Multiset ℂ} (h2 : m.Nodup) (h3 : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2)
    {s : ℂ} (hs : ∃ k : ℤ, s = k) :
    (m.map (· + s)).Nodup ∧ ∀ z ∈ m.map (· + s), ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  obtain ⟨j, rfl⟩ := hs
  refine ⟨h2.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h3 y hy
  exact ⟨k + j, by push_cast; ring⟩

theorem UpperTheory.V.Af.twi :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.Twi := by
  rintro - F Ω _ _ _ _ _ l _ ι n r κ ⟨sat, inf, hc, hr, hA⟩ ⟨χ, -, art, a, ha, hχ, hL⟩
  rcases hc with ⟨_, π, rfl, rfl⟩ | ⟨_, π, rfl, rfl⟩
  · refine ⟨_, _, Or.inl ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hA art χ a κ ha hL⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 ⟨_, expo_intC hχ τ⟩⟩
  · refine ⟨_, _, Or.inr ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 (expo_intR hχ _)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host Neutral.B1
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open scoped Matrix

private theorem roots_stable {k : Type} [Field k] {n : ℕ} (f : k →+* ℂ) (M P : GL (Fin n) k) (t : kˣ)
    (h : (M : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) =
      (t : k) • (P : Matrix (Fin n) (Fin n) k)) (B : Multiset ℂ)
    (hB : (M : Matrix (Fin n) (Fin n) k).charpoly.map f = (B.map fun b => X - C b).prod) :
    B.map (fun b => f t * b⁻¹) = B := by
  set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ
  have hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0 := fun U => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero
  have h' : Nᵀ * Q * N = f t • Q := by
    have := congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [hQ]
  rw [← Matrix.charpoly_map, ← hN] at hB
  have hc : B.card = n := by
    have := congrArg natDegree hB
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod := fun x => by
    have := congrArg (eval x) hB
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.smul_one_eq_diagonal] using this
  have e0 : N.det = B.prod := by
    have := ev 0
    simp only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this
    rw [Multiset.prod_map_neg, hc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by simp)) this
  have hb : ∀ b ∈ B, b ≠ 0 := fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))
  have key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod := by
    intro x hx
    have e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) =
        (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q) := by
      rw [mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]
      abel
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      ev, ev, e0, Fintype.card_fin] at e2
    have e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod =
        (-x) ^ n * (B.map fun b => f t / x - b).prod := by
      rw [← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]
      refine congrArg _ (Multiset.map_congr rfl fun b h => ?_)
      have := hb b h
      simp only [Function.comp_apply]
      field_simp
      ring
    refine mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_
    rw [← hQ]
    linear_combination Q.det * e3 - e2
  have hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)
    have := key x hx
    simpa [eval_multiset_prod, Multiset.map_map] using this
  have := congrArg roots hp
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this

private theorem sat_stable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {θ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    (hr : DualTw r θ) {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {χ : HChar F} {a : (F →+* ℂ) → ℤ}
    (hχ : IsLAdicOf art ι χ a (θ * cycBar F Ω l ^ ((n : ℤ) - 1))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hu : χ.UnrAt w) {B : Multiset ℂˣ}
    (hB : FrobEig ι r w (algSat n (normV w) B)) : (B.map (·⁻¹)).map (· * χ.val w) = B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  obtain ⟨P, hP⟩ := hr
  have h1 := roots_stable ι.toRingHom _ P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 := hχ.frob_unr ha (Or.inl hw) hu hA hσ
  have h3 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hw hA hσ]
    simp
  have hq : (0 : ℝ) < normV w := by
    have : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h : 0 < normV w := by
      rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      exact zero_lt_one.trans this
    exact_mod_cast h
  set c : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hq, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]
    simp
  have h4 : ι ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c * c * (χ.val w : ℂˣ) := by
    have h5 := congrArg ι h2
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, h3, map_mul, map_zpow₀,
      map_natCast, map_inv₀, ι.apply_symm_apply, ← hcc] at h5
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, h5, inv_mul_cancel₀ (Units.ne_zero _)]
  refine Multiset.map_injective (f := fun α : ℂˣ => c * (α : ℂ))
    (fun x y e => Units.ext (mul_left_cancel₀ hc0 e)) ?_
  have h6 : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    change Multiset.map _ (B.bind fun a : ℂˣ => ({(a : ℂ)} : Multiset ℂ)) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [h6] at h1
  refine Eq.trans ?_ h1
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  change c * _ = ι _ * (c * _)⁻¹
  rw [h4]
  simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem UpperTheory.V.Af.selfDualR :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.SelfDualR := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ θ χ hr hχ
  have hd : π.IsSelfDualBy χ := by
    obtain ⟨-, art, a, ha, -, h2⟩ := hχ
    refine UpperTheory.satakePolarization_of_cuspidalTransfer H.toClassicalTheorems F n hn π χ ?_
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    filter_upwards [hπ.2, hl, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1] with w ⟨S, hS, hE⟩ hw hu
    refine ⟨hu, S, hS, ?_⟩
    conv_rhs => rw [← sat_stable hr ha h2 hw hu hE]
    simp [Multiset.map_map]
  refine ⟨hd, fun hs => ⟨UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel F Ω l ι χ _ hχ fun c c' hc hc' => ?_, hd⟩⟩
  simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, hs c c' hc hc', UpperTheory.cyclotomic_char_conj_invariant F Ω l c hc,
    UpperTheory.cyclotomic_char_conj_invariant F Ω l c' hc']
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem of_model (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hc : Continuous R) (hs : IsSSRep R) (H : ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ)
    (hr : Continuous r) (ha : AttC ι r π) (w) (σ) (hσ : π.IsLocComp w σ) : LocGlob ι r w σ := by
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => (H w σ hσ A h rc hrc).1 hw, hf⟩
  intro A h rc hrc
  obtain ⟨h1, h2⟩ := H w σ hσ A h rc hrc
  refine ⟨fun hw => (h1 hw).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], fun O _ _ _ Bw hj => ?_⟩
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype)
    (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype) p (fun g => hp g.1) (h2 O Bw hj).1
  exact ⟨h3.1, by rw [h3.2]; exact (h2 O Bw hj).2⟩

private theorem cls_char {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E)
    {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (h : ((CuspSub.triv E le_rfl).twist χ).IsLocComp w σ) (hχ) :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (χ.loc w) hχ := by
  obtain ⟨f, h0, hf⟩ := h
  have hop : ∀ g (x : ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V),
      ((CuspSub.triv E le_rfl).twist χ).locRep w g x = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • x := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_triv_twist, ← CuspSub.chiDet_locGL]
    simp [opMul, opTriv, opAdd]
  let L : ℂ ≃ₗ[ℂ] ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ _ (oneFn E 1) oneFn_ne_zero).trans ((CuspSub.triv E le_rfl).toTwist χ)
  let f' : σ.V →ₗ[ℂ] ℂ := L.symm.toLinearMap ∘ₗ f
  have hf' : ∀ g v, f' (σ.ρ g v) = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • f' v := fun g v => by simp [f', hf, hop]
  have h0' : f' ≠ 0 := fun h => h0 (LinearMap.ext fun v => L.symm.injective (by simpa [f'] using LinearMap.congr_fun h v))
  have hinj : Function.Injective f' := by
    rcases ((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f') (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢; rw [hf', hv, smul_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0'
  have hsurj : Function.Surjective f' := LinearMap.range_eq_top.1
    ((eq_bot_or_eq_top (LinearMap.range f')).resolve_left fun h => h0' (LinearMap.range_eq_bot.1 h))
  refine (IrrGL.of_eq_of (σ := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).ρ) (hs' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).smooth)
    (hi' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).irr)).2 ⟨.mk (LinearEquiv.ofBijective f' ⟨hinj, hsurj⟩) fun g => ?_⟩
  ext v
  exact hf' g v

private theorem rank_one (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {π : CuspSub K 1} (hreg : (CG.mk π).IsRegAlg) :
    ∃ R : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 1) (Qbar l), Continuous R ∧ IsSSRep R ∧ ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose m hm using (CG.isRegAlg_ofChar χ).1 hreg
  have hχ := GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo K χ m hm
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμ, hL⟩, -⟩ := hμ l ι χ m hχ
  have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
    fun g => rfl
  have hc : Continuous (GlobalTheory.TripleGal.rk1 μ) := by
    refine (Continuous.units_map _ ?_).comp hμ
    exact continuous_matrix fun i j => by
      fin_cases i; fin_cases j
      simpa using continuous_id'
  refine ⟨_, hc, fun W _ => ?_, fun w σ hσ A h rc hrc => ?_⟩
  · obtain ⟨W', hW⟩ := W.exists_isCompl
    refine ⟨W', fun g v hv => ?_, hW⟩
    have := W'.smul_mem (μ g : Qbar l) hv
    convert this using 1
    ext i
    simp [hval, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hcp := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have e0 : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
  rw [rec_algNorm hrc, e0, WD.lpTw_zero, cls_char χ hσ hcp.1]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hcp.1]
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ⟨?_, ?_⟩⟩
  · have h1 := isWDOf_wdOf (h := h) (r := GlobalTheory.TripleGal.rk1 μ) hw ι (Units.continuous_val.comp hc)
    rwa [wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (χ.loc w).comp a) fun _ => ha.smooth hcp.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h1
  · obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val))
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.litN.aut.chA K Ω l _ _ ⟨T⟩ ι art hart χ m μ hχ hμ hL w A h O Bw hj).1
  · exact Lev.SsCmp.of_eq (P.litN.aut.chW K Ω l _ _ (Loc.tiedP l) ι art hart χ m μ hχ hμ hL w A h O Bw hj _ hcp a ha)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatCsd :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CompatCsd := by
  intro PH F Ω _ _ _ _ _ _ l _ ι n hn r π hr hreg hd ha
  have P := PH.toClassicalTheorems
  rcases hn.eq_or_lt with rfl | hn
  · obtain ⟨R, hc, hs, H⟩ := rank_one (Ω := Ω) P ι hreg
    exact of_model P hc hs H hr ha
  · obtain ⟨R, hc, hs, Haw, Hab⟩ := P.ss F Ω l ι n hn π hd (P.litN.aut.coh F n (by omega) π hreg)
    refine of_model P hc hs (fun w σ hσ A h rc hrc => ⟨fun hw => Haw w hw A h rc hrc σ hσ, fun O _ _ _ Bw hj => ?_⟩) hr ha
    have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
    exact ⟨h1.1, h1.2 σ hσ rc hrc⟩

end
end

section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

private theorem regInf_iff {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) :
    RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
  refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩) (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
  rintro ⟨m, hm, h⟩
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
  exact h

private theorem regInf_iff_real {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (π : TR.CuspSub F n) :
    RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
  refine ⟨fun h v => ?_, fun h τ => h _⟩
  have := h v.embedding
  simpa only [InfinitePlace.mk_embedding] using this

theorem UpperTheory.V.Af.autBridge :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.AutBridge := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hC : ∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (regInf_iff π).1 hr, ha⟩
      · exact (not_both F h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (regInf_iff π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (not_both F hF h).elim
      · exact ⟨π, (regInf_iff_real π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (regInf_iff_real π).2 hr, ha⟩
  · rintro _ ⟨π, hr, -, ha⟩
    exact hC.2 ⟨π, hr, ha⟩
end
