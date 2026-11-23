module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle074
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle082
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle059
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsContragredientCuspSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PAlgType
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd
private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i
private theorem transport_rho {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {n : ℕ} (a : WDRep h W) (b : Basis (Fin n) ℂ W) (σ : ↥(Weil h))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : LinearMap.toMatrix b b (a.ρ σ) = X) :
    (a.transport b.equivFun).ρ σ = Matrix.toLin' X := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  change b.equivFun (a.ρ σ (b.equivFun.symm (b.equivFun x))) = _
  rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, ← hX]
  exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ σ) x).symm

theorem UpperTheory.V.Af.weil_deligne_above_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAbove := by
  rintro - F Ω _ _ _ _ _ l _ - ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp hor
  have hκc := cont_diag hr hfl
  obtain ⟨L, ρ, κL, χL, hV, e, htri, hκ, hχL⟩ := UpperTheory.galois_representation_model_over_finite_extension F Ω l ι n r w A h O Bw hj κ χ
    (fun i => UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ (hχ i)) hfl hp
  obtain ⟨-, hcyc, hK⟩ := UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj
  obtain ⟨K', hK'⟩ := hK M hM
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => κ i * ε ^ (-m i)
  let μ : ↥(Weil h) → Fin n → ℂ := fun σ i => ((normV w : ℕ) : ℂ) ^ (m i * deg σ) * ι (ψ i (inc σ) : Qbar l)
  have hεc : Continuous fun s => (ε s : Qbar l) := by
    have h0 : Continuous fun g : GQ l => (((Loc.PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
      obtain ⟨hc, -, hq⟩ := Loc.cycFacts l l
      simp only [hq]
      have h0 : Continuous fun g : GQ l => ((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) := Units.continuous_val.comp hc
      exact continuous_subtype_val.comp h0
    exact ((continuous_algebraMap ℚ_[l] (Om l)).comp (h0.comp (continuous_subtype_val.comp Bw.e_cont))).congr
      fun s => hcyc L s
  have hψc : ∀ i, Continuous fun s => (ψ i s : Qbar l) := fun i => by
    refine ((hκc i).mul (hεc.zpow₀ (-m i) fun s => Or.inl (Units.ne_zero _))).congr fun s => ?_
    simp [ψ]
  haveI := hV.finite
  have T := UpperTheory.weilDeligne_triangularizable F Ω l ι w A h O Bw hj L n _ ρ κL μ htri (fun i hi σ y => by
    refine (UpperTheory.cyclotomicWeilChar_properties F Ω l ι w A h O Bw hj L (κL i) (χL i) (m i) ?_ ⟨K', fun g hg => ?_⟩ (fun g hg => ?_) hi σ y).trans ?_
    · refine ((hκc i).comp Bw.e_symm_cont).congr fun g => ?_
      rw [Function.comp_apply, ← hκ, MulEquiv.apply_symm_apply]
    · obtain ⟨s, rfl⟩ := Bw.e.surjective g
      refine Units.ext (Subtype.ext ?_)
      rw [hχL, hχ i s (hK' s hg)]
      rfl
    · obtain ⟨s, rfl⟩ := GlobalTheory.PstLaws.exists_ine_of_fix Bw h hj g hg
      refine Units.ext (Subtype.ext ?_)
      have h1 := congrArg Units.val (hI i (inc (ineIncl h s)) s.2)
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ← hκ, ← hχL, ← hcyc L] at h1
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      exact h1.trans (by congr 1)
    · congr 3
      have h1 : (ψ i (inc σ) : Qbar l) = (κ i (inc σ) : Qbar l) * (cycBar F Ω l (inc σ) : Qbar l) ^ (-m i) := by
        simp [ψ, ε]
      rw [h1, ← hκ, ← hcyc L, Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      congr 1) hV
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hN : wdN (Loc.PP l) ι ρ = 0 := by
    rcases hor with hne | ⟨O', _, _, _, Bw', hj', hpc⟩
    · by_contra h0
      obtain ⟨i, j, hij⟩ := UpperTheory.weilDeligne_monodromy_upperTriangular ℂ _ _ n _ _ _ μ (wdRho_wdN (Loc.PP l) ι Bw h hj ρ) T h0
      obtain ⟨ha, h1⟩ := UpperTheory.continuous_character_compact_unit_values F Ω l ι w A h (hj.mem_placesOver h) (ψ i * (ψ j)⁻¹) (1 + m j - m i)
        (by
          refine ((hψc i).mul ((hψc j).inv₀ fun s => Units.ne_zero _)).congr fun s => ?_
          simp) (fun σ => by
          have h2 := hij σ
          have h3 : ι (ψ j (inc σ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
          have h4 : ((normV w : ℕ) : ℂ) ^ (m i * deg σ) ≠ 0 := zpow_ne_zero _ hq
          change ι ((ψ i (inc σ) * (ψ j (inc σ))⁻¹ : (Qbar l)ˣ) : Qbar l) = _
          rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, sub_mul, add_mul, one_mul, zpow_sub₀ hq,
            zpow_add₀ hq, mul_inv_eq_iff_eq_mul₀ h3, div_mul_eq_mul_div, eq_div_iff h4, mul_comm, mul_assoc]
          exact h2)
      refine hne i j ?_
      have h5 : ψ i = ψ j := mul_inv_eq_one.mp h1
      have h6 : -m j = 1 + -m i := by omega
      simp only [ψ] at h5
      rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
      exact mul_right_cancel h5
    · have hc : Continuous fun g : ↥(Dec (F := F) A) =>
          ((r.comp (Dec (F := F) A).subtype g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
        Units.continuous_val.comp (hr.comp continuous_subtype_val)
      have hp' := GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding l _ _ (Loc.tiedP l) F Ω A O O' Bw Bw' hj hj' n _ hc hp
      have h1 := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw' h hj' (Loc.PP l) ι _ hp').2 hpc
      rw [← GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding l _ _ (Loc.tiedP l) ι F Ω A w O O' Bw Bw' h hj hj' n _ hc hp hp', e] at h1
      exact (mono0_wdPst ι Bw h hj hV).1 h1
  obtain ⟨b₀, hb₀⟩ := T
  obtain ⟨b, hb⟩ := UpperTheory.tridiagonal_weil_deligne _ ↥(Ine (F := F) A) n ((wdRho (Loc.PP l) ι Bw h hj ρ).comp (ineIncl h))
    (fun s => μ (ineIncl h s)) (isSmooth_wdRho (Loc.PP l) ι Bw h hj ρ).finite_range
    ⟨b₀, fun s => hb₀ (some (ineIncl h s))⟩
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), (wdRep (Loc.PP l) ι Bw h hj ρ).transport b.equivFun,
    fun i s hs => ?_, ?_, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [e, wdPst_of_isPst ι Bw h hj hV]
    exact (WD.sound (WDRep.iso_transport _ _)).symm
  · simp [WDRep.transport, hN]
  · have h1 : μ (ineIncl h s) = fun i => ι (χ i s : Qbar l) := funext fun i => by
      have h2 := hI i (inc (ineIncl h s)) s.2
      have h3 : ψ i (inc (ineIncl h s)) = χ i s := by
        have h6 : κ i (inc (ineIncl h s)) = cycBar F Ω l s ^ m i * χ i s := h2
        have h7 : ε (inc (ineIncl h s)) = cycBar F Ω l s := rfl
        simp only [ψ, MonoidHom.mul_apply, MonoidHom.zpow_apply]
        rw [h6, h7, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      simp [μ, h3]
    have h4 := (hb s).trans (congrArg Matrix.diagonal h1)
    have h5 : LinearMap.toMatrix b b ((wdRep (Loc.PP l) ι Bw h hj ρ).ρ (ineIncl h s)) =
        Matrix.diagonal fun i => ι (χ i s : Qbar l) :=
      (congrArg (LinearMap.toMatrix b b) (wdRep_ineIncl (Loc.PP l) ι Bw h hj ρ s)).trans h4
    exact transport_rho (wdRep (Loc.PP l) ι Bw h hj ρ) b (ineIncl h s) _ h5
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]
theorem UpperTheory.satake_polarization_real_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.Sol.PolSatR := by
  intro H F _ _ _ n hn π ψ h
  obtain ⟨π₁, h₁, -⟩ := UpperTheory.exists_contragredient_cuspSub F n π
  obtain ⟨B, hl, hr', hf, hc, hX⟩ := H.gkR F n π
  refine isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)
  filter_upwards [h] with w ⟨hu, S, hS, hE⟩
  refine ⟨S, hS, ?_⟩
  have e : (S.map (·⁻¹)).map (· * ψ.val w) = S := by
    rw [hE, Multiset.map_map]
    simp
  exact e ▸ (hasSat_invT h₁ hS).twist hu
end
end

section




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
theorem UpperTheory.V.Sd.twist_real_selfDual :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.TwR := by
  rintro - F Ω _ _ _ _ _ _ l _ ι n r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA⟩
  exact ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
private theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp
private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩
theorem UpperTheory.V.Sd.twist_conjugate_selfDual :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.TwC := by
  intro _ F Ω _ _ _ _ _ _ l _ ι n r κ ⟨_, art, χ, a, hart, hpos, hL⟩ ⟨π, hreg, hatt⟩
  exact ⟨π.twist χ, regAlg_twist hreg (isAlg_of_pos hpos),
    UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL⟩
end
end

section




section
noncomputable section
open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host
namespace UpperTheory.V.Sd.Wc
private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp
private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)
end UpperTheory.V.Sd.Wc
open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
namespace UpperTheory.GalN.V
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
theorem mod0'_alt (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) := h.1
theorem witAQ_of_isModularA (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : Continuous W) (_ : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (_ : 1 ≤ e)
    (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : _root_.UpperTheory.V.Z.Win.WitAQ ι W := h.2
end
theorem adm2B_of_adm2B (_ : _root_.UpperTheory.V.Af.Hypotheses') (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (_ : l ≠ 2) (ι : Qbar l ≃+* ℂ) (e M : ℕ) (_ : 1 ≤ e) (ρ : G K Ω →* GL (Fin 3) (Qbar l))
    (h : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ) : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ := h
end UpperTheory.GalN.V
end
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
namespace AlgType
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]
end AlgType
open AlgType in
theorem algType_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') : AlgType := by
  intro K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j
  have H : Good art ι a κ := ⟨Y, h1, h2⟩
  have H1 : Good art ι (fun _ => 1) (cycBar K Ω l) := good_cyc ha ι
  have H0 : Good art ι 0 1 := good_one H
  have key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j) := by
    intro j
    induction j with
    | zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm
    | succ j ih =>
      exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring)
        (pow_succ _ _).symm
  have key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j) := by
    intro n
    induction n with
    | zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)
    | succ n ih =>
      refine good_cong (good_mul ih H) (funext fun e => ?_) ?_
      · simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring
      · rw [pow_succ]
        exact mul_right_comm _ _ _
  exact key n
end UpperTheory.V.Cu2
end
end
end
