module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle680
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle737
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section

open GlobalTheory.SplitPts

variable {L : Type} [Field L] [NumberField L]

private theorem ic_mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h

variable [IsCMField L] {n : ℕ}

private theorem ic_sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc

private theorem ic_cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl

end

theorem UpperTheory.mem_maximalCompact_of_under_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n) (w w' : Plc E), w'.under (𝓞 (Lp E)) = w.under (𝓞 (Lp E)) → cLoc w x ∈ KO (w.adicCompletion E) (Fin n) → cLoc w' x ∈ KO (w'.adicCompletion E) (Fin n) := by
  intro E _ _ _ n x w w' h hx
  rcases ic_sameOver h with rfl | rfl
  · exact hx
  · rw [ic_cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.2 j i)))
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.1 j i)))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω), (∀ v, (s.w v).under (𝓞 (Lp L)) = v) ∧ ∀ w : Plc L, Dec (F := Lp L) (s.A (w.under (𝓞 (Lp L)))) ≤ (W.resP L Ω).range → IsSplitAt w := by
  intro l _ L Ω _ _ _ _ _ _ s
  obtain ⟨_, _, _, _, w, A, hAw, hAv, _⟩ := s
  refine ⟨fun v => ?_, fun w' hw' => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (hAv _) hw' w' rfl⟩
  have h1 := hAw v
  have h2 := hAv v
  apply HeightOneSpectrum.ext
  ext x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← h1 (algebraMap _ _ x), ← h2 x]
  have hx : ((algebraMap (𝓞 (Lp L)) (𝓞 L) x : 𝓞 L) : L) = algebraMap (Lp L) L (x : Lp L) := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.LocGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.twist_local_components_compatible :
    TwistLoc := by
  intro E _ _ _ a P t w ρ hρ
  refine ⟨_, hρ.twist (GlobalTheory.HeckeGal.Model.absPow E t), ?_⟩
  refine (GlobalTheory.LocGL.IrrGL.tw_of ρ.ρ ρ.smooth ρ.irred _
    (isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E t) w)).symm.trans ?_
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E t) w
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one

private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩

private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end UpperTheory.V.Af.Gu

theorem UpperTheory.total_frobenius_compatibility :
    HypothesesH → FrobTot := by
  intro P F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  have hrec : IsRec h rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc
  have hx := (H A h rc hrec).1 hl
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hsp := totPar_spec hrec n c a d ρ S hS
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm

end
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h)
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.total_reciprocity :
    HypothesesH → RecTot := by
  intro H E Ω _ _ _ _ _ _ n c a d hn P w ρ σ _ hP hS τ e A h rc hrc
  have L := H.litN.loc
  have h1 := GlobalTheory.FormDict.RecTLaws.locProd_eq hrc hn σ τ e
  have h2 : ∀ i, rc (cls (ParLaws.toRep (σ i))) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cls (ParLaws.toRep (ρ i)))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i => by
    have hd : ∑ _ : Fin (d i), a i = d i * a i := by simp
    exact GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos (a i) (d i) _ hd (ρ i) (σ i)
      (hS i).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E (a i) (P i) w (ρ i) (hP i))
      (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd (ρ i) (σ i) (hS i).2.2)
  rw [rec_algNorm hrc]
  change _ = (rc (cls (ParLaws.toRep τ))).lpTw _
  rw [h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC

private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]

private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]

theorem UpperTheory.irreducible_case :
    HypothesesH → IrrCase := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m H hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hn
  subst hn'
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (GlobalTheory.ContraPair.dualIsConjBy_one (P 0)).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E _ (P 0) 1 (by simpa only [inv_one, CuspSub.twist_one] using PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) ((GlobalTheory.GalOfCusp.isConjDualBy_one (P 0)).2 (H.csd 0))),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw⟩
  obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn1 π hπ τ
  rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
  refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
  rw [infOfWeight, Multiset.mem_map] at hz
  obtain ⟨j, -, rfl⟩ := hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst

private theorem map_sum' {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
    (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_sum {L : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {r₂ : ↥Gw →* GL (Fin b) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw r' L r₂) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') L (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) :=
  ⟨h₁.1, by rw [map_sum', h₁.2, h₂.2]⟩

private theorem dR_sum (h : IsdRAt (UpperTheory.V.Loc.PP l) Bw r) (h' : IsdRAt (UpperTheory.V.Loc.PP l) Bw r') :
    IsdRAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨_, _, model_sum n₁ n₂, (GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b _ _).1.2
    ⟨(n₁.isdRAt_iff _).1 h, (n₂.isdRAt_iff _).1 h'⟩⟩

private theorem jumps_sum {τ : E →+* Om l} {J J' : Multiset ℤ}
    (h : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r τ J) (h' : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r' τ J') :
    IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') τ (J + J') := by
  obtain ⟨L₁, r₁, m₁, d₁, τ₁, t₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, d₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  have t : IsInduced Bw τ (LL' := supExt L₁ L₂) ((IntermediateField.inclusion l₁).comp τ₁) := t₁
  have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b
    (mapRep (IntermediateField.inclusion l₁).toRingHom r₁) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
  refine ⟨_, _, model_sum n₁ n₂, S.1.2 ⟨(n₁.isdRAt_iff _).1 ⟨_, _, m₁, d₁⟩, (n₂.isdRAt_iff _).1 ⟨_, _, m₂, d₂⟩⟩,
    _, t, fun c => ?_⟩
  rw [S.2, ← h.count_eq _ n₁ t, ← h'.count_eq _ n₂ t, Multiset.count_add, Nat.cast_add]

end

theorem UpperTheory.sum_hodge_tate :
    SumHT := by
  intro E Ω _ _ _ _ _ l _ a b r r' _ _ HT HT' H H' w A hA O _ _ _ Bw hj
  obtain ⟨d, J⟩ := H w A hA O Bw hj
  obtain ⟨d', J'⟩ := H' w A hA O Bw hj
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e]
  exact ⟨dR_sum d d', fun τ L τ' t => jumps_sum (J τ L τ' t) (J' τ L τ' t)⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.compatible_polarization_of_link :
    HypothesesH → CompatCsd → SatLink → CompatPol := by
  intro PH hC hS E Ω _ _ _ _ _ _ l _ ι a ha P χ ξ m hreg hpol hξ hd σ hσ
  have Pr := PH.toClassicalTheorems
  obtain ⟨r, wt, HT, H⟩ := (GlobalTheory.T.local_global_of_gelfand_kazhdan Pr.litN.aut.gk).2 Pr.litN.aut.gal E Ω l ι a ha P χ hreg hpol
  have hatt : AttC ι r P := by
    refine ⟨H.ss, (((hS E a P).2).and (eventually_not_mem E l)).mono ?_⟩
    rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, satFrob Pr E Ω l ι a r H.cont w hw (σ w) B (((hS E a P).1 w _ (hσ w) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc _ (hσ w)⟩
  obtain ⟨art, hart⟩ := Pr.litN.aut.art E Ω
  obtain ⟨μ, hμc, hμ⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hξ)
  have hL := hC E Ω l ι a ha (tw r μ) (P.twist ξ) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ H.cont hμc) (regAlg_twist hreg hξ) hd
    (Cq.attTwist E Ω l ι a r P hatt art ξ m μ hart hμ)
  obtain ⟨T⟩ := Loc.tiedP l
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w A h O _ _ _ Bw hj => ?_, fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩⟩,
    H.weights⟩
  · exact ⟨(H.above _ _ ⟨T⟩ w A h O Bw hj).deRham, (H.above _ _ ⟨T⟩ w A h O Bw hj).jumps⟩
  · exact H.away w hw A h rc hrc _ (hσ w)
  · have hpst : IsPstAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
      Pr.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val))
        (H.above _ _ ⟨T⟩ w A h O Bw hj).deRham
    obtain ⟨c1, c2⟩ := (hL w _ ((hσ w).twist ξ) A h rc hrc).2 O Bw hj
    exact ⟨hpst, Lev.untwistS Pr.litN.aut.chA Pr.litN.aut.chW Pr.litN.aut.berger E Ω l ι a r H.cont art ξ m μ hart
      (isAlgPos_of_isAlg hξ) hμc hμ w A h O Bw hj hpst c1 (σ w) rc hrc c2⟩
end
