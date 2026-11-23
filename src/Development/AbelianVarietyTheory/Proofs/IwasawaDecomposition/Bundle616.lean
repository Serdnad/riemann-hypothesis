module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle008
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem iota_starProjection_Qsp (D : D7) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (hF : F ∈ D.what₂.V0 μ) :
    D.what₂.iota μ ((D.what₂.Qsp μ).starProjection F) = D.what₂.iota μ F := by
  set a := (D.what₂.Usp μ).starProjection F with ha
  have haU : a ∈ D.what₂.Usp μ := Submodule.starProjection_apply_mem _ _
  have hb : F - a ∈ D.what₂.Qsp μ := ⟨Submodule.sub_mem _ hF haU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have haQ : (D.what₂.Qsp μ).starProjection a = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Submodule.mem_orthogonal _ _).2 fun q hq => Submodule.inner_left_of_mem_orthogonal haU hq.2
  have e : (D.what₂.Qsp μ).starProjection F = F - a := by
    have h := map_add (D.what₂.Qsp μ).starProjection a (F - a)
    rw [add_sub_cancel, haQ, zero_add, Submodule.starProjection_eq_self_iff.2 hb] at h
    exact h
  rw [e, map_sub, LinearMap.mem_ker.1 haU.2, sub_zero]

theorem zeTied_of_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → D.BuRational → ZetaCompatible D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hP hH hB u μ c hfac hnz
  refine Y.ze u μ c hfac hnz ?_
  by_cases hU : Used0 D μ
  swap
  · exfalso
    obtain ⟨φ, x, hx, hne⟩ := hnz
    apply hne
    rw [hfac φ x hx, Y.junk μ hU, LinearMap.zero_apply, (D.Bu_linR u φ).map_zero, mul_zero]
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨Y.tupT μ, Y.tupTie μ hU⟩
  have hRS := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH).1
  have hFo := Y.formsA t
  have hR : LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin = LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin :=
    GlobalTheory.range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E _ _ _ _ _
  have hmem : ∀ f, Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) ∈ D.what₂.V0 (Y.tup t) := by
    intro f
    have h1 : (rV0 D A3.A F.P1 F.ψ1 t).mulVec f ∈ LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin := by
      rw [hR]; exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := h1
    refine ⟨Y.jA t g, ?_⟩
    exact (hFo.op_eq g).trans (congrArg (Y.jA t) hg)
  have hQ : ∃ x f, D.what₂.Bu u (D.jN u (C.eNu u x))
      (D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f))) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨φ0, F0, hF0, hne⟩ := hnz
    apply hne
    rw [hfac φ0 F0 hF0, iota_starProjection_Qsp D _ F0 hF0]
    have h1 : ∀ x, ∀ F ∈ D.what₂.V0 (Y.tup t), D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) F) = 0 := by
      intro x F hF
      obtain ⟨y, rfl⟩ := hF
      let L : D.what₂.Amb (Y.tup t) →ₗ[ℂ] ℂ :=
        ((D.Bu_linR u (D.jN u (C.eNu u x))).mk' _) ∘ₗ D.what₂.iota (Y.tup t) ∘ₗ D.what₂.eOp (Y.tup t)
      have hL : L = 0 := by
        refine LinearMap.ext_on_range hFo.span fun i => ?_
        have h2 : (rE D A3.A F.P1 F.ψ1 t).mulVec (Pi.single i 1) ∈ LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin := by
          rw [← hR]; exact ⟨_, rfl⟩
        obtain ⟨f, hf⟩ := h2
        have e1 : D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)) = Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) :=
          (hFo.op_eq _).trans (congrArg (Y.jA t) hf.symm)
        show D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) (D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)))) = 0
        rw [e1]
        exact hcon x f
      exact LinearMap.congr_fun hL y
    let M : D.what₂.Mu u →ₗ[ℂ] ℂ := (D.Bu_linL u (D.what₂.iota (Y.tup t) F0)).mk' _
    have hM : M = 0 := by
      refine LinearMap.ext_on_range (D.jN_basis u).2 fun i => ?_
      have h3 := h1 ((C.eNu u).symm ((D.div.Nu u).b i)) F0 hF0
      rw [LinearEquiv.apply_symm_apply] at h3
      exact h3
    rw [show D.what₂.Bu u φ0 (D.what₂.iota (Y.tup t) F0) = 0 from LinearMap.congr_fun hM φ0, mul_zero]
  obtain ⟨x, f, hx⟩ := hQ
  have hpt := C.pt u t x f
  have hf := hfac (D.jN u (C.eNu u x)) _ (hmem f)
  rw [iota_starProjection_Qsp D _ _ (hmem f)] at hf
  obtain ⟨w, hw⟩ : ∃ w : D.div.RR.V,
      D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) = D.jEE w :=
    ⟨_, by rw [← Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]; exact hRS.iota t f⟩
  rw [hw, hB] at hx hf
  refine ⟨(F.Dc (R.toCx3 F).zs).Pt (C.wU u) t x f / D.div.Bk u (C.eNu u x) w, ?_⟩
  rw [map_div₀, hpt, hf]
  exact mul_div_cancel_right₀ c hx

end GlobalTheory.Mem.R3
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem bk_eq_of_coordinates (D : D7) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0) {n nV d a : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL)
    (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (u : D.what₂.Word)
    (eN : (Fin a → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (P : (Fin a → D.what₂.LL) → (Fin nV → D.what₂.LL) → D.what₂.LL)
    (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (hBR : D.BuRational)
    (hV : D.what₂.V0 μ = Submodule.span ℂ (Set.range fun G => jA (V.mulVec G)))
    (hι : ∀ G, D.what₂.iota μ (jA (V.mulVec G)) = D.jEE (eRR (Pq.mulVec G)))
    (hper : ∀ x G, D.what₂.embLL (P x G) = D.what₂.perCol u μ (D.jN u (eN x)) (jA (V.mulVec G)))
    (hvan : ∀ x G, Pq.mulVec G = 0 → P x G = 0) :
    ∀ x G, D.div.Bk u (eN x) (eRR (Pq.mulVec G)) = P x G := by
  subst hμ
  intro x G
  have key := GlobalTheory.span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0}) := by
    rw [← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  have hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 (D.jN u (eN x)) F = 0 := by
    intro F hF
    rw [hU] at hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨G', hG', rfl⟩ := hF
      have hG'' : Pq.mulVec G' = 0 := eRR.map_eq_zero_iff.1 hG'
      refine (hper x G').symm.trans ?_
      rw [hvan x G' hG'', map_zero]
    | zero => exact D.perCol_zero u _
    | add F G _ _ hF hG => rw [D.perCol_add, hF, hG, add_zero]
    | smul c F _ hF => rw [GlobalTheory.perCol_base_smul_form, hF, mul_zero]
  have hmem : jA (V.mulVec G) ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G, rfl⟩
  apply D.what₂.embLL.injective
  rw [← hBR u (eN x) (eRR (Pq.mulVec G)), ← hι G, hper x G]
  exact (GlobalTheory.perCol_eq_pairing_of_kills D hB u _ hK _ hmem).symm

theorem pairing_eq_colPairing : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), Pins R F cG → Holds R F → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → ∀ u x y, D.div.Bk u (C.eNu u x) (Z.eRR y) = (colOf R F sEE).B (C.wU u) x y := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE hPins hHolds hBR hBt u x y
  have hR := complex_data_conditions_base_level_of_primitive_links hHolds.ok hHolds.sep hPins.char hHolds.prim
  have hW := hR.wf true
  have h2 := (hR.what₂ true).1
  have hI := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds).1
  have hPq := hW.Pq_surj A3.fam3.base3.μ0
  have hRi := CxData.rinv_spec _ hPq
  have hV := GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (Y.jA A3.fam3.base3.μ0) _ _ _
      (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) (Y.formsA A3.fam3.base3.μ0)
      (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A 1 hHolds.ok.ok2 F.P1 F.ψ1 A3.fam3.base3.μ0)
  have hι : ∀ G0, D.what₂.iota (Y.tup A3.fam3.base3.μ0) (Y.jA A3.fam3.base3.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0).mulVec G0)) =
      D.jEE (Z.eRR (((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec G0)) := by
    intro G0
    have h := hI.iota A3.fam3.base3.μ0 G0
    rw [Formalism.BasicNotions.Examples₂.NZ.sharp_iota] at h
    refine h.trans ?_
    show D.jEE (Z.eRR (((R.toCx3 F).rowMat F.cr true A3.fam3.base3.μ0).mulVec _)) = _
    rw [CxData.rowMat_base _ F.cr true h2]
    exact congrArg (fun v => D.jEE (Z.eRR v)) (Matrix.one_mulVec _)
  have key := bk_eq_of_coordinates D (Y.tup A3.fam3.base3.μ0) Y.tup0 (Y.jA A3.fam3.base3.μ0)
    (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0) Z.eRR u (C.eNu u)
    (fun x G0 => (F.Dc (R.toCx3 F).zs).Pt (C.wU u) A3.fam3.base3.μ0 x G0) Y.bu hBR hV hι
    (fun x G0 => C.pt u A3.fam3.base3.μ0 x G0) ?_
  · have hy : ∀ v : Fin ((lv (F.fc (R.toCx3 F).zs) true).dQ A3.fam3.base3.μ0) → D.what₂.LL,
        ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec
          ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec v) = v := by
      intro v
      refine (Matrix.mulVec_mulVec _ _ _).trans ?_
      exact (congrArg (fun M => Matrix.mulVec M v) hRi).trans (Matrix.one_mulVec v)
    refine Eq.trans ?_ (key x ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec y))
    exact congrArg (fun v => D.div.Bk u (C.eNu u x) (Z.eRR v)) (hy y).symm
  · intro x G0 hG0
    apply hBt (C.wU u) x G0
    exact LinearMap.mem_ker.2 hG0

end GlobalTheory.Mem.R3
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem rowLat_ties : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HLatTie (RowSide.sharp D).RR (A3.indefDown (s1Of R F)).RR (A3.indefDown (s1Of R F)).XE Z.eRR ∧ HLatTie X0.s.RR (A3.indefDown (s0Of R F)).RR (A3.indefDown (s0Of R F)).XE Z.eRR0 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hD := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have hmu1 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s1Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have hmu0 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s0Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have h1 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA hok hD.1 Z.rr hmu1 Y.stable
  have h0 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE0 X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 hok hD.2 Z.rr0 hmu0 Y.stable0
  have m1 := GlobalTheory.Mem.R3.MetSharp.majAt_rows_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have m0 := GlobalTheory.Mem.R3.MetBase.metric_base_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨⟨h1, fun v x y => ?_⟩, ⟨h0, fun v x y => ?_⟩⟩
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m1 x y
    · exact Z.met v hv x y
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m0 x y
    · exact Z.met0 v hv x y

end GlobalTheory.Mem.R3
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec

theorem kapOf_of_eigen {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) {κ : ℝ} (hk : 0 < κ) (hn : 0 < n)
    (hP : ∀ σ, 0 < ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ))
    (hT : ∀ σ, S.iiStar (b σ) = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) : ℝ) : ℂ) • b σ) :
    S.kapOf ty = κ := by
  set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef
  have hdet : LinearMap.det S.iiStar = ((κ ^ n * ∏ σ, P σ : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar =
        Matrix.diagonal (fun σ => ((κ * P σ : ℝ) : ℂ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply,
        ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : j = i
      · subst hij; simp [P]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]; simp
    rw [hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hr : S.kapRatio ty = κ ^ n := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hdet, Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ (Finset.prod_pos fun σ _ => hP σ).ne'
  unfold RowSide.kapOf
  rw [hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (y : EE) :
    S.iiStar y = S.iota D.what₂.mu0 (S.eOp D.what₂.mu0 (LinearMap.adjoint (S.iota D.what₂.mu0) y)) := by
  set μ := D.what₂.mu0
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem kapSharp_eq_kap : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → kapSharp D = R.kap := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI
  exact kapOf_of_eigen (RowSide.sharp D) D.what₂.onb D.what₂.ft hH.prim.posScal.1
    (GlobalTheory.Mem.R3.drows_pos D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL)
    (fun σ => Finset.prod_pos (GlobalTheory.Mem.R3.LamPos.lambdaPrime_basis_row_type_pos_at_reference D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))
    (fun σ => (iiStar_apply_eq (RowSide.sharp D) (D.what₂.onb σ)).trans
      (GlobalTheory.T.iotaProjectionAdjoint_basisRow_eigenvalue hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))

end GlobalTheory.KapRec
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem divisionPairing_rational_on_rationalPoints : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hPins hHolds
  have hR := complex_data_conditions_base_level_of_primitive_links hHolds.ok hHolds.sep hPins.char hHolds.prim
  have hW := hR.wf true
  have h2 := (hR.what₂ true).1
  have hI := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds).1
  have hPq := hW.Pq_surj A3.fam3.base3.μ0
  have hV := GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (Y.jA A3.fam3.base3.μ0) _ _ _
      (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) (Y.formsA A3.fam3.base3.μ0)
      (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A 1 hHolds.ok.ok2 F.P1 F.ψ1 A3.fam3.base3.μ0)
  have hι : ∀ G0, D.what₂.iota (Y.tup A3.fam3.base3.μ0) (Y.jA A3.fam3.base3.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0).mulVec G0)) =
      D.jEE (Z.eRR (((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec G0)) := by
    intro G0
    have h := hI.iota A3.fam3.base3.μ0 G0
    rw [Formalism.BasicNotions.Examples₂.NZ.sharp_iota] at h
    refine h.trans ?_
    show D.jEE (Z.eRR (((R.toCx3 F).rowMat F.cr true A3.fam3.base3.μ0).mulVec _)) = _
    rw [CxData.rowMat_base _ F.cr true h2]
    exact congrArg (fun v => D.jEE (Z.eRR v)) (Matrix.one_mulVec _)
  exact GlobalTheory.buRat_of_coordinates D (Y.tup A3.fam3.base3.μ0) Y.tup0 (Y.jA A3.fam3.base3.μ0)
    (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0) Z.eRR
    (fun u => (F.Dc (R.toCx3 F).zs).a (C.wU u)) C.eNu Y.bu
    (fun x y => ⟨_, ((Y.formsA A3.fam3.base3.μ0).inner x y).symm⟩) hV hι hPq
    (fun u x F0 => ⟨_, C.pt u A3.fam3.base3.μ0 x F0⟩)

end GlobalTheory.Mem.R3
end
