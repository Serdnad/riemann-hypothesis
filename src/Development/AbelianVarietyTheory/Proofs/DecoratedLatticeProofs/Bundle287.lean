module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle277
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.ExistsCommonLevelSobolevBoundWeilCompact

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

namespace GlobalTheory.FrameGlob

open Matrix

theorem exists_gl_of_lattices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (Λ₁ Λ₂ : Submodule 𝒪[k] (n → k)) (h₁ : Λ₁.IsFullLattice k)
    (h₂ : Λ₂.IsFullLattice k) : ∃ g : GL n k, ∀ z, z ∈ Λ₁ ↔ g.val *ᵥ z ∈ Λ₂ := by
  have key : ∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k →
      ∃ e : (Fin (Fintype.card n) → k) ≃ₗ[k] (n → k), ∀ y, e y ∈ Λ ↔ ∀ i, y i ∈ 𝒪[k] := by
    intro Λ hΛ
    let : Module.Free 𝒪[k] Λ := Submodule.IsLattice.free k Λ
    let : Module.Finite 𝒪[k] Λ := Submodule.IsLattice.finite k Λ
    let b := Module.finBasisOfFinrankEq 𝒪[k] Λ
      ((Submodule.IsFullLattice.finrank_eq k Λ).trans (Module.finrank_fintype_fun_eq_card k))
    let b' := b.extendOfIsFullLattice k
    have hkey : ∀ c : Fin (Fintype.card n) → 𝒪[k],
        b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : Λ) : n → k) := by
      intro c
      rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.extendOfIsFullLattice_apply]
      rfl
    refine ⟨b'.equivFun.symm, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have h1 := hkey (b.repr ⟨_, h⟩)
      rw [b.sum_repr] at h1
      rw [← b'.equivFun.symm.injective h1]
      exact fun i => (b.repr ⟨_, h⟩ i).2
    · have h1 := hkey fun i => ⟨y i, h i⟩
      have h2 : b'.equivFun.symm y = _ := h1
      rw [h2]
      exact Subtype.property _
  obtain ⟨e₁, he₁⟩ := key Λ₁ h₁
  obtain ⟨e₂, he₂⟩ := key Λ₂ h₂
  let φ : (n → k) ≃ₗ[k] (n → k) := e₁.symm.trans e₂
  refine ⟨⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap, ?_, ?_⟩, fun z => ?_⟩
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.toLinearMap * φ.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.symm.toLinearMap * φ.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · show z ∈ Λ₁ ↔ LinearMap.toMatrix' φ.toLinearMap *ᵥ z ∈ Λ₂
    rw [LinearMap.toMatrix'_mulVec]
    have h := he₁ (e₁.symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.coe_coe, ← he₂]
    rfl

end GlobalTheory.FrameGlob

namespace GlobalTheory.FrameGlob

open Matrix

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 p.e).2 ?_
  rw [← hsum, add_mul, hee, mul_comm (cA D p.e), hec, add_zero]

theorem sec_eq_mul (p : SplitPt D k) (a : k) : p.sec a = p.e * p.sec a := by
  have h := p.sec_pr (p.sec a)
  rwa [p.pr_sec] at h

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  rw [sec_eq_mul]
  exact Ideal.mul_mem_right _ _ (e_mem_idAt p)

variable {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_gl_vec {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (z : n → k) :
    mt S (β.gl g) *ᵥ (fun i => p.sec ((β.b *ᵥ z) i)) = fun i => p.sec ((β.b *ᵥ (g.val *ᵥ z)) i) := by
  funext i
  set m := mt S (β.gl g)
  set y : Fin S.rank → AE D := fun i => p.sec ((β.b *ᵥ z) i)
  have he : (m *ᵥ y) i = p.e * (m *ᵥ y) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show m i j * p.sec _ = p.e * (m i j * p.sec _)
    conv_lhs => rw [sec_eq_mul]
    ring
  have hpr : p.pr ((m *ᵥ y) i) = ((m.map p.pr) *ᵥ (β.b *ᵥ z)) i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, y, p.pr_sec]
  rw [he, ← p.sec_pr, hpr, β.gl_mat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, β.b'b, Matrix.mul_one]

theorem mt_gl_off {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· ≠ p.v)) : mt S (β.gl g) *ᵥ y = y := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have h0 : (mt S (β.gl g) - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← β.gl_supp g i j, hsum]
    calc algebraMap (AF D.host.F) (AE D) ε * (mt S (β.gl g) - 1) i j * y j
        = (mt S (β.gl g) - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [(GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).2 _ (hy j), mul_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ
  obtain ⟨Λ₁, hΛ₁, hLat₁, -⟩ := GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β L hL
  have hFull₁ : Λ₁.IsFullLattice k := by
    refine { toIsLattice := hΛ₁, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := FrameLat.exists_gen (p := p) hL
    have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
    simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hLat₁ _).2
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
    exact FrameLat.sec_inc_mem (p := p) (hs l)
  obtain ⟨g, hg⟩ := exists_gl_of_lattices Λ₁ Λ hFull₁ hΛ
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S L hL).1 (β.gl g)
  have supp : ∀ (N : Lat S), IsSelfDualC S N → ∀ y, y ∈ latV S N (· ≠ p.v) → ∀ i, y i ∈ idAt D (· ≠ p.v) :=
    fun N hN y hy => (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ p.v)).2 S).2.2.2 N y hN.1 |>.1 hy).1
  refine ⟨M, hM, fun x => ?_, ?_⟩
  · have hx : x = g.val *ᵥ ((g⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hx, ← hg, hLat₁, hMv (· = p.v) _ (fun i => sec_mem_idAt p _), mt_gl_vec]
  · ext y
    constructor
    · intro hy
      have hs := supp M hM y hy
      rw [← mt_gl_off β g y hs] at hy
      exact (hMv (· ≠ p.v) y hs).2 hy
    · intro hy
      have hs := supp L hL y hy
      have h := (hMv (· ≠ p.v) y hs).1 hy
      rwa [mt_gl_off β g y hs] at h

end GlobalTheory.FrameGlob
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DStepCell

variable {D : D7}

def integ {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ)
    (q₁ : GA D (c.V (j + 1))) (q₂ : GA D (c.V (j + 1 + 1))) : ℂ :=
  ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
      (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
      (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁ q₂) (rTrans q₂ f)

end GlobalTheory.DStepCell

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawRhs

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hv' => hv v (fun hp => hv' (h v hp)), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono S T _ _ h hu),
    fun e he u hu hh => hf.2.2 e he u (latO_mono S T _ _ h hu) hh⟩

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : idAt D P ≤ idAt D P' := by
  intro x hx
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {c : WO S T →₀ ℂ}
    (hc : CombAt P c) : CombAt P' c := fun u hu i j => idAt_mono h (hc u hu i j)

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp [comb, heisO, Finset.sum_apply]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • C) = a • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, Pi.smul_apply, smul_eq_mul, comb_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem comb_comm2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (e : WO A S →₀ ℂ) (d' : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' d' (fun v' => comb ψ A S e (fun u'' => G u'' v') u) v =
      comb ψ A S e (fun u'' => comb ψ S A' d' (G u'') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (d e : WO A S →₀ ℂ) (d' e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' d d' (biComb ψ A S A' e e' C) u v =
      comb ψ A S d (comb ψ A S e (fun u'' => comb ψ S A' d' (comb ψ S A' e' (C u'')) v)) u := by
  simp only [biComb]
  congr 1
  funext u'
  exact comb_comm2 ψ A S A' e d' (fun u'' v' => comb ψ S A' e' (C u'') v') u' v

theorem biLift_smul {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h1 : ∀ h₀ h₁ v, oma (h₀, h₁) (fun u => a * C u v) 0 = a * oma (h₀, h₁) (fun u => C u v) 0 := by
    intro h₀ h₁ v
    rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
    rfl
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => h1 h₀ h₁ v
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem theta_comb_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (c : WO S A' →₀ ℂ) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => comb ψ S A' c (Y u) v) := by
  classical
  have key : ∀ s : Finset (WO S A'),
      IsThetaFunO ψ A S (fun u => ∑ x ∈ s, c x * (ψ (symplOH S A' v x) * Y u (v + x))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Formalism.IndefR.Fock.CCR.theta_zero ψ A S
    · intro x s hx ih
      have := Formalism.IndefR.Fock.CCR.theta_add_smul ih (hY (v + x)) (c x * ψ (symplOH S A' v x))
      convert this using 1
      funext u
      simp only [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simpa only [comb_apply] using key c.support

end GlobalTheory.SeeSawRhs

namespace GlobalTheory.SeeSawRhs

theorem unfolded_eq_kernel_data : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  intro D c v t w hc hv _ hF hG hT _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ β
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  simp only [Comm.bl]
  rw [hG.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  set X₀ := c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ with hX₀
  set Y := (v.op j).app c.ψ X₀ with hY
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  unfold Tup.two
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  rw [biComb_smul, biLift_smul, e1, hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α), e2,
    smul_smul]

end GlobalTheory.SeeSawRhs
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.sobolevBoundedThetaForm_matrixCoeff_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → Continuous (fun u => ℓ (heisO ψ S T u f)) ∧ ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ u, ContDiff ℝ ∞ fun t => ℓ (heisO ψ S T (u + L t) f) := by
  first | exact @GlobalTheory.Unf.MatCoef.matCoef_smooth | exact GlobalTheory.Unf.MatCoef.matCoef_smooth | (intros; apply GlobalTheory.Unf.MatCoef.matCoef_smooth <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem tendsto_enorm_of_le {v : ℕ → ℂ} {a : ℂ} {s : ℕ → ℝ≥0∞} (C : ℝ≥0) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (h : ∀ j, ‖v j - a‖ₑ ≤ C * s j) : Filter.Tendsto (fun j => ‖v j‖ₑ) Filter.atTop (nhds ‖a‖ₑ) := by
  have h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)
  have h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      (fun j => by simpa [edist_eq_enorm_sub] using h j)
  exact (continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)

theorem sobBdd_absThetaInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m :=
  UpperTheory.Lit.Rallis.ThetaDens.sobBdd_absThetaInt

end GlobalTheory.ThetaDens
end

section

namespace GlobalTheory.Core.Deg

theorem vanishingGramBoundWindow_of_termPairTypeBound (hT : GlobalTheory.TypeAsm.TypeP) : VanishingGramTermsBoundWindow := by
  intro Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, H⟩ := hT Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨C₀, H2⟩ := H (Cp + 4) le_rfl
  obtain ⟨C'₀, Cl₀, H3⟩ := H2 (max C₀ (2 * (CH + 1))) (le_max_left _ _)
  obtain ⟨Cl₁, H4⟩ := GlobalTheory.T.pairsAmplitudeBound_of_typeBound CH Ch Cp (max C₀ (2 * (CH + 1))) hCH hCh hCp (le_max_right _ _)
  refine ⟨max C'₀ 1, max Cl₀ Cl₁, fun C' Cl hC' hCl D large₂ X Y _ _ u hTies _ h0 hC hAbs => ?_⟩
  have hK2 : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 :=
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 ((le_max_right _ _).trans hC')
  have hType := H3 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans hCl) D large₂ X Y u hTies hK2 hC
  have hPairs := H4 C' Cl Cg cb Cu cT CT C0 D large₂ X Y u ((le_max_right _ _).trans hCl) hK2 hC hType
  exact GlobalTheory.T.deg_termSumBoundOfPairsAmplitude C' Cl Cg cb Cu cT CT C0 D large₂ X Y u hK2 hC hAbs hPairs

end GlobalTheory.Core.Deg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_unimodular_basis_selfDual_lattice_at_place : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular | exact GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular | (intros; apply GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_flag_stabiliser_move_lattice_split_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  first | exact @GlobalTheory.IwaPlace.iwasawa_flag_move | exact GlobalTheory.IwaPlace.iwasawa_flag_move | (intros; apply GlobalTheory.IwaPlace.iwasawa_flag_move <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

theorem _root_.GlobalTheory.T.isPolynomialFockThetaVector_orthogonalBoxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  first | exact @GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT | exact GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT | (intros; apply GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT <;> assumption)
end
