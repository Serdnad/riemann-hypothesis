module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7}

abbrev finf (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finf D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n)
    (y : Mx D n k) (hm : m.map (finf D) = 1) :
    (x * m * y).map (finf D) = (x * y).map (finf D) := by
  have e1 : (x * m * y).map (finf D) = x.map (finf D) * m.map (finf D) * y.map (finf D) := by
    rw [Matrix.map_mul (f := finf D), Matrix.map_mul (f := finf D)]
  have e2 : (x * y).map (finf D) = x.map (finf D) * y.map (finf D) := Matrix.map_mul (f := finf D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one, ← Matrix.map_add _ (map_add (finf D)),
    o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem witt_embedding_mem_finite_unitary_points {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finf D)), Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ hg, ← Matrix.map_add _ (map_add (finf D)), ← Matrix.map_add _ (map_add (finf D)),
    d.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (ha : a ∈ GfC A) : embA d o a ∈ GfC S := by
  rw [embA_apply]
  exact witt_embedding_mem_finite_unitary_points d (orth_emb_mem_GfC o ha)

theorem castGA_fst {I I' : AutInst} (e : I = I') (x : I.GA) : (castGA e x).1 = 1 ↔ x.1 = 1 := by
  subst e
  exact Iff.rfl

theorem iotaX_fst {X : HidaSetting D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) {k : GA D (D.sp.Y 0)}
    (hk : k ∈ GfC (D.sp.Y 0)) : (iotaX X h k).1 = 1 := by
  have e := (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)).1 (by simpa using hk)
  exact (castGA_fst h.symm (Formalism.IndefR.RationalEmbedding.iota D k)).2 e

end GlobalTheory.Core.Mi.CenAct

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7} {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem toH_mul (B : SBes X h u ψ A) (a b : GA D A) : B.toH (a * b) = B.toH a * B.toH b := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (iotaX X h (embA B.d B.o (a * b))).1 = (iotaX X h (embA B.d B.o a)).1 * (iotaX X h (embA B.d B.o b)).1
    rw [map_mul, map_mul]
    rfl
  · show (iotaX X h (embA B.d B.o (a * b))).2 = (iotaX X h (embA B.d B.o a)).2 * (iotaX X h (embA B.d B.o b)).2
    rw [map_mul, map_mul]
    rfl

theorem toH_fst (B : SBes X h u ψ A) {a : GA D A} (ha : a ∈ GfC A) : (B.toH a).1 = 1 :=
  Subtype.ext (iotaX_fst h (embA_mem_GfC B.d B.o ha))

theorem toH_surj (B : SBes X h u ψ A) (k : Hfin X u) : ∃ a : GA D A, B.toH a = (1, k) := by
  obtain ⟨a, ha⟩ := (B.tieH ((iotaX X h).symm (1, (k : X.B.I.Gf)))).2 (by
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact ⟨one_mem _, k.2⟩)
  refine ⟨a, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · show (iotaX X h (embA B.d B.o a)).1 = 1
    rw [ha, ContinuousMulEquiv.apply_symm_apply]
  · show (iotaX X h (embA B.d B.o a)).2 = k
    rw [ha, ContinuousMulEquiv.apply_symm_apply]

theorem toH_snd_comm (B : SBes X h u ψ A) {a : GA D A} (hc : a ∈ Subgroup.center (GA D A)) (k : Hfin X u) :
    (B.toH a).2 * k = k * (B.toH a).2 := by
  obtain ⟨a', ha'⟩ := toH_surj B k
  have e : B.toH (a * a') = B.toH (a' * a) := by rw [(Subgroup.mem_center_iff.1 hc a').symm]
  rw [toH_mul, toH_mul, ha'] at e
  exact congrArg Prod.snd e

theorem rtr_mem_Cu (hK : X.LevelSubgroupCharacter) {δ : Hfin X u} (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) :
    Formalism.L2.SG.ColDict.rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ : Hfin X u)) :=
      Prod.ext rfl (hδ κ).symm
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (congrArg (T ξ) e).trans ((h1 ξ).2 _ κ)
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

end GlobalTheory.Core.Mi.CenAct


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.LeviCoordinates in
theorem GlobalTheory.Core.Mi.inner_pser_eq_setIntegral : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Fs : Set X.B.I.GA), IsReps X u Dt → InHH X u hK → IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∀ T : Cu X u hK, IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) → ∀ (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f → ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
  intro D X u hK Dt Fs hD hin hFs T hPI f φ hf hφf
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  have := Formalism.L2.SG.Pf.muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  have hPP := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hFD := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hS : Srat X u ≤ rr_GF X.B.I := inf_le_left
  have hDc : Dt.Countable :=
    (Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1
  have := hDc.to_subtype
  have hSc : Countable (Srat X u) := Function.Injective.countable (Subgroup.inclusion_injective hS)
  have hSinv : SMulInvariantMeasure (Srat X u) X.B.I.GA (X.B.I.muA X.B.μf) := ⟨fun s A _ => by
      show (X.B.I.muA X.B.μf) ((fun y => (s : X.B.I.GA) * y) ⁻¹' A) = (X.B.I.muA X.B.μf) A
      exact measure_preimage_mul _ (s : X.B.I.GA) A⟩
  have hPm : Measurable (Ph X u hK T) := (hPP T).1
  have hPinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y := (hPP T).2.1
  have hfm : Measurable f := hf.cont.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hfinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, f (γ * y) = f y := fun γ hγ y => hf.left γ hγ y
  have hginv : ∀ (s : Srat X u) (x : X.B.I.GA),
      (fun x => f x * Ph X u hK T x) ((s : X.B.I.GA) * x) = (fun x => f x * Ph X u hK T x) x := by
    intro s x
    show f (s * x) * Ph X u hK T (s * x) = f x * Ph X u hK T x
    rw [hfinv s (hS s.2) x, hPinv s s.2 x]
  have hF' : IsFundamentalDomain (Srat X u) (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) (X.B.I.muA X.B.μf) :=
    rr_isFD (Formalism.L2.SG.Pf.InHHLeaf.rr_FD_union hFD (Srat X u) hS Dt hD hDc)
  have hgFs : IntegrableOn (fun x => f x * Ph X u hK T x) Fs (X.B.I.muA X.B.μf) :=
    Integrable.bdd_mul (c := C) hPI hfm.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hgFs' := (hFs.integrableOn_iff hF' hginv).1 hgFs
  have e1 : ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) :=
    hFs.setIntegral_eq hF' (f := fun x => f x * Ph X u hK T x) hginv
  have hU : (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) = ⋃ δ : Dt, (fun y => (δ : X.B.I.GA) * y) '' X.B.fund := by
    rw [Set.biUnion_eq_iUnion]
  have hmeas : ∀ δ : Dt, MeasurableSet ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ; rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul]; exact hFD.meas.preimage (measurable_const_mul _)
  have hdisj : Pairwise (Function.onFun (AEDisjoint (X.B.I.muA X.B.μf))
      fun δ : Dt => (fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ δ' hne
    show X.B.I.muA X.B.μf (((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund)) = 0
    have hsub : ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund) ⊆
        (fun y => (δ' : X.B.I.GA) * y) '' ((fun y => ((δ' : X.B.I.GA)⁻¹ * δ) * y) '' X.B.fund ∩ X.B.fund) := by
      rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩
      simp only at hxx
      refine ⟨x', ⟨⟨x, hx, ?_⟩, hx'⟩, hxx⟩
      show (δ' : X.B.I.GA)⁻¹ * δ * x = x'
      rw [show x' = (δ' : X.B.I.GA)⁻¹ * ((δ' : X.B.I.GA) * x') by group, hxx]; group
    refine measure_mono_null hsub ?_
    have hγ : (δ' : X.B.I.GA)⁻¹ * δ ∈ rr_GF X.B.I := (rr_GF X.B.I).mul_mem ((rr_GF X.B.I).inv_mem (hD.1 δ'.2)) (hD.1 δ.2)
    have hne' : (δ' : X.B.I.GA)⁻¹ * δ ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      rw [← mul_one (δ' : X.B.I.GA), ← h1]; group
    rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul, measure_preimage_mul]
    exact hFD.disj _ hγ hne'
  have e2 : ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
    rw [hU] at hgFs' ⊢
    exact integral_iUnion_ae (fun δ => (hmeas δ).nullMeasurableSet) hdisj hgFs'
  have e3 : ∀ δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    intro δ
    have hpre : (fun y => (δ : X.B.I.GA) * y) ⁻¹' ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) = X.B.fund :=
      Set.preimage_image_eq _ (mul_right_injective (δ : X.B.I.GA))
    have h2 := (measurePreserving_mul_left (X.B.I.muA X.B.μf) (δ : X.B.I.GA)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (δ : X.B.I.GA)) (fun x => f x * Ph X u hK T x)
      ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)
    rw [hpre] at h2
    rw [← h2]
    refine setIntegral_congr_fun hFD.meas fun y _ => ?_
    show f ((δ : X.B.I.GA) * y) * Ph X u hK T ((δ : X.B.I.GA) * y) = f y * Ph X u hK T ((δ : X.B.I.GA) * y)
    rw [hfinv _ (hD.1 δ.2) y]
  have hbound : ∑' δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≠ ⊤ := by
    have hle : ∀ δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≤
        ENNReal.ofReal C * ∫⁻ y in X.B.fund, ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) := by
      intro δ
      rw [← lintegral_const_mul (f := fun y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) _ (hPm.comp (measurable_const_mul _)).enorm]
      refine lintegral_mono fun y => ?_
      rw [enorm_mul]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC y)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun (δ : Dt) y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) (fun δ => (hPm.comp (measurable_const_mul _)).enorm.aemeasurable),
      Formalism.L2.SG.Pf.InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs (fun w => ‖Ph X u hK T w‖ₑ) hPm.enorm
        (fun s hs y => by simp only [hPinv s hs y])]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPI.2.ne
  have e4 : ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    have hfun : (fun y => f y * Pser X u hK Dt T y) = fun y => ∑' δ : Dt, f y * Ph X u hK T ((δ : X.B.I.GA) * y) := by
      funext y
      show f y * ∑' δ : Dt, Ph X u hK T ((δ : X.B.I.GA) * y) = _
      rw [tsum_mul_left]
    rw [hfun]
    exact integral_tsum (fun δ => (hfm.mul (hPm.comp (measurable_const_mul _))).aestronglyMeasurable) hbound
  have hm := (hin T Dt hD).2.2.1
  have eL : ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) := by
    have e0 : PuFun X u hK Dt T = hm.toLp (Pser X u hK Dt T) := dif_pos hm
    rw [e0, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star φ, hm.coeFn_toLp, hφf] with a h1 h2 h3
    rw [h1, h2, Pi.star_apply, h3, RCLike.inner_apply]
    rw [mul_comm]
    congr 1
    first
      | exact Complex.conj_conj (f a)
      | simp [Complex.star_def]
  rw [eL, e4, e1, e2]
  exact tsum_congr fun δ => (e3 δ).symm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.IterProof

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem rTrans_lift {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (G : GA D W → ℂ) (Φ : WO V W → ℂ)
    (g : GA D V) : rTrans g (s.lift G Φ) = s.lift G (s.om (g, 1) Φ) := by
  funext x
  have key : ∀ h, s.om (x * g, h) Φ = s.om (x, h) (s.om (g, 1) Φ) := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [rTrans, Step.lift, liftS_apply, key]

end GlobalTheory.Unf.IterProof


open GlobalTheory.Unf.IterProof in
theorem GlobalTheory.Unf.iter_of_doubleStep_lastLaw : ∀ D : D7, DoubleStep D → LastLaw D → IT D := by
  intro D hD hL ψ T ρ B c
  induction c with
  | @last B t =>
    intro Φ F φ g hΦ hF hφ _
    show B.per ψ φ (rTrans g (t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ.2) Φ.1)) =
      t.Q φ (t.s.om (g, 1) Φ.1) Φ.2 F
    rw [rTrans_lift]
    exact hL ψ T B t φ _ Φ.2 F hφ hF (t.s.weil.om_pres _ _ hΦ.1) hΦ.2
  | @step σ B J B' s₁ s₂ l vL c ih =>
    intro Φ F φ g hΦ hF hφ hR
    obtain ⟨hR₁, hR₂, hR₃⟩ := hR
    obtain ⟨hΦ₁, hΦ₂, hΦ₃⟩ := hΦ
    obtain ⟨hcont, f₁, h₁, h₂⟩ := hD ψ σ B J B' s₁ s₂ l vL Φ.1 Φ.2.1 φ (c.down Φ.2.2 F) g hΦ₁ hΦ₂ hφ hR₂ hR₁
    refine ⟨f₁, fun a b => B'.per ψ (Chain.hand s₁ s₂ l vL Φ.1 Φ.2.1 φ g a b) (rTrans b (c.down Φ.2.2 F)), h₁,
      fun a => ⟨h₂ a, fun b => ?_⟩⟩
    exact ih Φ.2.2 F _ b hΦ₃ hF (hcont a b) hR₃
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.FinPl

theorem tensorProductBasis_repr_map_firstFactor {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing B] [Algebra F B] {ι : Type} (b : Module.Basis ι F E) (f : A →ₐ[F] B) (x : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | tmul a m =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Algebra.smul_def]

theorem CMAdele_eq_zero_of_infinite_and_finite_components_zero (D : D7) (a : AE D) (h0 : infPart D a = 0) (hw : ∀ w : Pl D, compAt D w a = 0) :
    a = 0 := by
  let b := Module.Free.chooseBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  suffices hc : ∀ i, bA.repr a i = 0 by
    apply bA.repr.injective
    ext i
    simpa using hc i
  intro i
  have h1 : fstA D.host.F (bA.repr a i) = 0 := by
    have := tensorProductBasis_repr_map_firstFactor b (fstA D.host.F) a i
    rw [← this]
    change (Algebra.TensorProduct.basis _ b).repr (infPart D a) i = 0
    rw [h0]; simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h2 : ∀ w : Pl D, evalV D.host.F w (sndA D.host.F (bA.repr a i)) = 0 := by
    intro w
    have e1 := tensorProductBasis_repr_map_firstFactor b (sndA D.host.F) a i
    have e2 := tensorProductBasis_repr_map_firstFactor b (evalV D.host.F w)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) i
    have hw' : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) = 0 := hw w
    rw [← e1, ← e2, hw', LinearEquiv.map_zero]
    rfl
  apply Prod.ext
  · exact h1
  · apply Subtype.ext
    funext w
    exact h2 w

theorem mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere (D : D7) (P : Pl D → Prop) (a : AE D) :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w : Pl D, ¬ P w → compAt D w a = 0 := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem placeIdempotent_infinite_and_finite_components (D : D7) (v : Pl D) (ε : AF D.host.F) (α : Af D.host.F)
    (hε : ε = pairA D.host.F 0 α) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, hε]
    exact TensorProduct.zero_tmul _ _
  · rw [ha]
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]
    rfl

theorem mem_supportedAtPlace_iff_placeIdempotent_mul (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0) (c1 : compAt D v e = 1)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) : a ∈ idAt D (· = v) ↔ e * a = a := by
  constructor
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
    obtain ⟨ha0, haw⟩ := ha
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul]
      by_cases h : w = v
      · subst h; rw [c1, one_mul, sub_self]
      · rw [haw w h, mul_zero, sub_zero]
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw' => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, c0 w hw', zero_mul]

theorem placeIdempotent_mul_supportedOffPlace_eq_zero (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) (ha : a ∈ idAt D (· ≠ v)) : e * a = 0 := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  obtain ⟨ha0, haw⟩ := ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · rw [haw w (fun h' => h' h), mul_zero]
    · rw [c0 w h, zero_mul]

theorem placeIdem_acts : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  intro D v ε ⟨α, hε, hv, hw⟩
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1 := by
    rw [hc, hv]; rfl
  have c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    intro w h; rw [hc, hw w h, TensorProduct.zero_tmul]
  exact ⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩

end GlobalTheory.FinPl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppGrp

open GlobalTheory.FinPl

theorem placeIdem_mem_idAt {D : D7} {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (P : Pl D → Prop) (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h2⟩ := h
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · exact TensorProduct.zero_tmul _ (1 : D.host.E)
  · have hu : u.1 ≠ v := fun e => u.2 (e ▸ hP)
    show (evalV D.host.F u.1 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h2 u.1 hu, TensorProduct.zero_tmul]

theorem mem_congGrp {D : D7} (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (h : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have h1 := h i j
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
  have : Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this] at h1
  exact h1

theorem mem_grpAt_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  intro D k _ _ _ _ q V g hg P hP
  obtain ⟨ε, h1, h2⟩ := q.above
  refine mem_congGrp V _ g fun i j => ?_
  have h3 := hg i j
  rw [h2] at h3
  rw [← h3]
  exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt h1 P hP)

end GlobalTheory.SuppGrp
end
