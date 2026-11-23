module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle524
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowthStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf



theorem base_term_norm_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∀ g : GA D V, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ = ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (n : GA D V) (h : GA D W), om (n * g, h) Φ = om (n, 1) (om (g, h) Φ) := by
    intro n h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hψn : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hω.std.1.2.1 x, ENNReal.ofReal_one]
  have hFm : Measurable (fun p : flagN d × GA D W =>
      ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ) := by
    refine Continuous.measurable ?_
    refine ((hG.2.1.comp continuous_snd).mul ?_).enorm
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hfib : ∀ h : GA D W, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
      ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν =
      ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
    intro h
    have hΨ : IsThetaFunO ψ V W (om (g, h) Φ) := hω.om_pres (g, h) Φ hΦ
    have hfm : Measurable (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) :=
      (((hTL _ hΨ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).enorm.measurable
    have hinv : ∀ c, ∀ n ∈ flagN d,
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) (d.nC c * n) =
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) n := by
      intro c n hn
      have hΨ' := hω.om_pres (n, 1) _ hΨ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      show ‖term ψ d W vS (om (d.nC c * n, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖term ψ d W vS (om (n, 1) (om (g, h) Φ)) x₀‖ₑ
      rw [t1, enorm_mul, hψn, one_mul]
      simp [term]
    have hval : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        ‖term ψ d W vS (om (d.nB b * d.levi u.1, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ := by
      intro u b
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul] at t1
      rw [t1, enorm_mul, hψn, one_mul]
      rfl
    have hl := hlay _ hfm hinv
    calc ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
          ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν
        = ‖G h‖ₑ * ∫⁻ n in 𝓐, ‖term ψ d W vS (om (n.1, 1) (om (g, h) Φ)) x₀‖ₑ ∂vN.ν := by
          rw [hl]
          simp only [hval]
      _ = ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          refine lintegral_congr fun n => ?_
          rw [enorm_mul, hsplit]
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFm.aemeasurable]
  refine lintegral_congr fun h => ?_
  exact hfib h

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec_mulVec, mt_unitary, form]

theorem act_vecX_of_mem_Nfix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (j : Fin ρ) (a : Fin ρ → AE D)
    (ha : ∀ i, j < i → a i = 0) {m : GA D V} (hm : m ∈ Nfix d j) : act V m (vecX d a) = vecX d a := by
  have hm' : ∀ i : Fin ρ, i ≤ j → ∀ k, (mt V m ⬝ d.jX : Mx D V.rank ρ) k i = d.jX k i := by
    intro i hi k
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hm).2) ⟨i, hi⟩
    have h2 := congrFun (congrFun (mem_fixer.1 h1) k) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using h2
  rw [act, vecX, Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ j
  · rw [hm' i hi k]
  · rw [ha i (not_le.1 hi), mul_zero, mul_zero]

theorem rat_mulVec_ratVec {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (a : Fin n → D.host.E) :
    rat x *ᵥ ratVec a = ratVec (x *ᵥ a) := by
  funext i
  exact (RingHom.map_mulVec (incA D) x a i).symm

theorem transv_trivial_after_Nfix : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  intro D hD ψ V V₀ W ρ d χV χW om hW vS Ψ hΨ j a ha v u hv hu x hx m hm n
  obtain ⟨-, hConj, hTriv⟩ := GlobalTheory.T.transvectionLemma_of_wittCoreDescent D hD
  have ha' : ∀ i, j < i → ratVec a i = 0 := fun i hi => by simp [ratVec, ha i hi]
  have hmw : act V m (vecX d (ratVec a)) = vecX d (ratVec a) := act_vecX_of_mem_Nfix d j _ ha' hm
  have hc := hConj V V₀ ρ d (ratVec a) v hv u m hu
  rw [hmw] at hc
  have hv' : form V (vecX d (ratVec a)) (act V m v) = 0 := by
    rw [← hmw, form_act_act, hv]
  have hx' : rat x *ᵥ ratVec a = 0 := by
    rw [rat_mulVec_ratVec, hx]
    funext i
    simp [ratVec]
  have e : ((m * u * n, (1 : GA D W)) : GA D V × GA D W) = (m * u * m⁻¹, 1) * (m * n, 1) := by
    ext
    · simp [mul_assoc]
    · simp
  have key := hTriv V V₀ W ρ d ψ χV χW om hW vS.μ vS.𝓕 vS.covol a (act V m v) hv' (m * u * m⁻¹) hc (rat x) hx'
    (om (m * n, 1) Ψ) (hW.om_pres _ _ hΨ)
  rw [term, term, e, map_mul, Module.End.mul_apply]
  exact congrFun key 0

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat' {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩



theorem unfold_norm_base_term_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν → IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∀ g : GA D V, ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) = ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro y
    have t4 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine (hG.2.1.comp continuous_snd).mul ?_
    exact t4.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1 * g, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat' W hq2
    have hΨ := hω.om_pres (p.1.1 * g, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1 * g, p.2) := by
        ext <;> simp [mul_assoc]
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) hGG key
  obtain ⟨hl, -⟩ := GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1) hmeas hinv
  simp only [hy₀] at hl
  exact hl

end GlobalTheory.Unf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SigConv

variable {D : D7}

theorem mt_jX_eq {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have e3 : blockX d n = 1 + T := by
    rw [blockX, h1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  rw [e3, h1, Matrix.mul_add, Matrix.mul_one]

theorem blockX_mul_inv {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    blockX d n ⬝ blockX d n⁻¹ = 1 := by
  have h1 := mt_jX_eq d (inv_mem hn)
  have h2 := mt_jX_eq d hn
  have h3 : d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹) = d.jX := by
    rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
      Matrix.one_mul]
  have h4 : d.pX ⬝ (d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹)) = d.pX ⬝ d.jX := by rw [h3]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h4

theorem blockX_rat {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ B : Matrix (Fin ρ) (Fin ρ) D.host.E, rat B = blockX d γ :=
  mem_ratMx.1 (ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V γ).1 hγ) (rat_mem d.e)))

def sumAbs (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ) : ENNReal :=
  ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS Ψ x‖ₑ

end GlobalTheory.Unf.SigConv


open GlobalTheory.Unf.SigConv in
theorem GlobalTheory.Unf.sum_term_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W χV χW om hW V₀ ρ d vS Φ hΦ
  have hT := fun Ψ (hΨ : IsThetaFunO ψ V W Ψ) => GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ

  have hA : ∀ g h, sumAbs ψ d W vS (om (g, h) Φ) ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    intro g h
    refine le_trans ?_ (hC g h 0)
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E =>
        (⟨rat x, rat_mem x⟩ : ratMx D W.rank ρ))
      (fun x y hxy => rat_injective (congrArg Subtype.val hxy))
      (fun y : ratMx D W.rank ρ => ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) y 0‖ₑ)

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ γ ∈ GQ V, γ ∈ flagN d →
      sumAbs ψ d W vS (om (γ, 1) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ γ hQ hN
    obtain ⟨B, hB⟩ := blockX_rat d hQ
    have key : ∀ x, term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ (x * B) :=
      fun x => (hT Ψ hΨ).2.1 γ hQ hN x (x * B) (by rw [rat_mul, hB])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => x * B) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : x * B = y * B := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => (rat z : Mx D W.rank ρ) ⬝ blockX d γ⁻¹) hxy'
    simp only [rat_mul, hB, Matrix.mul_assoc, blockX_mul_inv d hN, Matrix.mul_one] at h5
    exact h5

  have hD : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ δ ∈ GQ W,
      sumAbs ψ d W vS (om (1, δ⁻¹) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ δ hQ
    obtain ⟨M, hM⟩ := mem_ratMx.1 ((mem_GQ_iff W δ).1 hQ)
    have key : ∀ x, term ψ d W vS (om (1, δ⁻¹) Ψ) x = term ψ d W vS Ψ (M * x) :=
      fun x => (hT Ψ hΨ).2.2.1 δ⁻¹ (inv_mem hQ) x (M * x)
        (by rw [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => M * x) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : M * x = M * y := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => mt W δ⁻¹ ⬝ (rat z : Mx D W.rank ρ)) hxy'
    simp only [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul] at h5
    exact h5

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image continuous_subtype_val)
  set c' := max c 1 with hc'
  set C₀ := max C 0 with hC₀
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set C' := C₀ * c' ^ A with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _)

  have hN : ∀ g h, ∀ n ∈ flagN d, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * height W h) ^ A) := by
    intro g h n hn
    obtain ⟨γ, hγ, k, hk, hnk⟩ := hcov ⟨n, hn⟩
    have hγQ : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have hn' : n = γ.1 * k.1 := congrArg Subtype.val hnk
    have hp : ((n * g, h) : GA D V × GA D W) = (γ.1, 1) * (k.1 * g, h) := by
      rw [hn']; ext <;> simp [mul_assoc]
    have hom : om (n * g, h) Φ = om (γ.1, 1) (om (k.1 * g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    refine (hB _ (hW.om_pres _ _ hΦ) γ.1 hγQ γ.2).trans ((hA _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V k.1 ≤ c' := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (k.1 * g) ≤ c' * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx : height V (k.1 * g) * height W h ≤ c' * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (k.1 * g) * height W h) ^ A ≤ C₀ * (height V (k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ C₀ * (c' * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hC₀0
      _ = C' * (height V g * height W h) ^ A := by rw [mul_pow, hC', mul_assoc]
  refine ⟨C', A, fun g h n hn => ?_⟩

  have hδ : ∀ δ : GQ W, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * max (height W (δ.1 * h)) 0) ^ A) := by
    intro δ
    rw [max_eq_left (height_pos W _).le]
    have hp : ((n * g, h) : GA D V × GA D W) = (1, δ.1⁻¹) * (n * g, δ.1 * h) := by
      ext <;> simp [← mul_assoc]
    have hom : om (n * g, h) Φ = om (1, δ.1⁻¹) (om (n * g, δ.1 * h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    exact (hD _ (hW.om_pres _ _ hΦ) δ.1 δ.2).trans (hN g _ n hn)
  let φ : ℝ → ENNReal := fun t => ENNReal.ofReal (C' * (height V g * max t 0) ^ A)
  have hmono : Monotone φ := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC'0
    apply pow_le_pow_left₀ (mul_nonneg (height_pos V g).le (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) (height_pos V g).le
  have hcont : Continuous φ := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have hinf := hmono.map_ciInf_of_continuousAt (g := fun δ : GQ W => height W (δ.1 * h)) hcont.continuousAt
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height W _⟩
  have hq : ENNReal.ofReal (C' * (height V g * quotHeight W h) ^ A) = φ (quotHeight W h) := by
    simp only [φ, max_eq_left (quotHeight_pos W h).le]
  change sumAbs ψ d W vS (om (n * g, h) Φ) ≤ _
  rw [hq, quotHeight, hinf]
  exact le_iInf hδ
end
end
