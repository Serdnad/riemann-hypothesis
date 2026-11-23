module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
noncomputable section

namespace GlobalTheory.TrConv

variable {D : D7}

theorem finFn_eq_tensorFin (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (y : GfC V) :
    finFn V ff y = tensorFin D.sp.cm.sig V.gram ff ((finPtsEquiv D.sp.cm.sig V.gram).symm y) := by
  unfold finFn tensorFin
  refine finprod_congr fun v => congrArg (ff v) ?_
  have := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm y)
  rw [← this]
  congr 1
  exact (congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y)).symm

theorem conv_finFn : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  intro D V μf _ h1 ν hν a b ha hb
  refine ⟨GlobalTheory.Orb.IsFinFamily.conv ha hb h1, funext fun y => ?_, ?_⟩
  · have hfam := GlobalTheory.Orb.IsFinFamily.mul_translate ha hb (y : GA D V)
    have hint : (fun x : GfC V => finFn V a x * finFn V b (x⁻¹ * y)) =
        finFn V (fun v x => a v x * b v (x⁻¹ * proj D.sp.cm.sig V.gram v (y : GA D V))) := by
      funext x
      have e1 := ha.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have e2 := hb.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      rw [finFn_eq_tensorFin, finFn_eq_tensorFin]
      unfold finFn
      unfold tensorFin
      rw [← finprod_mul_distrib e1 e2]
      refine finprod_congr fun v => ?_
      have p1 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have p2 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      have q1 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm x) = (x : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply x)
      have q2 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y)) = ((x⁻¹ * y : GfC V) : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply _)
      rw [q1] at p1
      rw [q2] at p2
      rw [← p1, ← p2]
      simp [map_mul, map_inv]
    symm
    show ∫ x, finFn V a x * finFn V b (x⁻¹ * y) ∂ν = _
    rw [hint, hν.2 _ hfam]
    rfl
  · have hm := ha.tensorFin_mem
    rw [show finFn V a = tensorFin D.sp.cm.sig V.gram a ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
      funext fun y => finFn_eq_tensorFin V a y]
    exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
      hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

end GlobalTheory.TrConv
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
open scoped Pointwise

namespace GlobalTheory.RopRep

theorem rop_rep : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  intro D V μ _ _ f hf F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hloc : LocallyIntegrable (lift (GQ V) F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ := fun x =>
    hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _))
      (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq f _ x).symm
  refine ⟨hint, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
    have hC : IsCompact (K * tsupport f) := hK.mul hfs
    have hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ :=
      (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2
    refine continuousAt_of_dominated
      (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖)
      (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)
    · filter_upwards [hKx] with x hx
      refine .of_forall fun y => ?_
      by_cases hy : f (x⁻¹ * y) = 0
      · rw [hy, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _
      · have hmem : y ∈ K * tsupport f :=
          ⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩
        rw [Set.indicator_of_mem hmem, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)
    · exact ((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt
  · rw [hconv]
    exact (leftInv_lift _).convR f
  · rw [hconv]
    exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f
      (hfc.integrable_of_hasCompactSupport hfs) F).2

end GlobalTheory.RopRep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open scoped Pointwise TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.FrameCong

variable {D : D7}

theorem intAt_mul_mem {S : HSp D} {L : Lat S} {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (fun i => a * y i) ∈ latV S L (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hint : a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAt D (· = v) := by
      refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
      rw [RingHom.map_mul]
      exact FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have h := FrameLat.int_mul_mem hint hx
    have h1 : ∀ i, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (x i) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) := fun i => by
      change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simpa only [mul_assoc, h1] using h
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem inc_mul_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {𝔪 : Ideal (𝓞 D.host.E)} {m : 𝓞 D.host.E} (hm : m ∈ 𝔪)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα0, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα0, 1, rfl, m • x, Submodule.smul_mem_smul hm hx, ?_⟩
    funext i
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul]
    rfl
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem sub_one_mulVec_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n]
    [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
    β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
    (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k],
      (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
    ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
    ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
    (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈
      latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p S L n _ _ β hβ 𝔪 d ⟨m, hm, hmd⟩ k₀ hk y hy
  have hpi : ∀ x : n → k, x ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) ↔ ∀ j, x j ∈ 𝒪[k] := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨x j, h⟩, rfl⟩⟩
    rintro ⟨z, hz⟩
    rw [← hz]; exact z.2
  set g : GL n k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ with hg
  set Y : Fin S.rank → k := fun i => p.pr (y i) with hY
  set x : n → k := β.b' *ᵥ Y with hx
  have hbx : β.b *ᵥ x = Y := by rw [hx, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  have hxint : ∀ j, x j ∈ 𝒪[k] := by
    rw [← hpi, hβ x, hbx]
    simp only [hY, p.sec_pr]
    exact intAt_mul_mem (FrameLat.e_mem_intAt p) hy
  let x₀ : n → 𝒪[k] := fun j => ⟨x j, hxint j⟩
  have hz : ∀ i, ((k₀.1 - 1) *ᵥ x₀) i ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d := fun i =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hk i j)
  choose c hc hcz using fun i => hmd _ (hz i)
  have hgx : (g.val - 1) *ᵥ x = p.pr (incA D (m : D.host.E)) • c := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← hcz i]
    have h1 : g.val - 1 = (k₀.1 - 1).map (algebraMap 𝒪[k] k) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    rw [h1]
    exact (RingHom.map_mulVec (algebraMap 𝒪[k] k) (k₀.1 - 1) x₀ i).symm
  have hpr : ∀ i, p.pr (((mt S (β.gl g) - 1) *ᵥ y) i) = p.pr (incA D (m : D.host.E)) * (β.b *ᵥ c) i := by
    intro i
    rw [RingHom.map_mulVec, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), β.gl_mat g]
    have h2 : β.b * g.val * β.b' - 1 = β.b * (g.val - 1) * β.b' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, β.bb']
    rw [h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (β.b *ᵥ ((g.val - 1) *ᵥ x)) i = _
    rw [hgx, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hc' := (hβ c).1 ((hpi c).2 hc)
  have h := inc_mul_mem hm hc'
  have heq : (fun i => p.e * ((mt S (β.gl g) - 1) *ᵥ y) i) =
      fun i => incA D (m : D.host.E) * p.sec ((β.b *ᵥ c) i) := by
    funext i
    rw [← p.sec_pr, hpr, mul_comm (incA D _), FrameLat.sec_mul_right, mul_comm]
  rw [heq]
  exact h

end GlobalTheory.FinPl.FrameCong
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.RatClasses

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {J : Matrix (Fin n) (Fin n) E} {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']

theorem mapsCls_unique {ψ : k →ₐ[F] k'} {q : Cls P k} {a b : Cls P k'} (ha : MapsCls P ψ q a)
    (hb : MapsCls P ψ q b) : a = b := by
  obtain ⟨x, x', hx, rfl, ex⟩ := ha
  obtain ⟨y, y', hy, rfl, ey⟩ := hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))
  let m := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))
  have hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [m, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)
  have hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1 := by
    have : c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1 := congrArg Units.val hc
    rw [this, Units.val_mul, Units.mul_inv_cancel_left]
  change _ = x'.1⁻¹ * y'.1
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  change x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1
  rw [ex, ey, hm, ← hc', map_mul, map_mul]

theorem mapH_diagH (ψ : k →ₐ[F] k') (γ : Formalism.UG.UJ (σ : E →+* E) J) :
    mapH σ J ψ (diagH σ J k γ) = diagH σ J k' γ :=
  Subtype.ext (Units.ext (Matrix.ext fun r s => by
    change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s)
    simp))

variable [NumberField F] [NumberField E] (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
include hc hJ

theorem hasCls_unique {γ : HA k σ J} {q q' : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ q') : q = q' := by
  obtain ⟨x, φ, h, rfl, e⟩ := h
  obtain ⟨x', φ', h', rfl, e'⟩ := h'
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])

theorem hasCls_of_isConj {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (e : IsConj γ γ') :
    HasCls P k J γ' q := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.1 e
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g

theorem isConj_of_hasCls {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ' q) :
    IsConj γ γ' := by
  obtain ⟨x, φ, h, e, rfl⟩ := h
  obtain ⟨x', φ', h', e', rfl⟩ := h'
  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)
  exact isConj_iff.2 ⟨g, (hg _).symm⟩

theorem exists_mapsCls (ψ : k →ₐ[F] k') {γ : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) :
    ∃ q', MapsCls P ψ q q' ∧ HasCls P k' J (mapH σ J ψ γ) q' := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨x', φ', h', e1, e2, -⟩ := GlobalTheory.T.hermitian_isometry_base_change F E σ hc r n P J hJ k k' ψ x φ h
  exact ⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩

theorem exists_mapsCls_rat (k : Type) [CommRing k] [Algebra F k] {γ : GRat σ J} {q : Cls P F}
    (h : HasCls P F J (diagH σ J F γ) q) :
    ∃ q', MapsCls P (k := F) (Algebra.ofId F k) q q' ∧ HasCls P k J (diagH σ J k γ) q' := by
  simpa only [mapH_diagH] using exists_mapsCls hc hJ (Algebra.ofId F k) h

theorem exists_hasCls_rat {P : PPol σ n} (γ : GRat σ J) (h : γ.1.1.charpoly = P.1) :
    ∃ q, HasCls P F J (diagH σ J F γ) q := by
  obtain ⟨P', e, hq⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)
  obtain rfl : P' = P := Subtype.ext (e.symm.trans h)
  exact hq

theorem charpoly_of_hasCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) :
    γ.1.1.charpoly = P.1 := by
  obtain ⟨x, φ, h, -, e⟩ := h
  have h1 := (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hc r n P J hJ F x φ h).1
  rw [e] at h1
  apply Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective
  rw [← h1, ← Matrix.charpoly_map]
  rfl

theorem isConj_of_diagH {γ γ' : GRat σ J} (h : IsConj (diagH σ J F γ) (diagH σ J F γ')) : IsConj γ γ' := by
  have hb := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).1
  obtain ⟨g, e⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hb.2 g
  exact isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩

theorem existsUnique_hasCls_rat {P : PPol σ n} (k : Type) [CommRing k] [Algebra F k] (γ : GRat σ J)
    (h : γ.1.1.charpoly = P.1) : ∃! q, HasCls P k J (diagH σ J k γ) q := by
  obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
  obtain ⟨q', -, hq'⟩ := exists_mapsCls_rat hc hJ k hq
  exact ⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩

theorem exists_common {γ γ' : GRat σ J} {q q' : Cls P F} (h : HasCls P F J (diagH σ J F γ) q)
    (h' : HasCls P F J (diagH σ J F γ') q')
    (H : ∀ a, HasCls P k J (diagH σ J k γ) a → HasCls P k J (diagH σ J k γ') a) :
    ∃ a, MapsCls P (k := F) (Algebra.ofId F k) q a ∧ MapsCls P (k := F) (Algebra.ofId F k) q' a := by
  obtain ⟨a, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  obtain ⟨b, h3, h4⟩ := exists_mapsCls_rat hc hJ k h'
  exact ⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩

theorem hasCls_of_mapsCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) {a : Cls P k}
    (H : MapsCls P (k := F) (Algebra.ofId F k) q a) : HasCls P k J (diagH σ J k γ) a := by
  obtain ⟨b, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  exact mapsCls_unique h1 H ▸ h2

end General

theorem rat_classes_iff_local (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E)
    (hJ : IsHermND σ J) :
    (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧
      (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧
      ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧
    (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔
      (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧
        ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧
    ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion),
      (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) →
      ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧
        ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  have e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ := proj_ratEmb σ J
  have e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ := projArch_ratEmb σ J
  obtain ⟨H1, H2⟩ := GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ
  refine ⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩,
    fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩
  · rw [e1]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · rw [e2]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · have := isLattice_stdLattice (E := E) (n := r)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hc r P J hJ (stdLattice E r),
      eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm
    obtain ⟨q, hq, -⟩ := existsUnique_hasCls_rat hc hJ (Fv F v) γ h
    rw [← e1] at hq
    exact hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq
  · exact hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))
  · exact hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))
  · simp only [e1, e2] at H
    obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
    obtain ⟨q', hq'⟩ := exists_hasCls_rat hc hJ γ' h'
    obtain rfl : q = q' := H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v))
      fun w => exists_common hc hJ hq hq' (H.2 w)
    exact isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')
  · obtain ⟨q, hq, h2, h3⟩ := H2 qf qa hf ha h1
    obtain ⟨g, hg⟩ := exists_hasCls P hq
    obtain ⟨γ, rfl⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc r J hJ).1.2 g
    refine ⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩
    · rw [e1]; exact hasCls_of_mapsCls hc hJ hg (h2 v)
    · rw [e2]; exact hasCls_of_mapsCls hc hJ hg (h3 w)

end GlobalTheory.TrEll.RatClasses
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.PoinTerm

theorem norm_coef_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  intro D θ hθ V S M K v hv b hb
  choose C hC using fun τ => (hv τ).2 (b τ) (hb τ)
  have hpos : ∀ (τ : D.what₂.Tau) (x : GA D V), 0 < (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) := fun τ x =>
    pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hle : ∀ (τ : D.what₂.Tau) (x : GA D V), ‖⟪v τ, M.rep τ (cmp θ τ x) (b τ)⟫_ℂ‖ * (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) ≤ C τ :=
    fun τ x => hC τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
  have h0 : ∀ τ, 0 ≤ C τ := fun τ => (mul_nonneg (norm_nonneg _) (hpos τ 1).le).trans (hle τ 1)
  have hP : 0 ≤ ∏ τ, C τ := Finset.prod_nonneg fun τ _ => h0 τ
  refine ⟨∏ τ, C τ, hP, fun x => ?_⟩
  unfold coef
  split_ifs
  · unfold coefR
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hpos τ x)]
    exact hle τ x
  · rw [norm_zero]
    exact mul_nonneg hP (Finset.prod_nonneg fun τ _ => (inv_pos.2 (hpos τ x)).le)

end GlobalTheory.PoinTerm
end
