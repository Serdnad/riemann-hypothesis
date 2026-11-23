module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.ThetaLifts.CTKernel
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003

@[expose] public section

section

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem mat_mul' {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mulVec {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {x y : Fin n → AE F E} (h : mat g *ᵥ x = y) :
    mat g⁻¹ *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mulVec]

theorem pair_pres (hp : IsPair B M χX χW om r s r' s') (x) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om x Φ ∈ schA F _ :=
  (IsUWeilPair.isUSplitting hp.weil).pres x Φ hΦ

theorem pair_cont (hp : IsPair B M χX χW om r s r' s') {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous fun x => l (om x Φ) :=
  (IsUWeilPair.isUSplitting hp.weil).cont l hl Φ hΦ

theorem pair_adm (hp : IsPair B M χX χW om r s r' s') (x) {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) :
    l ∘ₗ om x ∈ (adeleClass F).adm (Fin n × Fin d) :=
  (IsUWeilPair.isUSplitting hp.weil).adm x l hl

theorem om_mul (om : Rep σ X W) (x y) (Φ) : om x (om y Φ) = om (x * y) Φ := by rw [map_mul]; rfl

theorem rho_om (hp : IsPair B M χX χW om r s r' s') (g h) (a : Fin n → AE F E) (b : Fin d → AE F E) (c : AE F E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (c • Matrix.vecMulVec a b) (om (g, h) Φ) =
      om (g, h) (M.co.rho B.ψ (c • Matrix.vecMulVec (mat g⁻¹ *ᵥ a) (mat h⁻¹ *ᵥ b)) Φ) := by
  rw [(IsUWeilPair.isUSplitting hp.weil).impl (g, h) _ Φ hΦ]
  congr 2
  change _ = mat g * _ * (mat h)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul', ← mat_mul', mul_inv_cancel, mul_inv_cancel, mat_one', mat_one',
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem rho_linear (M : Model σ X W) (ψ) (u) {ι : Type} (t : Finset ι) (c : ι → ℂ) (Φ : ι → Fn F n d) :
    M.co.rho ψ u (∑ i ∈ t, c i • Φ i) = ∑ i ∈ t, c i • M.co.rho ψ u (Φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ev_adm {κ : Type} [Fintype κ] (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  classical
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem kfin_dec (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hK : KFinite om K Φ) (S : Submodule ℂ (Fn F n d)) (hS : ∀ k : K, om (k.1, 1) Φ ∈ S) :
    ∃ (m : ℕ) (Ψ : Fin m → Fn F n d) (c : Fin m → K → ℂ), (∀ i, Ψ i ∈ S) ∧ (∀ i, Continuous (c i)) ∧
      ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i := by
  set V := Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) Φ)
  haveI : FiniteDimensional ℂ V := hK
  let b := Module.finBasis ℂ V
  have hc : Continuous fun k : K => (⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ : V) := by
    refine Continuous.subtype_mk (continuous_pi fun y => ?_) _
    exact (pair_cont hp (ev_adm y) hΦ).comp (continuous_subtype_val.prodMk continuous_const)
  refine ⟨_, fun i => (b i).1, fun i k => b.repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ i,
    fun i => Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k) (b i).2,
    fun i => (b.coord i).continuous_of_finiteDimensional.comp hc, fun k => ?_⟩
  have := congrArg Subtype.val (b.sum_repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩)
  rw [Submodule.coe_sum] at this
  exact this.symm

end Basic

end PositivityTheory.ThKCT

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _) ?_
  refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
  have := (jet k j f).norm_coe_le_norm x
  rwa [jet_apply, norm_smul, norm_pow, norm_norm] at this

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ :=
  (hI k j).mono' ((J k j).continuous.comp hG).aestronglyMeasurable (.of_forall fun a => (norm_jet k j _).le)

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp ((J 0 j).continuous.comp hG)
  refine this.congr fun a => ?_
  change jet 0 j (G a) x = _
  rw [jet_apply, pow_zero, one_smul]

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  simpa using SchwartzMap.le_seminorm ℂ 0 j f x

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ :=
  (hI 0 j).mono' (cont_D hG j x).aestronglyMeasurable (.of_forall fun a => bd_D _ j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ) (x₀ := x)
    (F := fun y a => iteratedFDeriv ℝ j (G a) y) (F' := fun y a => L (iteratedFDeriv ℝ (j + 1) (G a) y))
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) univ_mem
    (.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x)
    (L.continuous.comp (cont_D hG (j + 1) x)).aestronglyMeasurable
    (.of_forall fun a y _ => by rw [L.norm_map]; exact bd_D _ _ y) (hI 0 (j + 1))
    (.of_forall fun a y _ => ((cd (G a) (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) y).hasFDerivAt)
  have e := L.toContinuousLinearEquiv.integral_comp_comm (μ := μ) fun a => iteratedFDeriv ℝ (j + 1) (G a) x
  exact h.congr_fderiv e

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ :=
  ⟨fun x => ((continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.integral_comp_comm (μ := μ)
      fun a => iteratedFDeriv ℝ 0 (G a) x).symm,
    fun j _ x => deriv_D hG hI j x,
    fun j _ => continuous_iff_continuousAt.2 fun x => (deriv_D hG hI j x).continuousAt⟩

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  rw [← (taylor hG hI).eq_iteratedFDeriv (by exact_mod_cast le_top) x, ← integral_smul]
  exact ((BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm (int_J hG hI k j)).symm

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k j => ⟨‖∫ a, J k j (G a) ∂μ‖, fun x => ?_⟩⟩, fun k j => ?_⟩
  · have := (∫ a, J k j (G a) ∂μ).norm_coe_le_norm x
    rwa [eval_int hG hI, norm_smul, norm_pow, norm_norm] at this
  · ext1 x
    rw [eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let j : SchwartzMap V ℂ →ₗ[ℂ] ∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ) := LinearMap.pi fun i => (J i.1.1 i.1.2).toLinearMap
  have hb : ∀ f, ‖T f‖ ≤ C * ‖j f‖ := fun f => by
    refine (h f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_jet i.1 i.2 f).ge.trans (norm_le_pi_norm (j f) ⟨i, hi⟩)
  have hk : LinearMap.ker j ≤ LinearMap.ker T.toLinearMap := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let t : LinearMap.range j →ₗ[ℂ] ℂ := ((LinearMap.ker j).liftQ T.toLinearMap hk) ∘ₗ j.quotKerEquivRange.symm.toLinearMap
  have ht : ∀ f, t ⟨j f, f, rfl⟩ = T f := fun f => by
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [j.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (t.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [ht]
    exact hb f))
  exact ⟨s, g, fun f => ((hg ⟨j f, f, rfl⟩).trans (ht f)).symm⟩

end SchI

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem summable_lat_wt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sz {κ : Type} [Fintype κ] (y : κ → AF F) : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))

theorem norm_le_sz {κ : Type} [Fintype κ] (y : κ → AF F) : 1 + ‖fun j => evI F (y j)‖ ≤ sz y := by
  have h0 : ∀ j, 0 ≤ ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) := fun j =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  refine add_le_add_right ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => h0 j)).2 fun j => ?_) 1
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j))
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (y j)))
    (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)

theorem sz_pos {κ : Type} [Fintype κ] (y : κ → AF F) : 0 < sz y := lt_of_lt_of_le (by positivity) (norm_le_sz y)

theorem summable_wt {κ : Type} [Fintype κ] {C : Set (κ → Af F)} (hC : IsCompact C) : ∃ N : ℕ, Summable fun ξ : κ → F =>
    if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then (sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 := by
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hC
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, ?_⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine if_neg fun h0 => hξ ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ h0 i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_)
      ((summable_lat_wt (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj)
    · simp only [Function.comp_apply]
      split_ifs
      · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
      · exact le_rfl
    · simp only [Function.comp_apply]
      split_ifs
      · rw [inv_pow]
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := norm_le_sz (fun i => algebraMap F (AF F) (ξ.1 i))
        have e : (fun i => evI F (algebraMap F (AF F) (ξ.1 i))) = fun i => mixedEmbedding F (ξ.1 i) :=
          funext fun i => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
        rw [e] at h
        exact h
      · positivity

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_bound (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ (wt : (Fin m → F) → ℝ) (P : SInf F (Fin n × Fin d) → ℝ), Summable wt ∧ Continuous P ∧ P 0 = 0 ∧
      ∀ y (f : SInf F (Fin n × Fin d)),
        ‖l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) (pureA F f φ)))‖ ≤ P f * wt y := by
  obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨N, hN⟩ := summable_wt hC
  choose T hT using fun i => hl (φ₁ i) (h1 i)
  choose p hp hq using fun i => h4 ((normSeminorm ℂ ℂ).comp (T i).toLinearMap) N (T i).continuous.norm
  refine ⟨_, fun f => ∑ i, p i f, hN, continuous_finsetSum _ fun i _ => hp i, by simp, fun y f => ?_⟩

  rw [h2, map_sum]
  simp only [hT]
  split_ifs with hy
  · rw [Finset.sum_mul]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
    exact hq i i _ f
  · simp [h3 _ _ hy]

end PositivityTheory.ThKCT
end
end
