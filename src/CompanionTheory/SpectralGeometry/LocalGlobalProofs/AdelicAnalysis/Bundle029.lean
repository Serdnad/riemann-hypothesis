module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import GroundTheory.GlobalFields.Adele.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SizeInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def compReal (hF : IsTotallyReal F) (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal v)

theorem continuous_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).continuous

theorem continuous_compReal_symm (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v).symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).symm.continuous

theorem norm_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) (x : v.Completion) :
    ‖compReal hF v x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal v)).norm_map_of_map_zero
    (map_zero _) x

theorem secondCountable_Ainf (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).toHomeomorph.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

section Coord

variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)

def ainfEquiv : Ainf F ≃+ (InfinitePlace F → ℝ) where
  toFun x v := compReal hF v (x v)
  invFun w := (fun v => (compReal hF v).symm (w v) : ∀ v : InfinitePlace F, v.Completion)
  left_inv x := by funext v; exact (compReal hF v).symm_apply_apply _
  right_inv w := by funext v; exact (compReal hF v).apply_symm_apply _
  map_add' x y := by funext v; exact map_add (compReal hF v) (x v) (y v)

theorem continuous_ainfEquiv : Continuous (ainfEquiv hF) :=
  continuous_pi fun v => (continuous_compReal hF v).comp (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v)

theorem continuous_ainfEquiv_symm : Continuous (ainfEquiv hF).symm := by
  have h : Continuous fun (w : InfinitePlace F → ℝ) (v : InfinitePlace F) =>
      ((compReal hF v).symm (w v) : v.Completion) :=
    continuous_pi fun v => (continuous_compReal_symm hF v).comp (continuous_apply v)
  exact h

def coordEquiv : Ainf F ⊗[F] E ≃+ (Fin d → InfinitePlace F → ℝ) :=
  (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => ainfEquiv hF)

theorem abs_coordEquiv (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F) :
    ‖coordEquiv hF b y k v‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ :=
  norm_compReal hF v _

def tupEquiv (n M : ℕ) :
    (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => coordEquiv hF b

theorem tupEquiv_apply (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := rfl

theorem norm_tupEquiv_le (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    ‖tupEquiv hF b n M X‖ ≤ sizeTup b X := by
  have h0 : ∀ (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F),
      0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ := fun _ _ _ => norm_nonneg _
  have hI : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 y k v
  have hT : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI _
  refine (pi_norm_le_iff_of_nonneg hT).2 fun a => (pi_norm_le_iff_of_nonneg hT).2 fun i =>
    (pi_norm_le_iff_of_nonneg hT).2 fun k => (pi_norm_le_iff_of_nonneg hT).2 fun v => ?_
  rw [tupEquiv_apply, abs_coordEquiv]
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖
      ≤ ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖ :=
        Finset.single_le_sum (f := fun v' => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖)
          (fun v' _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k' => ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k' v'‖)
          (fun k' _ => Finset.sum_nonneg fun v' _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i', sizeInf b (X a i') :=
        Finset.single_le_sum (f := fun i' => sizeInf b (X a i')) (fun i' _ => hI _) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a' => ∑ i', sizeInf b (X a' i'))
          (fun a' _ => Finset.sum_nonneg fun i' _ => hI _) (Finset.mem_univ a)

theorem continuous_coordEquiv
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b) :=
  continuous_pi fun k => (continuous_ainfEquiv hF).comp ((continuous_apply k).comp hc.continuous)

theorem continuous_coordEquiv_symm
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b).symm := by
  have h1 : Continuous fun w : Fin d → InfinitePlace F → ℝ => fun k => (ainfEquiv hF).symm (w k) :=
    continuous_pi fun k => (continuous_ainfEquiv_symm hF).comp (continuous_apply k)
  have h2 := (hc.homeomorph _).symm.continuous.comp h1
  convert h2 using 1
  funext w
  apply (hc.homeomorph _).injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis (Ainf F) b).repr ((coordEquiv hF b).symm w) k = _
  apply (ainfEquiv hF).injective
  rw [AddEquiv.apply_symm_apply]
  have := congrFun ((coordEquiv hF b).apply_symm_apply w) k
  exact this

end Coord

theorem size_neg_pow_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM d b n M μ hμ
  have hF : IsTotallyReal F := hCM.1
  haveI : SecondCountableTopology (Ainf F) := secondCountable_Ainf hF
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  obtain ⟨hring, -, -, -, -, -, hhom, hborel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hring
  haveI := hborel n M
  have hc := hhom d b
  have hce := continuous_coordEquiv hF b hc
  have hcs := continuous_coordEquiv_symm hF b hc
  have hnorm : ∀ y : Ainf F ⊗[F] E, sizeInf b y = ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := fun y => by
    simp only [abs_coordEquiv, sizeInf]
  have hcontI : Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
    have : (sizeInf b : Ainf F ⊗[F] E → ℝ) = fun y => ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := funext hnorm
    rw [this]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
    exact ((continuous_apply v).comp ((continuous_apply k).comp hce)).norm
  have hcontT : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
    exact hcontI.comp ((continuous_apply i).comp (continuous_apply a))
  have hI0 : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  have hT0 : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X := fun X =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI0 _
  refine ⟨hcontT, hT0, ?_⟩
  let e := tupEquiv hF b n M
  have he : Continuous e :=
    continuous_pi fun a => continuous_pi fun i => hce.comp ((continuous_apply i).comp (continuous_apply a))
  have hes : Continuous e.symm :=
    continuous_pi fun a => continuous_pi fun i => hcs.comp ((continuous_apply i).comp (continuous_apply a))
  let W := Fin n → Fin M → Fin d → InfinitePlace F → ℝ
  haveI b1 : BorelSpace (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI s1 : SecondCountableTopology (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b2 : BorelSpace (Fin M → Fin d → InfinitePlace F → ℝ) := Pi.borelSpace
  haveI s2 : SecondCountableTopology (Fin M → Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b3 : BorelSpace W := Pi.borelSpace
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨N, hN⟩ := exists_nat_gt (Module.finrank ℝ W : ℝ)
  refine ⟨N, ?_⟩
  have hfin := finite_integral_one_add_norm (μ := Measure.map e μ) (E := W) (r := (N : ℝ)) hN
  have hmeas : Measurable fun y : W => ENNReal.ofReal ((1 + ‖y‖) ^ (-(N : ℝ))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (by positivity)).measurable
  rw [lintegral_map hmeas he.measurable] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun X => ?_) hfin
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (0 : ℝ) < 1 + ‖e X‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_natCast]
  have h2 : 1 + ‖e X‖ ≤ 1 + sizeTup b X := by
    have := norm_tupEquiv_le hF b n M X
    linarith
  exact inv_anti₀ (pow_pos h1 N) (pow_le_pow_left₀ h1.le h2 N)

end GlobalTheory.CompanionTheory.SW.SizeInt
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleHaar

theorem exists_haar_integral_one : ∀ (F : Type) [Field F] [NumberField F],
    ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧
      lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _
  have : BorelSpace (Af F) := ⟨rfl⟩
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F :
        Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  refine ⟨Measure.addHaarMeasure (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F),
    inferInstance, ?_⟩
  rw [hset]
  exact Measure.addHaarMeasure_self

end GlobalTheory.CompanionTheory.AdeleHaar
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Averaging

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]

theorem setLIntegral_mul_right_eq (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant]
    [μ₁.IsMulRightInvariant] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕₁ : Set G₁)
    (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁) (f : G₁ → ℝ≥0∞)
    (hf : ∀ γ ∈ Γ₁, ∀ u, f (γ * u) = f u) (u₀ : G₁) :
    ∫⁻ u in 𝓕₁, f (u * u₀) ∂μ₁ = ∫⁻ u in 𝓕₁, f u ∂μ₁ := by
  rw [(measurePreserving_mul_right μ₁ u₀).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight u₀).measurableEmbedding f 𝓕₁]
  have h2 : IsFundamentalDomain Γ₁ ((Equiv.mulRight u₀) '' 𝓕₁) μ₁ :=
    h𝓕₁.image_of_equiv (Equiv.mulRight u₀)
      (by
        rw [Equiv.mulRight_symm]
        exact (measurePreserving_mul_right μ₁ u₀⁻¹).quasiMeasurePreserving)
      (Equiv.refl _) (fun g => by
        intro x
        simp only [Equiv.coe_mulRight, Equiv.refl_apply, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  exact h2.setLIntegral_eq h𝓕₁ f (fun g x => by
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hf g g.2 x)

theorem bijective_pair (ι : G₁ →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    {Q : Type} (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) :
    Function.Bijective (fun p : Q × Γ₁ =>
      (⟨ι (p.2 : G₁)⁻¹ * r p.1, Γ.mul_mem (hΓ _ (Γ₁.inv_mem p.2.2)) (hr p.1)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, v⟩ ⟨q', v'⟩ h
    have hval : ι (v : G₁)⁻¹ * r q = ι (v' : G₁)⁻¹ * r q' := congrArg Subtype.val h
    obtain ⟨q₀, -, huniq⟩ := hQ _ (Γ.mul_mem (hΓ _ (Γ₁.inv_mem v.2)) (hr q))
    have hq : q = q' := by
      rw [huniq q ⟨(v : G₁)⁻¹, Γ₁.inv_mem v.2, rfl⟩, huniq q' ⟨(v' : G₁)⁻¹, Γ₁.inv_mem v'.2, hval⟩]
    subst hq
    have h3 : ι (v : G₁)⁻¹ = ι (v' : G₁)⁻¹ := mul_right_cancel hval
    have hv : (v : G₁) = v' := inv_injective (hι h3)
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext hv
  · rintro ⟨γ, hγ⟩
    obtain ⟨q, ⟨u, hu, hγu⟩, -⟩ := hQ γ hγ
    refine ⟨(q, ⟨u⁻¹, Γ₁.inv_mem hu⟩), ?_⟩
    apply Subtype.ext
    show ι (u⁻¹)⁻¹ * r q = γ
    rw [inv_inv]
    exact hγu.symm

theorem lintegral_sum_cosets_eq (ι : G₁ →* G) (hιc : Continuous ι) (hι : Function.Injective ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant] [μ₁.IsInvInvariant]
    (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁]
    (𝓕 : Set G) (𝓕₁ : Set G₁)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁)
    (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ) {Q : Type} [Countable Q] (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q)
    (w : G → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1)
    (ψ : G → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ u ∈ Γ₁, ∀ g, ψ (ι u * g) = ψ g) :
    ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ = ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ := by
  have hιm : Measurable ι := hιc.measurable
  have hm1 : Measurable (fun p : G × G₁ => ι p.2 * p.1) :=
    ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hm2 : Measurable (fun p : G₁ × G => (ι p.1)⁻¹ * p.2) :=
    ((hιc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm3 : Measurable (fun p : G × G₁ => (ι p.2)⁻¹ * p.1) :=
    ((hιc.comp continuous_snd).inv.mul continuous_fst).measurable
  have hWm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) :=
    (hw.comp hm3).lintegral_prod_right'
  have hFm : Measurable (fun g : G => ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) := hψ.mul hWm
  have hsumW : ∀ x : G, ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * x)) ∂μ₁ = 1 := by
    intro x
    have h0 : ∫⁻ y, w ((ι y)⁻¹ * x) ∂μ₁ = 1 := by
      have h := lintegral_inv_eq_self (μ := μ₁) (fun y => w (ι y * x))
      simp only [map_inv] at h
      rw [h, hw1 x]
    rw [← h0, h𝓕₁.lintegral_eq_tsum'' (fun y => w ((ι y)⁻¹ * x))]
    refine tsum_congr fun v => lintegral_congr fun u => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, map_mul, map_inv, mul_inv_rev, mul_assoc]
  have key : ∀ u : G₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ = ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ := by
    intro u
    have h := lintegral_mul_left_eq_self (μ := μ) (fun x => w ((ι u)⁻¹ * x) * ψ x) (ι u)
    simp only [inv_mul_cancel_left] at h
    exact h
  have hpt : ∀ h : G, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ =
      ∑' q, ψ (r q * h) := by
    intro h
    let E := Equiv.ofBijective _ (bijective_pair ι hι Γ Γ₁ hΓ r hr hQ)
    let F : G → ℝ≥0∞ := fun x => ψ x * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * x) ∂μ₁
    calc ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁
        = ∑' p : Q × Γ₁, F (E p • h) := (E.tsum_eq (fun γ => F (γ • h))).symm
      _ = ∑' q, ∑' v : Γ₁, F (E (q, v) • h) := ENNReal.tsum_prod (f := fun q v => F (E (q, v) • h))
      _ = ∑' q, ψ (r q * h) * ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * (r q * h))) ∂μ₁ := by
          refine tsum_congr fun q => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun v => ?_
          show ψ ((ι (v : G₁)⁻¹ * r q) * h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * ((ι (v : G₁)⁻¹ * r q) * h)) ∂μ₁ = _
          rw [mul_assoc, hinv _ (Γ₁.inv_mem v.2)]
      _ = ∑' q, ψ (r q * h) := by simp only [hsumW, mul_one]
  symm
  calc ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ
      = ∫⁻ g, ∫⁻ u in 𝓕₁, w g * ψ (ι u * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (w g) (f := fun u => ψ (ι u * g)) (hψ.comp (hιm.mul_const g))]
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ ∂μ₁ :=
        lintegral_lintegral_swap ((hw.comp measurable_fst).mul (hψ.comp hm1)).aemeasurable
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ ∂μ₁ := lintegral_congr fun u => key u
    _ = ∫⁻ g, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) * ψ g ∂μ₁ ∂μ :=
        lintegral_lintegral_swap ((hw.comp hm2).mul (hψ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const (ψ g) (f := fun u => w ((ι u)⁻¹ * g)) (hw.comp (hιm.inv.mul_const g))]
        exact mul_comm _ _
    _ = ∑' γ : Γ, ∫⁻ h in 𝓕, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ h in 𝓕, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        (lintegral_tsum fun γ : Γ => (hFm.comp (measurable_const_mul (γ : G))).aemeasurable).symm
    _ = ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ := lintegral_congr fun h => hpt h

end

theorem lintegral_sum_cosets_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hιce μ _ μ₁ _ Γ _ Γ₁ _ 𝓕 𝓕₁ h𝓕 h𝓕₁ hfin hΓ Q _ r hr hQ φ hφ hinv
  haveI : T2Space G₁ := hιce.isEmbedding.t2Space
  obtain ⟨hne, hright, hinvinv⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  haveI := hright
  haveI := hinvinv
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.closed_subgroup_quotient_measure G G₁ ι hιce μ₁
  have hιc : Continuous ι := hιce.continuous
  have hι : Function.Injective ι := hιce.injective
  have hm : Measurable (fun p : G × G₁ => φ (ι p.2 * p.1)) :=
    hφ.comp ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hAm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) := hm.lintegral_prod_right'
  have hAinv : ∀ (v : G₁) (g : G),
      ∫⁻ u in 𝓕₁, φ (ι u * (ι v * g)) ∂μ₁ = ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁ := by
    intro v g
    have h := setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁ (fun u => φ (ι u * g)) (fun γ hγ u => by
      simp only [map_mul, mul_assoc]
      exact hinv γ hγ _) v
    simpa only [map_mul, mul_assoc] using h
  have hA := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1 φ hφ hinv
  have hB := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1
    (fun g => (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) (hAm.const_mul _)
    (fun u _ g => by simp only [hAinv])
  rw [hA, hB]
  refine lintegral_congr fun g => ?_
  congr 1
  simp only [hAinv]
  rw [setLIntegral_const, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hne hfin.ne, one_mul]

end GlobalTheory.CompanionTheory.SW.Averaging
end
