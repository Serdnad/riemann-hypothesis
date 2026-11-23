module

public import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.Bundle006
public import GroundTheory.AutomorphicForms.Bundle010
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import GroundTheory.AutomorphicForms.DixmierMalliavinHaar
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarCoord
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.Bundle007
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import GroundTheory.GlobalFields.Bundle001
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LocalField.Basic
public import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]


end Transport

section Split

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

section OfGram

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermitianForm.ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) : HermitianForm F A (ι → A) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F A) (RingHom.id A)
    (fun x y => ∑ i, ∑ j, conj F A (x i) * H i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  isSymm := ⟨fun x y => by

    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : conj F A (H j i) = H i j := congrFun (congrFun hH i) j
    rw [this]
    ring⟩
  nonsingular := by
    refine bijective_of_injective_sesq _ ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hv : Matrix.vecMul (fun i => conj F A (x i)) H = 0 := by
      funext j
      have := LinearMap.congr_fun hx (Pi.single j 1)
      rw [LinearMap.mk₂'ₛₗ_apply] at this
      simpa [vecMul, dotProduct, Pi.single_apply] using this
    have hinj := (Matrix.vecMul_injective_iff_isUnit (A := H)).2
      ((Matrix.isUnit_iff_isUnit_det H).2 hu)
    have h0 := hinj (hv.trans (Matrix.zero_vecMul H).symm)
    funext i
    have := congrFun h0 i
    rw [← conj_conj (F := F) (x i), this]
    simp

theorem HermitianForm.ofGram_apply (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (x y : ι → A) :
    (HermitianForm.ofGram H hH hu).toSesq x y = ∑ i, ∑ j, conj F A (x i) * H i j * y j :=
  rfl

theorem gram_ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) :
    gram (HermitianForm.ofGram H hH hu).toSesq (Pi.basisFun A ι) = H := by
  ext i j
  rw [gram_apply, HermitianForm.ofGram_apply]
  simp [Pi.single_apply]

end OfGram

section LocalField

variable {F A : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A] [Algebra.IsSeparable F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end LocalField

section Diagonal

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]

end Diagonal

end GroundTheory.Automorphic
end
end

section

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

theorem exists_smooth_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2) := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hsmooth : (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by
    intro g
    rw [h.contMDiffAt_iff_expG]
    have hcont : Continuous (fun Y : 𝔤 => g * h.expG Y) :=
      continuous_const.mul h.continuous_expG
    have hg0 : g * h.expG 0 = g := by rw [h.expG_zero, mul_one]
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      have hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r := hεr hz₀
      obtain ⟨hgW, hcg⟩ := hPW z₀ hz₀r
      have hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0]
          fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ) := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hW.mem_nhds hgW)
        filter_upwards [this] with Y hY
        simp [κ, indicator_of_mem hY]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hc0 := hc (P z₀) hgW
      have hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0 := by
        rw [hg0, hcg]; exact (hρpos z₀ hz₀r).ne'
      exact (hK.contDiffAt.comp _ hc0).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))
    · have hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hCc.isClosed.isOpen_compl.mem_nhds hg)
        filter_upwards [this] with Y hY
        exact hκC _ hY
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hκc : Continuous κ := by
    let := h.chartedSpace
    exact hsmooth.continuous
  refine ⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

section

open MeasureTheory Topology Filter Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G)

def automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) : ℂ :=
  ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2)

theorem automorphicKernel_smul_left (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (δ • a, b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
  congr 1
  group

theorem automorphicKernel_smul_right (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (a, δ • b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulRight δ⁻¹)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  congr 1
  group

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ]

theorem locallyFinite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    LocallyFinite fun γ : Γ => support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  intro p
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds p.1
  obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds p.2
  refine ⟨A ×ˢ B, prod_mem_nhds hA hB, ?_⟩
  have hAS : IsCompact (A * tsupport f) := hAc.mul f.hasCompactSupport
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hBc hAS).subset ?_
  rintro γ ⟨⟨a, b⟩, hq, hab⟩
  simp only [mem_prod] at hab
  refine ⟨γ • b, mem_image_of_mem _ hab.2, ?_⟩
  refine ⟨a, hab.1, a⁻¹ * γ * b, subset_tsupport _ hq, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul]
  group

theorem continuous_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (automorphicKernel Γ f) :=
  continuous_finsum (fun γ => f.continuous.comp (by fun_prop))
    (locallyFinite_support_automorphicKernel Γ f)

theorem finite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) :
    (support fun γ : Γ => f (p.1⁻¹ * γ * p.2)).Finite := by
  exact (locallyFinite_support_automorphicKernel Γ f).point_finite p

def quotientKernel (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : ℂ :=
  Quotient.lift₂ (fun a b => automorphicKernel Γ f (a, b)) (fun a₁ b₁ a₂ b₂ ha hb => by
    obtain ⟨δ, rfl⟩ := ha
    obtain ⟨ε, rfl⟩ := hb
    rw [automorphicKernel_smul_left, automorphicKernel_smul_right]) p.1 p.2

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
@[simp] theorem quotientKernel_mk (f : CompactlySupportedContinuousMap G ℂ) (a b : G) :
    quotientKernel Γ f (mk Γ a, mk Γ b) = ∑ᶠ γ : Γ, f (a⁻¹ * γ * b) :=
  rfl

theorem continuous_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (quotientKernel Γ f) := by
  have hq : IsQuotientMap (Prod.map (mk Γ) (mk Γ)) :=
    ((isOpenQuotientMap_mk Γ).prodMap (isOpenQuotientMap_mk Γ)).isQuotientMap
  refine hq.continuous_iff.2 ?_
  exact continuous_automorphicKernel Γ f

section Operator

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]

def rightRegularRep : UnitaryRep G (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  UnitaryRep.ofLinearIsometryEquiv (rightRegular Γ μ) (continuous_rightRegular_apply Γ μ)

theorem rightRegularRep_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ = rightTranslate Γ μ g φ :=
  rfl

theorem coeFn_rightRegularRep (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x => φ (rightMul Γ g x) :=
  coeFn_rightTranslate Γ μ g φ


variable [CompactSpace (RightCosetSpace Γ)]


omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem coeFn_compactSupportToL1 (f : CompactlySupportedContinuousMap G ℂ) :
    (UnitaryRep.ccToL1 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _



end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
end

section

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl

end UnitaryRep

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end RightCosetSpace

end

end GroundTheory.Automorphic
end

section

open NumberField IsDedekindDomain Topology Filter TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

variable (K : Type*) [Field K] [NumberField K]

instance secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  let O : Set (v.adicCompletion K) := v.adicCompletionIntegers K
  let U : K → Set (v.adicCompletion K) := fun a => {x | x - algebraMap K _ a ∈ O}
  have hO : IsOpen O := GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hU : ∀ a, IsOpen (U a) := fun a => hO.preimage (continuous_id.sub continuous_const)
  have hSC : ∀ a, SecondCountableTopology (U a) := fun a => by
    have : SecondCountableTopology O :=
      inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
    let φ : U a → O := fun x => ⟨x.1 - algebraMap K _ a, x.2⟩
    have he : IsEmbedding ((Subtype.val : O → v.adicCompletion K) ∘ φ) :=
      (Homeomorph.subRight (algebraMap K (v.adicCompletion K) a)).isEmbedding.comp
        IsEmbedding.subtypeVal
    exact ((IsEmbedding.subtypeVal.of_comp_iff).1 he).secondCountableTopology
  refine secondCountableTopology_of_countable_cover hU ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hV : IsOpen {y : v.adicCompletion K | x - y ∈ O} :=
    hO.preimage (continuous_const.sub continuous_id)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hV
    ⟨x, by simp [O, (v.adicCompletionIntegers K).zero_mem]⟩
  exact ⟨a, ha⟩

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  let R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K
  let A := fun v : HeightOneSpectrum (𝓞 K) =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hAo : ∀ v, IsOpen (A v) := fun v => GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) := fun S => by
    rw [le_principal_iff]
    exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (Πʳ v, [R v, A v]) :=
    fun S => Set.range (RestrictedProduct.inclusion R A (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS S)).isOpen_range
  have hSC : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 :
        SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    have hfin : {v | x.1 v ∉ A v}.Finite := x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    show ∀ᶠ v in 𝓟 ((hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))ᶜ), x.1 v ∈ A v
    rw [eventually_principal]
    intro v hv
    by_contra h
    exact hv (by simpa using h)
  show SecondCountableTopology (Πʳ v, [R v, A v])
  exact @secondCountableTopology_of_countable_cover _ _ _ _ _ hSC hUo hcov

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Automorphic
end
