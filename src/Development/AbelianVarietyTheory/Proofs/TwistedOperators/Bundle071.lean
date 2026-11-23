module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuLR

open Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem cofinite_le_principal_compl :
    cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite


open Classical in
def jSP : SPart F S × OPart F S →
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  fun p => ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v), by
    rw [eventually_principal]
    intro v hv
    have hv' : v ∉ S := hv
    simp only [dif_neg hv']
    exact (p.2 ⟨v, hv'⟩).2⟩

def jSPinv : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] →
    SPart F S × OPart F S :=
  fun x => (fun v => x v.1, fun v => ⟨x v.1, x.2 v.2⟩)

theorem continuous_jSP : Continuous (jSP F S) := by
  rw [RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff]
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => p.1 ⟨v, h⟩ := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)

theorem continuous_jSPinv : Continuous (jSPinv F S) := by
  have hc : Continuous (fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] =>
      (x : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous
  refine Continuous.prodMk (continuous_pi fun v => (continuous_apply v.1).comp hc)
    (continuous_pi fun v => ((continuous_apply v.1).comp hc).subtype_mk _)

def jSPHomeo : SPart F S × OPart F S ≃ₜ
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] where
  toFun := jSP F S
  invFun := jSPinv F S
  left_inv p := by
    ext v
    · simp [jSP, jSPinv, v.2]
    · simp [jSP, jSPinv, v.2]
  right_inv x := by
    ext v
    by_cases h : v ∈ S <;> simp [jSP, jSPinv, h]
  continuous_toFun := continuous_jSP F S
  continuous_invFun := continuous_jSPinv F S

theorem jS_eq_comp : (jS F S : SPart F S × OPart F S → Af F) =
    RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl F S) ∘ jSP F S := by
  funext p; rfl

theorem isOpenEmbedding_jS : IsOpenEmbedding (jS F S) := by
  rw [jS_eq_comp]
  exact (RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)) (cofinite_le_principal_compl F S)).comp
    (jSPHomeo F S).isOpenEmbedding

end GlobalTheory.ModuLR
end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem addEquivAddHaarChar_prodCE (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) :
    addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  set μ₁ : Measure G₁ := Measure.addHaar
  set μ₂ : Measure G₂ := Measure.addHaar
  set μ : Measure (G₁ × G₂) := μ₁.prod μ₂
  have hμ : μ.IsAddHaarMeasure := by infer_instance
  have hreg : μ.Regular := by infer_instance
  set φ := prodCE e₁ e₂
  have h1 := addEquivAddHaarChar_smul_map μ₁ e₁
  have h2 := addEquivAddHaarChar_smul_map μ₂ e₂
  have h := addEquivAddHaarChar_smul_map μ φ
  have hm1 : (μ₁.map e₁).IsAddHaarMeasure := e₁.isAddHaarMeasure_map μ₁
  have hm2 : (μ₂.map e₂).IsAddHaarMeasure := e₂.isAddHaarMeasure_map μ₂
  have hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂) := by
    have := Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable
    exact this.symm
  have hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ := by
    rw [hmap]
    conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]
    rw [mul_smul]
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hν : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G₁ × G₂)
  have hpos : (μ.map φ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory.ModuLR
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual

namespace GlobalTheory.SmGL.IndCoinv

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_bump (β : σ.IntertwiningMap ρ) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) (v : fixed ρ (J.subgroupOf P)) (hv : β w = v) :
    smIndMap β (bump σ hJ w) = bump ρ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  show β ((bump σ hJ w).1.1 g) = _
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero _ _ _ h, map_zero]
  · rw [bump_mul _ _ _ _ hj, bump_mul _ _ _ _ hj, β.isIntertwining, hv]

theorem mem_of_bump {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (Z : Submodule ℂ (smoothPart (ind P σ))) (hZ : ∀ g, ∀ f ∈ Z, smInd P σ g f ∈ Z)
    (h : ∀ (J : Subgroup G) (hJ : IsOpen (J : Set G)), J ≤ K → ∀ w, bump σ hJ w ∈ Z)
    (f : smoothPart (ind P σ)) : f ∈ Z := by
  obtain ⟨J, hJ, hJU, hle, hn⟩ := hb _ (IsOpen.mem_nhds (isSmooth_smoothRep _ f) (by
    rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
  refine Submodule.span_le.2 ?_ (mem_span_bump σ hJ hK hle hn hPK f fun j hj => hJU hj)
  rintro _ ⟨z, -, w, rfl⟩
  exact hZ _ _ (h J hJ hle w)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem map_mem_fixed {σ : Representation ℂ G X} {ρ : Representation ℂ G U} (β : σ.IntertwiningMap ρ)
    {H : Subgroup G} {w : X} (hw : w ∈ fixed σ H) : β w ∈ fixed ρ H :=
  mem_fixed_iff.2 fun h hh => by rw [← β.isIntertwining, mem_fixed_iff.1 hw h hh]

theorem mem_of_fixed [T2Space G] {σ : Representation ℂ G X} (hσ : IsSmooth σ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {Γ : Type} (T : Γ → σ.IntertwiningMap σ) (M : Submodule ℂ (fixed σ H))
    (hM : ∀ γ (z : fixed σ H), (⟨T γ z, map_mem_fixed (T γ) z.2⟩ : fixed σ H) - z ∈ M) (w : fixed σ H)
    (hw : w.1 ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) : w ∈ M := by
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend l
  obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form G X σ hσ _ hH l₀
  have h3 : ∀ v : fixed σ H, l₁ v = l v := fun v =>
    (h2 _ (mem_fixed_iff.1 v.2)).trans (LinearMap.congr_fun hl₀ v)
  have h4 : ∀ γ, l₁ ∘ₗ (T γ).toLinearMap = l₁ := fun γ =>
    dual_ext hσ hH (fun h hh v => by
      show l₁ (T γ _) = l₁ (T γ _)
      rw [(T γ).isIntertwining, h1 h hh]) h1 fun v hv => by
      have h5 : l (_ - _) ∈ M.map l := Submodule.mem_map_of_mem (hM γ ⟨v, hv⟩)
      rw [hl0, Submodule.mem_bot, map_sub, ← h3, ← h3, sub_eq_zero] at h5
      exact h5
  apply hl
  rw [← h3]
  refine (Submodule.span_le (p := LinearMap.ker l₁)).2 ?_ hw
  rintro _ ⟨γ, z, rfl⟩
  have h5 : l₁ (T γ z) = l₁ z := LinearMap.congr_fun (h4 γ) z
  simp [h5]

theorem smInd_coinvariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (P K : Subgroup G), IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) → (∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧ ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (U : Type) [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ P X) (ρ : Representation ℂ P U), IsSmooth σ → ∀ (α : σ.IntertwiningMap ρ) (Γ : Type) (T : Γ → σ.IntertwiningMap σ), Function.Surjective α → (∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) → Function.Surjective (smIndMap α) ∧ ∀ f, smIndMap α f = 0 → f ∈ Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} := by
  intro G _ _ _ _ P K hP hK hPK hb X _ _ U _ _ σ ρ hσ α Γ T hα hker
  have hc : ∀ J : Subgroup G, IsOpen (J : Set G) → J ≤ K → IsCompact (J.subgroupOf P : Set P) :=
    fun J hJ hle => hP.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle)
  constructor
  · intro f
    refine mem_of_bump hK hPK hb (LinearMap.range (smIndMap α).toLinearMap) ?_ ?_ f
    · rintro g _ ⟨φ, rfl⟩
      exact ⟨smInd P σ g φ, rfl⟩
    · intro J hJ hle w
      obtain ⟨x, hx⟩ := hα w
      obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ (hc J hJ hle) α.toLinearMap x fun h hh => by
        show α _ = α _
        rw [α.isIntertwining, hx, mem_fixed_iff.1 w.2 h hh]
      exact ⟨bump σ hJ ⟨v, hv⟩, smIndMap_bump α hJ _ _ (e.trans hx)⟩
  · intro f hf
    set Z := Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} with hZ
    let N : Submodule ℂ X := LinearMap.ker α.toLinearMap
    have hN : ∀ g, ∀ v ∈ N, σ g v ∈ N := fun g v hv => by
      have hv' : α v = 0 := hv
      show α _ = 0
      rw [α.isIntertwining, hv', map_zero]
    let τ := sub σ N hN
    let j : τ.IntertwiningMap σ := { toLinearMap := N.subtype, isIntertwining' := fun _ => rfl }
    let f' : smoothPart (ind P τ) :=
      ⟨⟨fun g => ⟨f.1.1 g, congrArg (fun φ : smoothPart (ind P ρ) => φ.1.1 g) hf⟩, fun h g => Subtype.ext (f.1.2 h g)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
          have hg' : ind P σ g f.1 = f.1 := hg
          exact Subtype.ext (funext fun x => Subtype.ext (congrFun (congrArg Subtype.val hg') x)))⟩
    have hst : ∀ g, Z ≤ Z.comap (smInd P σ g) := fun g => Submodule.span_le.2 (by
      rintro _ ⟨γ, z, rfl⟩
      exact Submodule.subset_span ⟨γ, smInd P σ g z, rfl⟩)
    refine mem_of_bump hK hPK hb (Z.comap (smIndMap j).toLinearMap) (fun g φ hφ => hst g hφ) ?_ f'
    intro J hJ hle w
    have hw := map_mem_fixed j w.2
    show smIndMap j _ ∈ Z
    rw [smIndMap_bump j hJ w ⟨_, hw⟩ rfl]
    refine mem_of_fixed hσ (hc J hJ hle) T (Z.comap (bump σ hJ)) (fun γ z => ?_) _ (hker _ w.1.2)
    rw [Submodule.mem_comap, map_sub, ← smIndMap_bump (T γ) hJ z _ rfl]
    exact Submodule.subset_span ⟨γ, _, rfl⟩

end GlobalTheory.SmGL.IndCoinv
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex

namespace GlobalTheory.QuadraticValuationIndexTwo

theorem exists_mul_conj_iff {B E : Type} [Field B] [CharZero B] [Field E] [Algebra B E] {d : B}
    {θ : E} {σ : E ≃ₐ[B] E} (h : IsKum 2 (-1 : B) d θ σ) (x : B) :
    (∃ y : E, y * σ y = algebraMap B E x) ↔ Nm d x := by
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ h
  have hinv : ∀ z, σ (σ z) = z := fun z => kb.2.2.1 z
  have hfix := kb.2.2.2.1
  have hpow : θ ^ 2 = algebraMap B E d := h.pow
  have hconj : σ θ = -θ := by rw [h.conj, map_neg, map_one, neg_one_mul]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap B E).injective
  have hθ : θ ≠ 0 := by
    intro h0
    apply h.nonpow 0
    apply (algebraMap B E).injective
    rw [← hpow, h0]
    simp
  constructor
  · rintro ⟨y, hy⟩

    obtain ⟨a, ha⟩ := hfix ((y + σ y) / 2) (by
      rw [map_div₀, map_add (f := _), hinv, map_ofNat, add_comm])
    obtain ⟨b, hb⟩ := hfix ((y - σ y) / (2 * θ)) (by
      rw [map_div₀, map_sub, hinv, map_mul, hconj, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub])
    have hy' : y = algebraMap B E a + algebraMap B E b * θ := by
      rw [← ha, ← hb]
      field_simp
      ring
    have hσy : σ y = algebraMap B E a - algebraMap B E b * θ := by
      rw [hy', map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
      ring
    refine ⟨a, b, (algebraMap B E).injective ?_⟩
    rw [← hy, hσy, hy']
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring
  · rintro ⟨a, b, rfl⟩
    refine ⟨algebraMap B E a + algebraMap B E b * θ, ?_⟩
    rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring

theorem exists_valuation_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℕ, v.valuation F ((2 : ℕ) : F) = WithZero.exp (-(e : ℤ)) := by
  have h0 : v.valuation F ((2 : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr (by norm_num)
  have hle : v.valuation F ((2 : ℕ) : F) ≤ 1 := by
    have := GlobalTheory.QuadSymbol.NormIndex.map_two_le (v.valuation F)
    simpa using this
  have hlog : WithZero.log (v.valuation F ((2 : ℕ) : F)) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp h0]
    simpa using hle
  refine ⟨(-WithZero.log (v.valuation F ((2 : ℕ) : F))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]

theorem exists_subgroup_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    ∃ N : Subgroup Bˣ, N.index = 2 ∧ ∀ x : Bˣ, x ∈ N ↔ Nm d (x : B) := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hnp : ∀ r : B, r ^ 2 ≠ d := fun r hr => hd ⟨r, by rw [← hr, sq]⟩

  obtain ⟨E, _, _, θ, σ, hK⟩ :=
    GlobalTheory.CNorm.exists_isKum 2 B (-1) d Nat.prime_two (IsPrimitiveRoot.neg_one 0 (by norm_num)) hnp
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ hK
  have : FiniteDimensional B E := kb.1
  let : Algebra K E := ((algebraMap B E).comp (algebraMap K B)).toAlgebra
  have : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional K E := Module.Finite.trans B E
  obtain ⟨e, he⟩ := exists_valuation_two F v
  have hB := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e B (by norm_num) he
  have hE := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e E (by norm_num) he
  let σ' : Eˣ →* Eˣ := Units.map (σ : E →+* E).toMonoidHom
  let j : Bˣ →* Eˣ := Units.map (algebraMap B E).toMonoidHom
  have hσ' : ∀ y : Eˣ, ((σ' y : Eˣ) : E) = σ (y : E) := fun y => rfl
  have hj' : ∀ x : Bˣ, ((j x : Eˣ) : E) = algebraMap B E (x : B) := fun x => rfl
  have hj : Function.Injective j := fun a b hab =>
    Units.ext ((algebraMap B E).injective (by rw [← hj', ← hj', hab]))
  have hσ'2 : ∀ a, σ'^[2] a = a := fun a => Units.ext (kb.2.2.1 (a : E))

  have hfix : GlobalTheory.CNorm.fix σ' = j.range := by
    ext x
    rw [GlobalTheory.CNorm.mem_fix, MonoidHom.mem_range]
    constructor
    · intro hx
      have hx' : σ (x : E) = x := by rw [← hσ', hx]
      obtain ⟨a, ha⟩ := kb.2.2.2.1 (x : E) hx'
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [ha, map_zero])
      exact ⟨Units.mk0 a ha0, Units.ext (by rw [hj', Units.val_mk0, ha])⟩
    · rintro ⟨b, rfl⟩
      exact Units.ext (by rw [hσ', hj', AlgEquiv.commutes])
  have hnrm : ∀ y : Eˣ, ((GlobalTheory.CNorm.nrm σ' 2 y : Eˣ) : E) = (y : E) * σ y := by
    intro y
    rw [GlobalTheory.CNorm.nrm_apply, Finset.prod_range_succ, Finset.prod_range_one]
    rfl

  have hker : (GlobalTheory.CNorm.nrm σ' 2).ker ≤ (GlobalTheory.CNorm.dif σ').range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ∏ i ∈ Finset.range 2, σ^[i] (y : E) = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_one]
      have := congrArg Units.val hy
      rw [hnrm] at this
      exact this
    obtain ⟨z, hz0, hz⟩ := kb.2.2.2.2.1 (y : E) h1
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [GlobalTheory.CNorm.dif_apply, Units.val_div_eq_div_val, hσ', Units.val_mk0, hz]
  have hR2 : (GlobalTheory.CNorm.dif σ').range.relIndex (GlobalTheory.CNorm.nrm σ' 2).ker = 1 :=
    Subgroup.relIndex_eq_one.mpr hker
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hIE : GlobalTheory.CNorm.pIdx 2 (⊤ : Subgroup Eˣ) ≠ 0 := by
    rw [hE.2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1

  obtain ⟨-, -, -, -, heq⟩ := GlobalTheory.CNorm.herbrand_prime_order 2 Eˣ σ' Nat.prime_two hσ'2 hIE hE.1
  rw [hfix, hR2, GlobalTheory.CNorm.pIdx_range_of_injective 2 j hj, GlobalTheory.CNorm.pTor_range_of_injective 2 j hj,
    hE.2, hB.2] at heq
  have hrank : Module.finrank K E = Module.finrank K B * 2 := by
    rw [← Module.finrank_mul_finrank K B E, kb.2.1]
  rw [hrank, pow_mul] at heq
  set Q := (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank K B
  set TE := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Eˣ)
  set TB := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Bˣ)
  set R := (GlobalTheory.CNorm.nrm σ' 2).range.relIndex j.range
  have hX : Q ^ 2 * TE * TB ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1)
      (pow_ne_zero _ hB.1)
  have hR : R = 2 := by
    have h4 : (R * 2) * (Q ^ 2 * TE * TB ^ 2) = 4 * (Q ^ 2 * TE * TB ^ 2) := by
      have e21 : (2 : ℕ) - 1 = 1 := rfl
      rw [e21, pow_one, one_pow, one_mul] at heq
      calc (R * 2) * (Q ^ 2 * TE * TB ^ 2) = R * (2 * Q ^ 2 * TE) * TB ^ 2 := by ring
        _ = TE * (2 * Q * TB) ^ 2 := heq
        _ = 4 * (Q ^ 2 * TE * TB ^ 2) := by ring
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) h4
    omega
  refine ⟨(GlobalTheory.CNorm.nrm σ' 2).range.comap j, ?_, ?_⟩
  · rw [Subgroup.index_comap]
    exact hR
  · intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range, ← exists_mul_conj_iff hK (x : B)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(y : E), ?_⟩
      rw [← hnrm, hy, hj']
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hy
        exact x.ne_zero ((algebraMap B E).injective (by rw [← hy, map_zero]))
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [hnrm, hj', Units.val_mk0]
      exact hy

theorem norm_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
      ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  obtain ⟨N, hN, hmem⟩ := exists_subgroup_index_two F v B d hd
  refine ⟨?_, ?_⟩
  ·
    have hne : N ≠ ⊤ := by
      rintro rfl
      rw [Subgroup.index_top] at hN
      exact absurd hN (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : Bˣ, c ∉ N := by
      by_contra hall
      apply hne
      rw [eq_top_iff]
      intro c _
      by_contra hc
      exact hall ⟨c, hc⟩
    exact ⟨c, c.ne_zero, fun h => hc ((hmem c).mpr h)⟩
  · intro x y hx hy hnx hny
    have hx' : Units.mk0 x hx ∉ N := fun h => hnx ((hmem _).mp h)
    have hy' : Units.mk0 y hy ∉ N := fun h => hny ((hmem _).mp h)
    have : Units.mk0 x hx * Units.mk0 y hy ∈ N :=
      (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hx' hy')
    exact (hmem _).mp this

end GlobalTheory.QuadraticValuationIndexTwo
end
