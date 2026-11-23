module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

section

open MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.ConjModulus

theorem map_mul_right_eq_of_fundamentalDomain {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (Λ : Subgroup H) [Countable Λ] (ρ : Measure H)
    [ρ.IsHaarMeasure] (𝓡 : Set H) (h𝓡 : IsFundamentalDomain Λ 𝓡 ρ) (hfin : ρ 𝓡 ≠ ⊤) (x₀ : H) :
    ρ.map (· * x₀) = ρ := by
  haveI : (ρ.map (· * x₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ρ x₀
  have hc := Measure.isMulLeftInvariant_eq_smul (ρ.map (· * x₀)) ρ
  set c := Measure.haarScalarFactor (ρ.map (· * x₀)) ρ
  have h' : IsFundamentalDomain Λ ((· * x₀) ⁻¹' 𝓡) ρ := by
    refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀) (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ρ ((· * x₀) ⁻¹' 𝓡) = ρ 𝓡 := h'.measure_eq h𝓡
  have h0 : ρ 𝓡 ≠ 0 := h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hmap : (ρ.map (· * x₀)) 𝓡 = ρ ((· * x₀) ⁻¹' 𝓡) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x₀) 𝓡
  have h1 : (c : ℝ≥0∞) * ρ 𝓡 = 1 * ρ 𝓡 := by
    calc (c : ℝ≥0∞) * ρ 𝓡 = (c • ρ) 𝓡 := by simp [Measure.smul_apply]
      _ = (ρ.map (· * x₀)) 𝓡 := by rw [hc]
      _ = 1 * ρ 𝓡 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

def conjB {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) (b : B) : B :=
  ⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩

def conjCME {H G : Type} [Group H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ι : H →* G) (B : Subgroup G) (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) :
    B ≃ₜ* B where
  toFun := conjB ι B hB x
  invFun := conjB ι B hB x⁻¹
  left_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  right_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [conjB, mul_assoc]
  continuous_toFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem conjB_mul {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x y : H) :
    conjB ι B hB (x * y) = conjB ι B hB x ∘ conjB ι B hB y := by
  funext b; apply Subtype.ext; simp [conjB, mul_assoc]

end GlobalTheory.ConjModulus

namespace GlobalTheory.ConjModulus

theorem map_conj_eq_self_of_lattice : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ι : H →* G), Continuous ι → ∀ B : Subgroup G, IsClosed (B : Set G) →
    ∀ (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (β : Measure B), β.IsHaarMeasure →
    ∀ (Λ : Subgroup H) [Countable Λ] (ρ : Measure H) (𝓡 : Set H), ρ.IsHaarMeasure → IsFundamentalDomain Λ 𝓡 ρ → ρ 𝓡 ≠ ⊤ →
    (∀ x ∈ Λ, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β) →
    ∀ x : H, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β := by
  intro H _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _ ι hι B hBc hB β hβ Λ _ ρ 𝓡 hρ h𝓡 hfin hΛ
  haveI := hβ
  haveI := hρ
  haveI : LocallyCompactSpace B := hBc.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology (B : Set G)
  haveI : SigmaCompactSpace B := inferInstance
  haveI : SigmaFinite β := inferInstance
  have hΛ' : ∀ x ∈ Λ, β.map (conjB ι B hB x) = β := hΛ
  show ∀ x : H, β.map (conjB ι B hB x) = β
  have hφm : ∀ x, Measurable (conjB ι B hB x) := fun x => (conjCME ι B hB x).continuous.measurable
  have hHaar : ∀ x, (β.map (conjB ι B hB x)).IsHaarMeasure := fun x =>
    (conjCME ι B hB x).isHaarMeasure_map β
  obtain ⟨d, hdβ⟩ : ∃ d : H → ℝ≥0, ∀ x, β.map (conjB ι B hB x) = d x • β := ⟨fun x =>
    Measure.haarScalarFactor (β.map (conjB ι B hB x)) β, fun x => by
      haveI := hHaar x; exact Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : B)
  have hK0 : β K ≠ 0 := (Measure.measure_pos_of_mem_nhds β hK1).ne'
  have hKt : β K ≠ ⊤ := hKc.measure_lt_top.ne
  have hcancel : ∀ a b : ℝ≥0, a • β = b • β → a = b := by
    intro a b h
    have h2 : (a : ℝ≥0∞) * β K = (b : ℝ≥0∞) * β K := by
      have := congrArg (fun m : Measure B => m K) h
      simpa [Measure.smul_apply] using this
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).1 h2
  have hmul : ∀ x y, d (x * y) = d x * d y := by
    intro x y
    apply hcancel
    rw [← hdβ, conjB_mul, ← Measure.map_map (hφm x) (hφm y), hdβ y, Measure.map_smul, hdβ x,
      smul_smul, mul_comm]
    exact (hφm x).aemeasurable
  have hdΛ : ∀ x ∈ Λ, d x = 1 := by
    intro x hx
    apply hcancel
    rw [← hdβ, hΛ' x hx, one_smul]
  have hpos : ∀ x, 0 < d x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := congrArg (fun m : Measure B => m Set.univ) (hdβ x)
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    rw [Measure.map_apply (hφm x) MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne β)).ne' h1

  have hΦ : Continuous (fun p : H × B => conjB ι B hB p.1 p.2) :=
    continuous_induced_rng.2 (((hι.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul (hι.comp continuous_fst).inv)
  have hS : MeasurableSet ((fun p : H × B => conjB ι B hB p.1 p.2) ⁻¹' K) :=
    (hKc.isClosed.preimage hΦ).measurableSet
  have hDm : Measurable fun x => β (conjB ι B hB x ⁻¹' K) := measurable_measure_prodMk_left hS
  have hdK : ∀ x, (d x : ℝ≥0∞) = β (conjB ι B hB x ⁻¹' K) / β K := by
    intro x
    rw [ENNReal.eq_div_iff hK0 hKt, ← Measure.map_apply (hφm x) hKc.isClosed.measurableSet, hdβ x]
    simp [Measure.smul_apply, mul_comm]
  have hdm : Measurable d := by
    apply measurable_coe_nnreal_ennreal_iff.1
    simp_rw [hdK]
    exact hDm.div_const _

  obtain ⟨g, hgm, hgs, hg1⟩ : ∃ g : ℝ≥0 → ℝ≥0∞, Measurable g ∧
      (∀ a b : ℝ≥0, 0 < a → a < b → g a < g b) ∧ ∀ t, g t ≤ 1 := by
    refine ⟨fun t => ENNReal.ofReal ((t : ℝ) / (1 + t)), ?_, ?_, ?_⟩
    · exact (measurable_coe_nnreal_real.div (measurable_const.add measurable_coe_nnreal_real)).ennreal_ofReal
    · intro a b ha hab
      have ha' : (0 : ℝ) < a := ha
      have hab' : (a : ℝ) < b := hab
      have hb' : (0 : ℝ) < b := ha'.trans hab'
      have hpos' : (0 : ℝ) < (b : ℝ) / (1 + b) := div_pos hb' (by linarith)
      simp only
      rw [ENNReal.ofReal_lt_ofReal_iff hpos', div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · intro t
      apply ENNReal.ofReal_le_one.2
      rw [div_le_one (by positivity)]
      linarith

  have hR : ∀ x₀ : H, ρ.map (· * x₀) = ρ := map_mul_right_eq_of_fundamentalDomain Λ ρ 𝓡 h𝓡 hfin
  have hfΛ : ∀ (l : Λ) (z : H), g (d (l • z)) = g (d z) := by
    intro l z
    rw [Subgroup.smul_def, smul_eq_mul, hmul, hdΛ _ l.2, one_mul]
  have hshift : ∀ x₀ : H, ∫⁻ z in 𝓡, g (d z) ∂ρ = ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
    intro x₀
    have hmp : MeasurePreserving (· * x₀) ρ ρ := ⟨measurable_mul_const x₀, hR x₀⟩
    have hemb : MeasurableEmbedding (· * x₀ : H → H) := (MeasurableEquiv.mulRight x₀).measurableEmbedding
    have h' : IsFundamentalDomain Λ ((· * x₀) '' 𝓡) ρ := by
      rw [Set.image_mul_right]
      refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀⁻¹) (e := id)
        Function.bijective_id ?_
      intro l y
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have := (h𝓡.setLIntegral_eq h' (fun z => g (d z)) hfΛ).trans
      (hmp.setLIntegral_comp_emb hemb (fun z => g (d z)) 𝓡).symm
    simpa [hmul] using this
  have hne : ρ.restrict 𝓡 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hfinI : ∀ c : ℝ≥0, ∫⁻ z in 𝓡, g (d z * c) ∂ρ ≠ ⊤ := by
    intro c
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in 𝓡, 1 ∂ρ) ?_ (lintegral_mono fun z => hg1 _)
    rw [setLIntegral_const, one_mul]; exact hfin
  have hd1 : ∀ x, d x = 1 := by
    intro x₀
    by_contra hne1
    have hsh := hshift x₀
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have hlt' : ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ < ∫⁻ z in 𝓡, g (d z) ∂ρ := by
        refine lintegral_strict_mono hne (hgm.comp hdm).aemeasurable (hfinI _)
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (mul_pos (hpos z) (hpos x₀)) (mul_lt_of_lt_one_right (hpos z) hlt)
      exact hlt'.ne hsh.symm
    · have hlt' : ∫⁻ z in 𝓡, g (d z) ∂ρ < ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
        have h1 := hfinI 1
        simp only [mul_one] at h1
        refine lintegral_strict_mono hne ((hgm.comp (hdm.mul_const _))).aemeasurable h1
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (hpos z) (lt_mul_of_one_lt_right (hpos z) hgt)
      exact hlt'.ne hsh
  intro x
  rw [hdβ x, hd1 x, one_smul]

end GlobalTheory.ConjModulus
end

section

open MeasureTheory Topology

namespace GlobalTheory.KernelCovolume

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma c_zero {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) : c 0 = 1 :=
  mul_left_cancel (a := c 0) (by rw [mul_one, ← hca, add_zero])

lemma c_neg {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (r : ℝ) : (c r)⁻¹ = c (-r) :=
  inv_eq_of_mul_eq_one_right (by rw [← hca, add_neg_cancel, c_zero hca])

def cHom (c : ℝ → G) (hca : ∀ x y, c (x + y) = c x * c y) : Multiplicative ℝ →* G where
  toFun x := c (Multiplicative.toAdd x)
  map_one' := c_zero hca
  map_mul' x y := hca _ _

lemma c_int {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (n : ℤ) : c n = c 1 ^ n := by
  have h := map_zpow (cHom c hca) (Multiplicative.ofAdd (1:ℝ)) n
  rw [← ofAdd_zsmul, zsmul_one] at h
  exact h

lemma mem_of_split {H : Subgroup G} {s : G → ℝ} {c : ℝ → G}
    (hsa : ∀ g h, s (g * h) = s g + s h) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0)
    (g : G) : g * c (-s g) ∈ H := by
  rw [hH, hsa, hsc]; ring

def splitHomeo {H : Subgroup G} {s : G → ℝ} {c : ℝ → G} (hs : Continuous s)
    (hsa : ∀ g h, s (g * h) = s g + s h) (hc : Continuous c)
    (hca : ∀ x y, c (x + y) = c x * c y) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0) :
    H × ℝ ≃ₜ G where
  toFun p := (p.1 : G) * c p.2
  invFun g := (⟨g * c (-s g), mem_of_split hsa hsc hH g⟩, s g)
  left_inv p := by
    rcases p with ⟨⟨h, hh⟩, t⟩
    have h0 : s h = 0 := (hH h).1 hh
    have e : s (h * c t) = t := by rw [hsa, hsc, h0, zero_add]
    refine Prod.ext (Subtype.ext ?_) ?_
    · show h * c t * c (-s (h * c t)) = h
      rw [e, mul_assoc, ← hca, add_neg_cancel, c_zero hca, mul_one]
    · exact e
  right_inv g := by
    show g * c (-s g) * c (s g) = g
    rw [mul_assoc, ← hca, neg_add_cancel, c_zero hca, mul_one]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd)
  continuous_invFun := (Continuous.subtype_mk (continuous_id.mul (hc.comp hs.neg)) _).prodMk hs

end GlobalTheory.KernelCovolume

open scoped Pointwise

open GlobalTheory.KernelCovolume in
theorem GlobalTheory.finiteCovolume_kernel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H Γ Λ s c hs hsa hc hca hcc hsc hH hΓ hΛ _hdisc hfin π D hπ hD
  have hcl : IsClosed (H : Set G) := by
    have : (H : Set G) = s ⁻¹' {0} := by ext g; exact hH g
    rw [this]; exact isClosed_singleton.preimage hs
  haveI : LocallyCompactSpace H := hcl.locallyCompactSpace
  haveI : SigmaCompactSpace H := hcl.sigmaCompactSpace
  haveI : SigmaFinite π := inferInstance
  set φ : H × ℝ ≃ₜ G := GlobalTheory.KernelCovolume.splitHomeo hs hsa hc hca hsc hH with hφdef
  have hφ : ∀ p : H × ℝ, φ p = (p.1 : G) * c p.2 := fun p => rfl
  set μ0 : Measure (H × ℝ) := π.prod volume with hμ0
  set ν : Measure G := μ0.map φ with hνdef
  have hνapp : ∀ A, ν A = μ0 (φ ⁻¹' A) := fun A => φ.toMeasurableEquiv.map_apply A
  have hmulφ : ∀ (γ : H) (r : ℝ) (p : H × ℝ), (γ : G) * c r * φ p = φ (γ * p.1, r + p.2) := by
    intro γ r p
    simp only [hφ, Subgroup.coe_mul, hca, mul_assoc]
    rw [← mul_assoc (c r) (p.1 : G), hcc r, mul_assoc]

  haveI : (Subgroup.zpowers (c 1)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute ((c 1) ^ k) g := (Commute.zpow_left (hcc 1 g) k)
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers _ _⟩
  have hdec : ∀ l ∈ Λ, ∃ γ ∈ Γ, ∃ n : ℤ, l = γ * c n := by
    intro l hl
    rw [hΛ] at hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨y, hy, n, by rw [GlobalTheory.KernelCovolume.c_int hca]⟩
  have hmemΛ : ∀ γ ∈ Γ, ∀ n : ℤ, γ * c n ∈ Λ := by
    intro γ hγ n
    rw [hΛ, GlobalTheory.KernelCovolume.c_int hca]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

  have hνHaar : ν.IsHaarMeasure := by
    haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ0 φ
    haveI : ν.IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
    haveI : ν.IsMulLeftInvariant := ⟨fun g => by
      obtain ⟨p0, rfl⟩ := φ.surjective g
      ext A hA
      rw [Measure.map_apply (measurable_const_mul _) hA, hνapp, hνapp]
      have hpre : φ ⁻¹' ((fun x => φ p0 * x) ⁻¹' A) =
          (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) ⁻¹' (φ ⁻¹' A) := by
        ext p
        simp only [Set.mem_preimage, Prod.map]
        rw [show φ p0 = (p0.1 : G) * c p0.2 from rfl, hmulφ]
      have hT : μ0.map (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) = μ0 := by
        rw [hμ0, ← Measure.map_prod_map π volume (measurable_const_mul _) (measurable_const_add _),
          map_mul_left_eq_self, map_add_left_eq_self]
      rw [hpre, ← Measure.map_apply ((measurable_const_mul _).prodMap (measurable_const_add _))
        (φ.measurable hA), hT]⟩
    exact ⟨⟩

  set S : Set (H × ℝ) := D ×ˢ Set.Ico (0:ℝ) 1 with hS
  set D' : Set G := φ.symm ⁻¹' S with hD'
  have hφD' : φ ⁻¹' D' = S := by ext p; simp [hD']
  have hsub : ∀ (l : Λ) (γ : G) (hγ : γ ∈ Γ) (n : ℤ), (l : G) = γ * c n → ∀ p : H × ℝ,
      φ p ∈ l • D' → (⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1 ∈ D ∧ ((-n : ℤ) : ℝ) + p.2 ∈ Set.Ico (0:ℝ) 1 := by
    intro l γ hγ n e p hp
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hp
    have hx : l⁻¹ • φ p = φ ((⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1, ((-n : ℤ) : ℝ) + p.2) := by
      rw [← hmulφ, Subgroup.smul_def, smul_eq_mul]
      congr 1
      simp only [Subgroup.coe_inv, e, mul_inv_rev, GlobalTheory.KernelCovolume.c_neg hca, Int.cast_neg]
      exact hcc _ _
    rw [hx] at hp
    simpa [hD', hS] using hp
  have hFD : IsFundamentalDomain Λ D' ν := by
    refine { nullMeasurableSet := ?_, ae_covers := ?_, aedisjoint := ?_ }
    · exact (hD.nullMeasurableSet.prod measurableSet_Ico.nullMeasurableSet).preimage
        (φ.toMeasurableEquiv.quasiMeasurePreserving_symm μ0)
    · rw [hνdef, show (⇑φ : H × ℝ → G) = ⇑φ.toMeasurableEquiv from rfl,
        φ.toMeasurableEquiv.measurableEmbedding.ae_map_iff]
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp
      obtain ⟨γ, hγ⟩ := hp
      have hγΓ : ((γ : H) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      refine ⟨⟨((γ : H) : G) * c ((-⌊p.2⌋ : ℤ) : ℝ), hmemΛ _ hγΓ _⟩, ?_⟩
      rw [Subgroup.smul_def, smul_eq_mul]
      show _ ∈ φ.symm ⁻¹' S
      rw [Set.mem_preimage, show (φ.toMeasurableEquiv p) = φ p from rfl, hmulφ, φ.symm_apply_apply]
      have hfr : ((-⌊p.2⌋ : ℤ) : ℝ) + p.2 = Int.fract p.2 := by
        rw [Int.cast_neg, Int.fract]; ring
      rw [hfr]
      exact Set.mk_mem_prod hγ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro l1 l2 hne
      obtain ⟨γ1, hγ1, n1, e1⟩ := hdec l1 l1.2
      obtain ⟨γ2, hγ2, n2, e2⟩ := hdec l2 l2.2
      show ν ((l1 • D') ∩ (l2 • D')) = 0
      rw [hνapp]
      by_cases hn : n1 = n2
      · subst hn
        have hγne : γ1 ≠ γ2 := by
          rintro rfl; exact hne (Subtype.ext (e1.trans e2.symm))
        let g1 : Γ.subgroupOf H := ⟨⟨γ1, hΓ hγ1⟩, Subgroup.mem_subgroupOf.2 hγ1⟩
        let g2 : Γ.subgroupOf H := ⟨⟨γ2, hΓ hγ2⟩, Subgroup.mem_subgroupOf.2 hγ2⟩
        have hg : g1 ≠ g2 := fun h => hγne (congrArg (fun x : Γ.subgroupOf H => ((x : H) : G)) h)
        have h0 : π (g1 • D ∩ g2 • D) = 0 := hD.aedisjoint hg
        refine measure_mono_null (t := (g1 • D ∩ g2 • D) ×ˢ Set.univ) ?_ ?_
        · rintro p ⟨hp1, hp2⟩
          refine Set.mk_mem_prod ⟨?_, ?_⟩ (Set.mem_univ _)
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l1 γ1 hγ1 n1 e1 p hp1).1
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l2 γ2 hγ2 n1 e2 p hp2).1
        · rw [hμ0, Measure.prod_prod, h0, zero_mul]
      · refine measure_mono_null (t := ∅) ?_ measure_empty
        rintro p ⟨hp1, hp2⟩
        have a1 := (hsub l1 γ1 hγ1 n1 e1 p hp1).2
        have a2 := (hsub l2 γ2 hγ2 n2 e2 p hp2).2
        simp only [Set.mem_Ico, Int.cast_neg] at a1 a2
        have b1 : (n1 : ℝ) < n2 + 1 := by linarith
        have b2 : (n2 : ℝ) < n1 + 1 := by linarith
        have c1 : n1 < n2 + 1 := by exact_mod_cast b1
        have c2 : n2 < n1 + 1 := by exact_mod_cast b2
        exact absurd (by omega : n1 = n2) hn
  have hfinν := hfin ν D' hνHaar hFD
  have hνD' : ν D' = π D := by
    rw [hνapp, hφD', hS, hμ0, Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
      mul_one]
  rwa [hνD'] at hfinν
end

section

open scoped NNReal ENNReal
open MeasureTheory

theorem GlobalTheory.unimodular_of_isFundamentalDomain_finite : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by
  intro S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin
  haveI : SMulInvariantMeasure Γ S μS :=
    ⟨fun c s _ => by
      show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s
      exact measure_preimage_mul μS (c : S) s⟩
  have hpos : μS 𝓢 ≠ 0 := hF.measure_ne_zero (NeZero.ne μS)
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μS g

  have hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS := by
    refine hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact quasiMeasurePreserving_mul_right μS g
    · intro γ x
      show (γ : S) * x * g = (γ : S) * (x * g)
      exact mul_assoc _ _ _
  have heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢 := hF'.measure_eq hF
  have h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢 := by
    rw [show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]
    exact heq
  rw [hmap] at h2
  rw [Measure.smul_apply] at h2
  have hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    have h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢 := by
      rw [one_mul]; simpa [ENNReal.smul_def] using h2
    exact (ENNReal.mul_left_inj hpos hfin).mp h3
  rw [show (fun x : S => x * g) = fun x => x * g from rfl] at hmap
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]
end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_sublevel_tail_le (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  have hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1} := fun T =>
    measurableSet_le hx measurable_const
  haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne
  have hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1}) := by
    intro a b hab y hy
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ.withDensity g)
    (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - x y)
    exact ⟨n, by linarith⟩
  rw [hem, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds hε)).exists
  refine ⟨n, fun T hT => ?_⟩
  rw [← withDensity_apply _ (hms T)]
  refine le_trans (measure_mono ?_) hn
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith

end GlobalTheory
end
