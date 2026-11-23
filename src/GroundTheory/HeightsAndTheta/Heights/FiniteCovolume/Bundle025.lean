module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle015
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

universe u

theorem exists_covering_of_relIndex_ne_zero {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by
  classical
  have : (A.subgroupOf B).FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def
  have hbad : μ bad = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)
  refine ⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹'
    toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage
      (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [measure_toMeasurable, hbad, add_zero]
    refine lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_
    simp only [measure_preimage_mul, measure_toMeasurable]
    exact ENNReal.sum_lt_top.2 fun _ _ => hfin
  · intro l
    by_cases hl : l ∈ bad
    · exact ⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩
    · rw [hbad_def, Set.mem_ofPred_eq, not_not] at hl
      obtain ⟨⟨γ, hγ⟩, hγl⟩ := hl
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hγ
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
      set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)
      have hcA : (((c : B) : K)) ∈ A := c.2
      refine ⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      apply subset_toMeasurable
      have e : ((Quotient.out k : B) : K) = b * ((c : B) : K) := by
        rw [hc]; rfl
      simp only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      simpa [Subgroup.smul_def] using hγl

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerCovolumeFinite.proof [FiniteDimensional E W] (h : HermitianForm F E W)
    (v : Basis ι E W) (h₁ : CovolumeFiniteBelow.{u} F E (finrank E W))
    (h₂ : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (h₃ : StabilizerLevi.Statement h v) (h₄ : UnipotentModulus.Statement h v)
    (h₅ : UnipotentCocompact.Statement h v) (h₆ : CongruenceLift.Statement h) :
    StabilizerCovolumeFinite.Statement h v := by
  classical
  intro D La x₀ hLa hx₀ hne hiso ν hν

  obtain ⟨w₀, hxw, hww⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨h', hh'⟩ := ComplementForm.proof h x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  have hlt : finrank E (hypComplement h x₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : w₀ ∈ hypComplement h x₀ w₀ := htop ▸ Submodule.mem_top
    rw [mem_hypComplement, hxw] at hmem
    exact one_ne_zero hmem.1

  obtain ⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩ := h₃ x₀ w₀ hp h' hh' _ v'

  obtain ⟨D', La', G'', hLa', hG'', hidx, hlift⟩ := h₆ D La x₀ w₀ hLa hx₀ hp h' hh'
  let μL : Measure (archUnitary h' v') := Measure.haar
  obtain ⟨FD', hFD', hFD'fin⟩ :=
    h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'
  obtain ⟨T, hTm, hTfin, hT⟩ := exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G''
    (latticeStab h' La') hidx FD' hFD' hFD'fin
  set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ
  have hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T := by
    intro l
    obtain ⟨m, hm, hml⟩ := hT l
    obtain ⟨γ₀, hγx, hγw, hγm⟩ := ComplementExtension.proof h x₀ w₀ hp h' hh' m
    have hγ₀ : γ₀ ∈ latticeStab h La := hlift m hm γ₀ hγx hγw hγm
    refine ⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩
    rw [hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]
    exact ⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩

  obtain ⟨C, hC, hcovN⟩ := h₅ D La x₀ hLa hx₀ hne hiso
  let j : unipRadical h v x₀ →* vecFixGroup h v x₀ :=
    Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _)
  have hj : IsClosedEmbedding j := by
    refine ⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩
    have : Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v)) := by
      ext g
      exact ⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_unipRadical h v x₀).preimage continuous_subtype_val
  have hjr : ∀ g, q g = 1 ↔ g ∈ j.range := fun g => (hker g).trans
    ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  let μN : Measure (unipRadical h v x₀) := Measure.haar
  have hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v) :=
    (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding
  have hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j := by
    intro l
    have key := h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩
    have hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹ :=
      (continuous_const.mul hjc).mul continuous_const
    rw [← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j),
      Measure.map_map hemb.measurable hf.measurable,
      Measure.map_map hemb.measurable hjc.measurable]
    have e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) =
        fun n : unipRadical h v x₀ =>
          ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) *
            ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹ := by
      funext n
      simp [j]
    have e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v) := by
      funext n
      rfl
    rw [e1, e2, key]
  have hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C := fun n => by
    obtain ⟨δ, hδ, hδn⟩ := hcovN n
    exact ⟨δ, hδ, hδn⟩

  obtain ⟨S, -, hSfin, hScov⟩ :=
    h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν

  have hdG : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ :
        vecStabGroup h v La x₀))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc

  have hle : ν FD ≤ ν S := by
    rw [hFD.measure_eq_tsum S]
    refine (measure_mono fun x hx => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, hγx⟩ := hScov x
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγx
  have hν0 : ν ≠ 0 := fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])
  exact ⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem real_smul_vec (c : ℝ) (z : ι → ℂ) : c • z = (c : ℂ) • z := by
  ext i
  simp [Complex.real_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem map_conj_transpose (M : Matrix ι ι ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := rfl

theorem hyperbolic_at_place (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨(GramAtData.proof h v w).1, (GramAtData.proof h v w).2, ?_, ?_, ?_⟩
  · rw [hForm, ← HermAtPlace.proof h v w, h1, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h2, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h3, map_one]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem archUnitary_at_place {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (w : InfinitePlace E) :
    (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w := by
  rw [← map_conj_transpose]
  exact mem_archUnitary.1 g.2 w

def heisY (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Submodule ℝ (InfinitePlace E → ι → ℂ) where
  carrier := {y | ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0}
  add_mem' {y z} hy hz w := by
    simp only [Pi.add_apply, hForm_add_right, (hy w).1, (hz w).1, (hy w).2, (hz w).2, add_zero,
      and_self]
  zero_mem' w := ⟨hForm_zero_right _ _, hForm_zero_right _ _⟩
  smul_mem' c y hy w := by
    simp only [Pi.smul_apply, real_smul_vec, hForm_smul_right, (hy w).1, (hy w).2, mul_zero,
      and_self]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem mem_heisY {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
    {y : InfinitePlace E → ι → ℂ} : y ∈ heisY h v x₀ w₀ ↔
      ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
        hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0 := Iff.rfl

abbrev HeisCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :=
  heisY h v x₀ w₀ × (InfinitePlace E → ℝ)

def heisMatAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (y : InfinitePlace E → ι → ℂ) (t : InfinitePlace E → ℝ) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  heisMat (gramAt h v w) (vecAt v x₀ w) (y w) (heisS (gramAt h v w) (y w) (t w))

omit [DecidableEq ι] in
theorem heisS_add {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (y₁ y₂ : ι → ℂ) (t₁ t₂ : ℝ) :
    heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂ =
      heisS H (y₁ + y₂) (t₁ + t₂ - (hForm H y₁ y₂).im) := by
  have hs : (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      starRingEnd ℂ (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      hForm H (y₁ + y₂) (y₁ + y₂) = 0 := by
    have e1 := heisS_spec hH y₁ t₁
    have e2 := heisS_spec hH y₂ t₂
    have e3 := hForm_conj hH y₁ y₂
    simp only [map_add (f := _), map_sub, hForm_add_left, hForm_add_right]
    linear_combination e1 + e2 - e3
  rw [eq_heisS hs]
  congr 1

section Coords

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem heisMatAt_mul (hp : IsHyperbolicPair h x₀ w₀) {y₁ y₂ : InfinitePlace E → ι → ℂ}
    (hy₁ : y₁ ∈ heisY h v x₀ w₀) (hy₂ : y₂ ∈ heisY h v x₀ w₀) (t₁ t₂ : InfinitePlace E → ℝ)
    (w : InfinitePlace E) :
    heisMatAt h v x₀ y₁ t₁ w * heisMatAt h v x₀ y₂ t₂ w = heisMatAt h v x₀ (y₁ + y₂)
      (t₁ + t₂ - fun w => (hForm (gramAt h v w) (y₁ w) (y₂ w)).im) w := by
  obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
  rw [heisMatAt, heisMatAt, heisMat_mul hH ha (hy₁ w).1 (hy₂ w).1, heisS_add hH, heisMatAt]
  rfl

def heisUnit (hp : IsHyperbolicPair h x₀ w₀) (y : heisY h v x₀ w₀) (t : InfinitePlace E → ℝ)
    (w : InfinitePlace E) : GL ι ℂ where
  val := heisMatAt h v x₀ y t w
  inv := heisMatAt h v x₀ (-(y : InfinitePlace E → ι → ℂ)) (-t) w
  val_inv := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp y.2 (neg_mem y.2), heisMatAt]
    simp only [add_neg_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_right, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero
  inv_val := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp (neg_mem y.2) y.2, heisMatAt]
    simp only [neg_add_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_left, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero

def heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) : unipRadical h v x₀ :=
  ⟨⟨fun w => heisUnit hp p.1 p.2 w, mem_archUnitary.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      rw [map_conj_transpose]
      exact heisMat_unitary hH ha (p.1.2 w).1 (heisS_spec hH _ _)⟩,
    mem_unipRadical.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      refine ⟨heisMat_mulVec_self hH ha (p.1.2 w).1 _, fun z hz => ⟨-hForm (gramAt h v w)
        ((p.1 : InfinitePlace E → ι → ℂ) w) z, ?_⟩⟩
      change heisMat _ _ _ _ *ᵥ z = _
      rw [heisMat_mulVec, show hForm (gramAt h v w) (vecAt v x₀ w) z = 0 from hz]
      simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]⟩

theorem heisPoint_val (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    ((((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) = heisMatAt h v x₀ p.1 p.2 w := rfl


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem unipRadical_at_place (n : unipRadical h v x₀) (w : InfinitePlace E) :
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)ᴴ * gramAt h v w *
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      vecAt v x₀ w ∧
    ∀ z, hForm (gramAt h v w) (vecAt v x₀ w) z = 0 → ∃ c : ℂ,
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        z + c • vecAt v x₀ w :=
  ⟨archUnitary_at_place _ w, (mem_unipRadical.1 n.2 w).1, (mem_unipRadical.1 n.2 w).2⟩

def heisU (n : unipRadical h v x₀) (w : InfinitePlace E) : ι → ℂ :=
  (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

def heisYOf (n : unipRadical h v x₀) : InfinitePlace E → ι → ℂ := fun w =>
  heisU (w₀ := w₀) n w - hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) • vecAt v x₀ w

theorem heisYOf_spec (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) +
      starRingEnd ℂ (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) +
      hForm (gramAt h v w) (heisYOf (w₀ := w₀) n w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w)
        (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  obtain ⟨hn, hna, hn'⟩ := unipRadical_at_place n w
  exact eq_heisMat hH ha hb hab hn hna hn'

def heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) : HeisCoord h v x₀ w₀ :=
  (⟨heisYOf n, fun w => ⟨(heisYOf_spec hp n w).1, (heisYOf_spec hp n w).2.1⟩⟩,
    fun w => (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)).im)

end Coords

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
