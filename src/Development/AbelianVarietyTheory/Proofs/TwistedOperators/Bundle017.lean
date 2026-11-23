module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem unfolding_cover_bound (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) [Countable Γ] (Kc : Set H)
    (hK : ∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) (F : G → ENNReal)
    (hF : ∀ γ : G, Measurable fun h => F (γ * ι h)) :
    ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  classical
  haveI hcH : Countable (Γ.comap ι) := by
    have : Function.Injective (fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) := by
      intro a b hab
      apply Subtype.ext
      apply hι
      simpa using congrArg Subtype.val hab
    exact this.countable
  have step : ∀ g : G, ∫⁻ h, F (g * ι h) ∂μ
      ≤ ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
    intro g
    have hcov : (Set.univ : Set H) = ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc := by
      ext h
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, true_iff]
      obtain ⟨δ, hδ, hδK⟩ := hK h
      exact ⟨⟨δ, hδ⟩, hδK⟩
    calc ∫⁻ h, F (g * ι h) ∂μ
        = ∫⁻ h in ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ := by
          rw [← hcov, Measure.restrict_univ]
      _ ≤ ∑' δ : Γ.comap ι, ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
          congr 1; funext δ
          set e := MeasurableEquiv.mulLeft ((δ:H)⁻¹) with he
          have hmap : μ.map e = μ := by
            rw [MeasurableEquiv.coe_mulLeft]; exact map_mul_left_eq_self μ _
          have hpre : e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc) = Kc := by
            ext k; simp [e]
          calc ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ
              = ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂(μ.map e) := by rw [hmap]
            _ = ∫⁻ h, F (g * ι h) ∂((μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))).map e) := by
                rw [e.restrict_map]
            _ = ∫⁻ k, F (g * ι (e k)) ∂(μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))) :=
                lintegral_map_equiv _ _
            _ = _ := by rw [hpre]; simp [e, mul_assoc]
  haveI : Countable (Γ ⧸ ι.range.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  let φ : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p =>
    (p.1.out : Γ) * ⟨ι ((p.2 : H)⁻¹), by simpa using Γ.inv_mem p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨q₁, δ₁⟩ ⟨q₂, δ₂⟩ h
    have hv := congrArg Subtype.val h
    simp only [φ, Subgroup.coe_mul] at hv
    have hq : q₁ = q₂ := by
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨(δ₁:H)⁻¹ * (δ₂:H), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((q₁.out : Γ) : G)⁻¹ * ((q₂.out : Γ) : G)
          = ((q₁.out : Γ) : G)⁻¹ * (((q₂.out : Γ) : G) * ι ((δ₂:H)⁻¹)) * ι (δ₂:H) by
            rw [map_inv]; group, ← hv]
      simp only [map_mul, map_inv]; group
    subst hq
    have h2 : ι ((δ₁:H)⁻¹) = ι ((δ₂:H)⁻¹) := mul_left_cancel hv
    have h3 : (δ₁:H)⁻¹ = (δ₂:H)⁻¹ := hι h2
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext (inv_injective h3)
  calc ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' δ : Γ.comap ι,
          ∫⁻ k in Kc, F (((φ (q, δ)) : G) * ι k) ∂μ := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        exact step _
    _ = ∑' p, ∫⁻ k in Kc, F ((φ p : G) * ι k) ∂μ := ENNReal.tsum_prod.symm
    _ = ∫⁻ k in Kc, ∑' p, F ((φ p : G) * ι k) ∂μ :=
        (lintegral_tsum fun p => (hF _).aemeasurable).symm
    _ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ :=
        lintegral_mono fun k => ENNReal.tsum_comp_le_tsum_of_injective hφ (fun γ : Γ => F (γ * ι k))

end GlobalTheory
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
end

section

open MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.UnipChange

section Shear

variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]

end Shear

section Linear

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_mul_left_eq_smul' (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) ν = distribHaarChar F (Units.mk0 a ha)⁻¹ • ν := by
  have hf : (fun x : F => a * x) = fun x => Units.mk0 a ha • x := by
    funext x; simp [Units.smul_def]
  ext s hs
  rw [Measure.map_apply (by rw [hf]; exact (continuous_const_smul _).measurable) hs, hf,
    Set.preimage_smul, ← distribHaarChar_mul ν]
  rw [Measure.coe_nnreal_smul_apply]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_diagonal_mulVec_pi (D : κ → F) (hD : ∀ i, D i ≠ 0) :
    Measure.map (diagonal D).mulVec (Measure.pi fun _ : κ => ν)
      = (∏ i, distribHaarChar F (Units.mk0 (D i) (hD i))⁻¹) • Measure.pi fun _ : κ => ν := by
  have hfun : (diagonal D).mulVec = fun x i => (fun y => D i * y) (x i) := by
    funext x i; simp [mulVec_diagonal]
  haveI : ∀ i, SigmaFinite (Measure.map (fun y => D i * y) ν) := fun i => by
    rw [map_mul_left_eq_smul' ν (D i) (hD i)]; infer_instance
  rw [hfun, Measure.pi_map_pi (f := fun i y => D i * y)
    (fun i => (continuous_const.mul continuous_id).aemeasurable)]
  simp_rw [map_mul_left_eq_smul' ν _ (hD _)]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.coe_nnreal_smul_apply _ _ _

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem measurePreserving_transvection_mulVec (t : TransvectionStruct κ F) :
    MeasurePreserving t.toMatrix.mulVec (Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => ν) := by
  let p : κ → Prop := fun i => i ≠ t.i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → F) → (β → F) → β → F := fun a b => (fun _ => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let G : (α → F) × (β → F) → (α → F) × (β → F) := fun q => (id q.1, g q.1 q.2)
  let e : (κ → F) ≃ᵐ (α → F) × (β → F) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => F) p
  have hmv : t.toMatrix.mulVec = e.symm ∘ G ∘ e := by
    cases t with | mk i j hij c =>
    ext f k
    by_cases h : i = k
    · subst h
      simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, Matrix.single, ite_and, Matrix.one_apply, ite_mul]
      ring
    · simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, h, Matrix.single, ite_and, Ne.symm h, Matrix.one_apply,
        ite_mul]
  rw [hmv]
  have hA : MeasurePreserving e (Measure.pi fun _ : κ => ν)
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : κ => ν) p
  have hB : MeasurePreserving G ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have hg : Measurable (Function.uncurry g) := by
      refine Measurable.add ?_ measurable_snd
      exact Measurable.of_eval fun _ =>
        ((measurable_pi_apply _).comp measurable_fst).const_mul _
    exact (MeasurePreserving.id _).skew_product hg
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact ((hA.symm e).comp hB).comp hA


open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
theorem _root_.GlobalTheory.UnipChange.smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ)
    (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = Measure.pi fun _ : κ => ν := by
  have hmeas : ∀ N : Matrix κ κ F, Measurable N.mulVec := fun N =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have key : ∀ u : Fˣ, (u : F) = M.det → Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun N : Matrix κ κ F => ∀ u : Fˣ,
      (u : F) = N.det → Measure.map N.mulVec (Measure.pi fun _ : κ => ν)
        = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν) M
      (hu ▸ u.ne_zero) ?_ ?_ ?_
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := fun i => by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      rw [map_diagonal_mulVec_pi ν D hD']
      have hu' : u = ∏ i, Units.mk0 (D i) (hD' i) := by
        ext
        rw [hu, det_diagonal, Units.coe_prod]
        rfl
      rw [hu', ← Finset.prod_inv_distrib, map_prod]
    · intro t u hu
      have hu' : u = 1 := by
        ext
        rw [hu, TransvectionStruct.det, Units.val_one]
      rw [hu', inv_one, map_one, one_smul]
      exact (measurePreserving_transvection_mulVec ν t).map_eq
    · intro A B hA hB hPA hPB u hu
      have hcomp : (A * B).mulVec = A.mulVec ∘ B.mulVec :=
        funext fun x => (mulVec_mulVec x A B).symm
      have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := by
        ext
        simp [hu, det_mul]
      rw [hcomp, ← Measure.map_map (hmeas A) (hmeas B), hPB (Units.mk0 _ hB) rfl,
        Measure.map_smul _ (hmeas A).aemeasurable, hPA (Units.mk0 _ hA) rfl, smul_smul, hu', _root_.mul_inv_rev, map_mul,
        mul_comm]
  rw [key u hu]
  ext s hs
  rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]

end Linear

section Algebra

variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}



end Algebra

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}


end Top

end GlobalTheory.UnipChange
end

section

open MeasureTheory

namespace GlobalTheory.UnfoldNormal

def pairGroup {H : Type} [Group H] (Γ N : Subgroup H) (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) :
    Subgroup (H × H) where
  carrier := {p | p.1 ∈ Γ ∧ p.2 ∈ Γ ∧ p.1 * p.2⁻¹ ∈ N}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hb, hab⟩ ⟨hc, hd, hcd⟩
    refine ⟨Γ.mul_mem ha hc, Γ.mul_mem hb hd, ?_⟩
    have e : a * c * (b * d)⁻¹ = (a * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [e]
    exact N.mul_mem hab (hN b hb _ hcd)
  one_mem' := ⟨Γ.one_mem, Γ.one_mem, by simp [N.one_mem]⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    refine ⟨Γ.inv_mem ha, Γ.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹⁻¹ = a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    simp only [Prod.fst_inv, Prod.snd_inv]
    rw [e]
    exact hN _ (Γ.inv_mem ha) _ (N.inv_mem hab)

def shear {H : Type} [Group H] (N : Subgroup H) (p : N × H) : H × H := ((p.1 : H) * p.2, p.2)

end GlobalTheory.UnfoldNormal

namespace GlobalTheory.UnfoldNormal

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

def shearEquiv : H × H ≃ᵐ H × H where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.mul measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.mul measurable_snd.inv).prodMk measurable_snd

theorem shear_eq (N : Subgroup H) : shear N = shearEquiv ∘ Prod.map Subtype.val id := rfl

theorem measurableEmbedding_shear {N : Subgroup H} (hN : IsClosed (N : Set H)) :
    MeasurableEmbedding (shear N) := by
  rw [shear_eq]
  exact shearEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hN.measurableSet).prodMap MeasurableEmbedding.id)

theorem nullMeasurableSet_shear_image {N : Subgroup H} (hN : IsClosed (N : Set H)) (κ : Measure N)
    (ν : Measure H) {A : Set N} {B : Set H} (hA : NullMeasurableSet A κ) (hB : NullMeasurableSet B ν) :
    NullMeasurableSet (shear N '' (A ×ˢ B)) ((κ.prod ν).map (shear N)) := by
  have he := measurableEmbedding_shear hN
  have hAB : NullMeasurableSet (A ×ˢ B) (κ.prod ν) := hA.prod hB
  refine (he.measurableSet_image.2 (measurableSet_toMeasurable (κ.prod ν) (A ×ˢ B))).nullMeasurableSet.congr ?_
  refine (he.ae_map_iff (p := fun y => (y ∈ shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) ↔
    (y ∈ shear N '' (A ×ˢ B)))).2 ?_
  filter_upwards [hAB.toMeasurable_ae_eq] with x hx
  have e1 : shear N x ∈ shear N '' toMeasurable (κ.prod ν) (A ×ˢ B) ↔ x ∈ toMeasurable (κ.prod ν) (A ×ˢ B) :=
    he.injective.mem_set_image
  have e2 : shear N x ∈ shear N '' (A ×ˢ B) ↔ x ∈ (A ×ˢ B) := he.injective.mem_set_image
  rw [e1, e2]
  exact hx

end GlobalTheory.UnfoldNormal
end

section

namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin N → E) × Fin N =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let b : NumberField.RingOfIntegers E :=
    ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ((z p).2 : NumberField.RingOfIntegers E)
  refine ⟨b, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, i) ∈ s ×ˢ (Finset.univ : Finset (Fin N)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ i⟩)
    refine ⟨e * (z (g, i)).1, ?_⟩
    have h := hz (g, i)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show b = ((z (g, i)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro i
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    obtain ⟨c2, h2⟩ := hy i
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorLemma
end

end

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_unfolding_le_of_translate_cover : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (Kc : Set H), (∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) → ∀ F : G → ENNReal, (∀ γ : G, Measurable fun h => F (γ * ι h)) → ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  first | exact @GlobalTheory.unfolding_cover_bound | exact GlobalTheory.unfolding_cover_bound | (intros; apply GlobalTheory.unfolding_cover_bound <;> assumption)

end
end
