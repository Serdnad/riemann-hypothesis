module

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfForallZpow
public import Formalism.LocalToGlobal.UnitaryNorms.UnrAe
import Mathlib.Algebra.Order.Star.Real
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology

namespace Formalism.L2.Fam.IdTrans

theorem re_gt_half {b : ℂ} (hb : ‖b‖ = 1) (h : ‖b - 1‖ < 1) : 1 / 2 < b.re := by
  have h1 : b.re * b.re + b.im * b.im = 1 := by
    have h0 := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at h0
    linarith
  have h3 : ‖b - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (b - 1)]
  rw [Complex.sq_norm, Complex.normSq_apply] at h3
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
  nlinarith

theorem one_sub_re_sq {b : ℂ} (hb : ‖b‖ = 1) : 1 - (b ^ 2).re = 2 * (1 - b.re) * (1 + b.re) := by
  have h1 : b.re * b.re + b.im * b.im = 1 := by
    have h0 := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at h0
    linarith
  rw [sq, Complex.mul_re]
  linear_combination h1

theorem eq_one_of_pow {a : ℂ} (h : ∀ n : ℤ, ‖a ^ n - 1‖ < 1) (ha : a ≠ 0) : a = 1 := by
  apply _root_.UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> assumption

section Top

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  exact Valued.isOpen_integer _

open Classical in
theorem finiteSingle_eq (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) (hx : x ∈ v.adicCompletionIntegers L) :
    finiteSingle L v x = RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite
      (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L)) := by
  apply RestrictedProduct.ext
  intro w
  show (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v x w) =
    ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => ↥(w.adicCompletionIntegers L)) v ⟨x, hx⟩ w :
      w.adicCompletionIntegers L) : w.adicCompletion L)
  by_cases h : w = v
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

theorem single_mem_nhds {S : Set (AdeleRing (𝓞 L) L)} (hS : S ∈ 𝓝 (1 : AdeleRing (𝓞 L) L)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 L)), I.Finite ∧ ∀ v ∉ I, ∀ (x : v.adicCompletion L) (_hx : x ∈ v.adicCompletionIntegers L),
      (((1 : InfiniteAdeleRing L), finiteSingle L v x) : AdeleRing (𝓞 L) L) ∈ S := by
  have hS' : S ∈ 𝓝 (((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) : InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) := hS
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hS'
  have hw' : w ∈ Filter.map (RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite)
      (𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_integers v)]
    exact hw
  have hw'' : RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite ⁻¹' w ∈
      𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L) := hw'
  rw [nhds_pi, Filter.mem_pi] at hw''
  obtain ⟨I, hI, t, ht, hIt⟩ := hw''
  refine ⟨I, hI, fun v hv x hx => huw ⟨mem_of_mem_nhds hu, ?_⟩⟩
  classical
  have hf : (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L) : Π v : HeightOneSpectrum (𝓞 L),
      v.adicCompletionIntegers L) ∈ I.pi t := by
    intro w' hw'
    have hne : w' ≠ v := fun h => hv (h ▸ hw')
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht w')
  have := hIt hf
  show finiteSingle L v x ∈ w
  rw [finiteSingle_eq v x hx]
  exact this

end Top

theorem unrAE {L : Type} [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  classical
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1} with hWdef
  have hWo : IsOpen W := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hW1 : (1 : ℂˣ) ∈ W := by simp [hWdef]
  have hN : χ ⁻¹' W ∈ 𝓝 (1 : Ideles L) := by
    apply hχ.continuousAt.preimage_mem_nhds
    rw [map_one]
    exact hWo.mem_nhds hW1
  rw [(Units.isEmbedding_embedProduct (M := AdeleRing (𝓞 L) L)).isInducing.nhds_eq_comap] at hN
  obtain ⟨T, hT, hTN⟩ := hN
  rw [map_one] at hT
  have hT' : T ∈ 𝓝 (((1 : AdeleRing (𝓞 L) L), (1 : (AdeleRing (𝓞 L) L)ᵐᵒᵖ))) := hT
  obtain ⟨T1, hT1, T2, hT2, hT12⟩ := mem_nhds_prod_iff.mp hT'
  have hT2' : MulOpposite.op ⁻¹' T2 ∈ 𝓝 (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact hT2)
  obtain ⟨I1, hI1, h1⟩ := single_mem_nhds hT1
  obtain ⟨I2, hI2, h2⟩ := single_mem_nhds hT2'
  have hmem : ∀ v ∉ I1 ∪ I2, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) ∈ W := by
    intro v hv x hx
    have hv1 : v ∉ I1 := fun h => hv (Or.inl h)
    have hv2 : v ∉ I2 := fun h => hv (Or.inr h)
    have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx
    have hxO' : ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
      rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, inv_one]
    apply hTN
    apply hT12
    refine ⟨h1 v hv1 _ hxO, ?_⟩
    show (((localIdele L v x)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) ∈ MulOpposite.op ⁻¹' T2
    rw [← map_inv]
    exact h2 v hv2 _ hxO'
  refine Filter.mem_of_superset (hI1.union hI2).compl_mem_cofinite fun v hv x hx => ?_
  apply Units.ext
  apply eq_one_of_pow _ (Units.ne_zero _)
  intro n
  have hxn : IsUnitAt v (x ^ n) := by
    show Valued.v (((x ^ n : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_zpow]
  have := hmem v hv (x ^ n) hxn
  rw [map_zpow, map_zpow] at this
  have h' : ‖(((χ (localIdele L v x)) ^ n : ℂˣ) : ℂ) - 1‖ < 1 := this
  rwa [Units.val_zpow_eq_zpow_val] at h'

theorem unrAe {L : Type} [Field L] [NumberField L] (χ : HChar L) : ∀ᶠ v in cofinite, χ.UnrAt v := (unrAE (L := L) χ.1 χ.2.1).mono fun v hv x hx => hv x hx

section UnitsTriv

variable {L : Type} [Field L] [NumberField L]


end UnitsTriv

section UnitsTrivPf

variable {L : Type} [Field L] [NumberField L]

end UnitsTrivPf

end Formalism.L2.Fam.IdTrans
