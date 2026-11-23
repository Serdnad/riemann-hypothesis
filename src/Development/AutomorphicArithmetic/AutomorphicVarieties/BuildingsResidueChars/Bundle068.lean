module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open UpperTheory.V.Sd.Eis

private theorem exists_addChar_fourier_coeff_ne_zero_of_ne_zero {α : Type} [AddCommGroup α] [Fintype α] (F : α → ℂ) (hF : F ≠ 0) :
    ∃ ψ : AddChar α ℂ, ∑ a, F a * ψ (-a) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hF
  funext x
  have key : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = (Fintype.card α : ℂ) * F x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key2 : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ _
    simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_left_comm (F _), ← Finset.mul_sum, h ψ,
      mul_zero]
  have hc : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := key.symm.trans key2
  simpa [hc] using this

theorem UpperTheory.exists_character_separation :
    UpperTheory.V.Sd.Eis.CharPick := by
  intro T _ U₀ hU₀ f₀ hf₀ hinv
  classical
  have inv_out : ∀ (V : Subgroup T) (w : T → ℂ), (∀ t u, u ∈ V → w (t * u) = w t) →
      ∀ t : T, w ((QuotientGroup.mk t : T ⧸ V).out) = w t := by
    intro V w hw t
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V t
    rw [hh, hw _ _ h.2]
  haveI : Fintype (T ⧸ U₀) := Fintype.ofFinite _
  let F : Additive (T ⧸ U₀) → ℂ := fun a => f₀ (Additive.toMul a).out
  have hF : F ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hf₀
    intro h0
    apply ht
    have := congrFun h0 (Additive.ofMul (QuotientGroup.mk t))
    simp only [F, toMul_ofMul, Pi.zero_apply] at this
    rw [inv_out U₀ f₀ hinv t] at this
    exact this
  obtain ⟨ψ, hψ⟩ := exists_addChar_fourier_coeff_ne_zero_of_ne_zero F hF
  let χ : T →* ℂˣ :=
    { toFun := fun t => ⟨ψ (Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀)),
        ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))),
        by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
        by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [AddChar.map_add_eq_mul] }
  have hχval : ∀ t, (((χ t)⁻¹ : ℂˣ) : ℂ) = ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))) :=
    fun t => rfl
  have hχU₀ : ∀ u ∈ U₀, χ u = 1 := by
    intro u hu
    ext
    simp [χ, (QuotientGroup.eq_one_iff u).mpr hu]
  let aV : Subgroup T → (T → ℂ) → ℂ := fun V h =>
    ∑ᶠ q : T ⧸ V, h q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
  have aV_lin : ∀ V : Subgroup T, V.FiniteIndex → ∀ (c : ℂ) (p p' : T → ℂ),
      aV V (c • p + p') = c * aV V p + aV V p' := by
    intro V hV c p p'
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    simp only [aV, finsum_eq_sum_of_fintype, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have aV_zero : ∀ V : Subgroup T, aV V 0 = 0 := by
    intro V; simp [aV]
  have kill : ∀ V : Subgroup T, V.FiniteIndex → V ≤ U₀ → ∀ g : T → ℂ,
      (∀ t u, u ∈ V → g (t * u) = g t) → ∀ s, aV V (fun t => g (t * s)) = (χ s : ℂ) * aV V g := by
    intro V hV hVU g hg s
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let φ : T → ℂ := fun t => g t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ : ∀ t u, u ∈ V → φ (t * u) = φ t := by
      intro t u hu
      simp only [φ, map_mul, hχU₀ u (hVU hu), mul_one, hg t u hu]
    simp only [aV, finsum_eq_sum_of_fintype]
    have hre : ∑ q : T ⧸ V, g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
        = ∑ q : T ⧸ V, g (q * (QuotientGroup.mk s : T ⧸ V)).out
            * (((χ (q * (QuotientGroup.mk s : T ⧸ V)).out)⁻¹ : ℂˣ) : ℂ) :=
      (Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk s : T ⧸ V))
        (fun q => g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ))).symm
    rw [hre, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hq : q * (QuotientGroup.mk s : T ⧸ V) = QuotientGroup.mk (q.out * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have h2 := inv_out V φ hφ (q.out * s)
    rw [hq]
    change _ = _ * φ _
    rw [h2]
    simp only [φ, map_mul, mul_inv, Units.val_mul]
    have hs1 : (χ s : ℂ) * (((χ s)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (-(g (q.out * s) * (((χ q.out)⁻¹ : ℂˣ) : ℂ))) * hs1
  have fiber : ∀ V : Subgroup T, V ≤ U₀ → V.FiniteIndex → aV V f₀ ≠ 0 := by
    intro V hVU hV
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let π : T ⧸ V →* T ⧸ U₀ := QuotientGroup.map V U₀ (MonoidHom.id T) (fun x hx => hVU hx)
    let φ0 : T → ℂ := fun t => f₀ t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ0 : ∀ t u, u ∈ U₀ → φ0 (t * u) = φ0 t := by
      intro t u hu
      simp only [φ0, map_mul, hχU₀ u hu, mul_one, hinv t u hu]
    let Kf : T ⧸ U₀ → ℂ := fun r => φ0 r.out
    have hH : ∀ q : T ⧸ V, f₀ q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ) = Kf (π q) := by
      intro q
      have : π q = QuotientGroup.mk q.out := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      exact (inv_out U₀ φ0 hφ0 q.out).symm
    have hsurj : ∀ r : T ⧸ U₀, r ∈ Set.range π := by
      intro r
      refine ⟨QuotientGroup.mk r.out, ?_⟩
      change (QuotientGroup.mk r.out : T ⧸ U₀) = r
      exact QuotientGroup.out_eq' r
    have hcard : ∀ r : T ⧸ U₀, (Finset.univ.filter fun q => π q = r).card
        = (Finset.univ.filter fun q => π q = 1).card :=
      fun r => MonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 1)
    have hpos : (Finset.univ.filter fun q => π q = 1).card ≠ 0 := by
      rw [Finset.card_ne_zero]
      exact ⟨1, by simp⟩
    have hsumK : ∑ r, Kf r ≠ 0 := by
      have e : ∑ r, Kf r = ∑ a, F a * ψ (-a) := by
        refine Fintype.sum_equiv Additive.ofMul _ _ (fun r => ?_)
        simp only [Kf, φ0, F, hχval, QuotientGroup.out_eq', toMul_ofMul]
      rw [e]; exact hψ
    simp only [aV, finsum_eq_sum_of_fintype, hH]
    rw [← Finset.sum_fiberwise' Finset.univ π Kf]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos) hsumK
  let Kset : Set (T → ℂ) := {p | ∃ (U : Subgroup T) (g : T → ℂ) (s : T), U.FiniteIndex ∧
      (∀ t u, u ∈ U → g (t * u) = g t) ∧ p = (fun t => g (t * s)) - (χ s : ℂ) • g}
  have key : ∀ p : T → ℂ, p ∈ Submodule.span ℂ Kset → ∃ V : Subgroup T, V ≤ U₀ ∧ V.FiniteIndex ∧
      ∀ V' : Subgroup T, V' ≤ V → V'.FiniteIndex → aV V' p = 0 := by
    intro p hmem
    induction hmem using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨U, g, s, hU, hg, rfl⟩ := hp
      haveI := hU
      haveI := hU₀
      refine ⟨U ⊓ U₀, inf_le_right, inferInstance, fun V' hV' hV'f => ?_⟩
      have hg' : ∀ t u, u ∈ V' → g (t * u) = g t :=
        fun t u hu => hg t u (Subgroup.mem_inf.mp (hV' hu)).1
      have e : (fun t => g (t * s)) - (χ s : ℂ) • g = (-(χ s : ℂ)) • g + (fun t => g (t * s)) := by
        funext t; simp; ring
      rw [e, aV_lin V' hV'f, kill V' hV'f (hV'.trans inf_le_right) g hg' s]
      ring
    | zero => exact ⟨U₀, le_rfl, hU₀, fun V' _ _ => aV_zero V'⟩
    | add x y _ _ hx hy =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      obtain ⟨V2, hV2U, hV2f, hV2⟩ := hy
      haveI := hV1f
      haveI := hV2f
      refine ⟨V1 ⊓ V2, inf_le_left.trans hV1U, inferInstance, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f 1 x y
      rw [one_smul, one_mul] at this
      rw [this, hV1 V' (hV'.trans inf_le_left) hV'f, hV2 V' (hV'.trans inf_le_right) hV'f, add_zero]
    | smul c x _ hx =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      refine ⟨V1, hV1U, hV1f, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f c x 0
      rw [add_zero, aV_zero, add_zero] at this
      rw [this, hV1 V' hV' hV'f, mul_zero]
  have hnot : f₀ ∉ Submodule.span ℂ Kset := by
    intro hmem
    obtain ⟨V, hVU, hVf, hV⟩ := key f₀ hmem
    exact fiber V hVU hVf (hV V le_rfl hVf)
  obtain ⟨L, hL, hLK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨χ, L, hχU₀, hL, ?_⟩
  intro U hU f hf s
  have hmemK : (fun t => f (t * s)) - (χ s : ℂ) • f ∈ Submodule.span ℂ Kset :=
    Submodule.subset_span ⟨U, f, s, hU, hf, rfl⟩
  have h0 : L ((fun t => f (t * s)) - (χ s : ℂ) • f) = 0 := by
    have := Submodule.mem_map_of_mem (f := L) hmemK
    rw [hLK, Submodule.mem_bot] at this
    exact this
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0
end

section

open UpperTheory.V.Sd.Eis
open MeasureTheory Measure Pointwise

private theorem perMean_fin {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (hc : Cocpt Γ) (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) : μ D ≠ ⊤ := by
  obtain ⟨C, hC, hcov⟩ := hc
  have h1 : D ⊆ ⋃ g : Γ, ((g +ᵥ C) ∩ D) := by
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨x - γ, h, ?_⟩, hx⟩
    change γ + (x - γ) = x
    abel
  have h2 : μ D ≤ μ C := by
    rw [hD.measure_eq_tsum C]
    exact (measure_mono h1).trans (measure_iUnion_le _)
  exact ne_top_of_le_ne_top hC.measure_lt_top.ne h2

private theorem perMean_key {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) (hfin : μ D ≠ ⊤) (e : A ≃ᵐ A) (c : NNReal)
    (he : μ.map e = c • μ) (σ : Γ → Γ) (hσ : Function.Bijective σ) (hs : ∀ (g : Γ) x, e ((σ g : A) + x) = (g : A) + e x)
    (f : A → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) :
    ∫ x in D, f (e x) ∂μ = ∫ x in D, f x ∂μ := by
  have hq : QuasiMeasurePreserving e μ μ := ⟨e.measurable.aemeasurable, by rw [he]; exact Measure.smul_absolutelyContinuous⟩
  have hD' : IsAddFundamentalDomain Γ (e ⁻¹' D) μ := hD.preimage_of_equiv hq hσ (fun g x => hs g x)
  have hm : μ (e ⁻¹' D) = μ D := by
    have := hD'.measure_set_eq hD MeasurableSet.univ (fun g => by simp)
    simpa using this
  have h0 : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hc : (c : ENNReal) = 1 := by
    rw [← e.map_apply, he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hm
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [hm, one_mul])
  have hc' : c = 1 := by exact_mod_cast hc
  rw [hc', one_smul] at he
  have h1 : ∫ x in D, f (e x) ∂μ = ∫ x in e ⁻¹' D, f (e x) ∂μ := by
    refine hD.setIntegral_eq hD' (fun g x => ?_)
    obtain ⟨g', rfl⟩ := hσ.2 g
    change f (e ((σ g' : A) + x)) = _
    rw [hs, hf _ g'.2]
  rw [h1, ← setIntegral_map_equiv, he]

theorem UpperTheory.periodic_integral_fundamentalDomain_invariant :
    UpperTheory.V.Sd.Eis.PerMean := by
  intro A _ _ _ _ _ _ _ _ Γ _ hc μ _ D hD
  have hfin := perMean_fin Γ hc μ D hD
  refine ⟨hfin, fun f hf => ⟨fun hcont => ?_, fun y => ?_, fun e he => ?_⟩⟩
  · obtain ⟨C, hC, hcov⟩ := hc
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
    refine Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨γ, hγ, h⟩ := hcov x
    have := hf γ hγ (x - γ)
    rw [add_sub_cancel] at this
    rw [this]
    exact hM _ h
  · refine perMean_key Γ μ D hD hfin (MeasurableEquiv.addRight y) 1 ?_ id Function.bijective_id ?_ f hf
    · rw [one_smul]
      exact map_add_right_eq_self μ y
    · intro g x
      exact add_assoc _ _ _
  · haveI : (μ.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ e
    refine perMean_key Γ μ D hD hfin e.toHomeomorph.toMeasurableEquiv _
      (Measure.isAddLeftInvariant_eq_smul (μ.map e) μ)
      (fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩) ⟨fun a b h => ?_, fun b => ⟨⟨e b, (he _).2 b.2⟩, ?_⟩⟩ ?_ f hf
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact Subtype.ext (e.symm_apply_apply _)
    · intro g x
      change e (e.symm g + x) = g + e x
      rw [map_add (f := _), e.apply_symm_apply]
end

section

open UpperTheory.V.Sd.Eis

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_cont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (TR.infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (TR.sInf F : TR.Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_aff_add (F : Type) [Field F] [NumberField F] (y : F) (x : Ad F) :
    (aff 1 (algebraMap F (Ad F) y + x) : GA F 2) = ratGL F 2 (aff 1 y) * aff 1 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, ratGL, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
private theorem ct_level (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a) (X : TR.Lie F a)
    (h : IsOpen {k | TR.finRep F a k φ = φ}) : IsOpen {k | TR.finRep F a k (TR.lie F a X φ) = TR.lie F a X φ} := by
  let S : TR.Sm F a → Subgroup (GL (Fin a) (Af F)) := fun ψ =>
    { carrier := {k | TR.finRep F a k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine Subgroup.isOpen_mono (H₁ := S φ) (H₂ := S (TR.lie F a X φ)) (fun k hk => ?_) h
  have hk' : TR.rt F a (finGL F a k) φ = φ := hk
  have e := LinearMap.congr_fun (TR.lie_rt_fin X k) φ
  rw [Module.End.mul_apply, Module.End.mul_apply, hk'] at e
  exact e.symm

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.constant_term_automorphy :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.PerDeriv → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtLie := by
  intro hS hM hD hB F _ _ _ _ _ μ _ D hF φ hl ho X
  have hl' : ∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g := by
    intro γ g
    have e : TR.chart φ.1 (ratGL F 2 γ * g) = TR.chart φ.1 g := by
      funext x
      simp only [TR.chart, mul_assoc, hl]
    simp only [TR.lie_apply, TR.lieD, e]
  have hc' : Continuous (TR.lie F 2 X φ).1 := hS F 2 _ (ct_level F 2 φ X ho)
  have hc : Continuous φ.1 := hS F 2 _ ho
  refine ⟨⟨hl', hc'⟩, fun c hcc hmul hder g => ?_⟩
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have h0 : c 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin := (hM (NA F) (ratN F 2 1) hco μ D hF).1
  have hcont : Continuous fun p : NA F × ℝ => (unip p.1 : GA F 2) * (g * TR.infGL F 2 (c p.2)) :=
    (hu.comp continuous_fst).mul (continuous_const.mul ((ct_cont_infGL F 2).comp (hcc.comp continuous_snd)))
  have hper : ∀ ψ : GA F 2 → ℂ, (∀ γ g, ψ (ratGL F 2 γ * g) = ψ g) → ∀ γ ∈ ratN F 2 1, ∀ (x : NA F) (h : GA F 2),
      ψ (unip (γ + x) * h) = ψ (unip x * h) := by
    rintro ψ hψ _ ⟨y, rfl⟩ x h
    rw [hx, hx x]
    refine Eq.trans ?_ (hψ (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, ← ct_aff_add]
    rfl
  have key := hD (NA F) (ratN F 2 1) hco μ D hfin
    (fun x t => φ.1 (unip x * (g * TR.infGL F 2 (c t))))
    (fun x t => (TR.lie F 2 X φ).1 (unip x * (g * TR.infGL F 2 (c t))))
    (hc.comp hcont) (hc'.comp hcont)
    (fun γ hγ x => funext fun t => hper _ hl γ hγ x _)
    (fun γ hγ x => funext fun t => hper _ hl' γ hγ x _)
    (fun x t => by
      have h1 := TR.hasDerivAt_curve φ (unip x * (g * TR.infGL F 2 (c t))) c X h0 hder
      have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
      have h3 := HasDerivAt.scomp_of_eq t h1 h2 (sub_self t).symm
      rw [one_smul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, mul_assoc, ← map_mul, ← hmul, add_sub_cancel])
  simpa only [cterm, h0, map_one, mul_one] using key
end

section

open UpperTheory.V.Sd.Eis

open UpperTheory.V.Sd in
private theorem cb_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd in
private theorem cb_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]


open NumberField GlobalTheory.CuspRep in
private noncomputable def cb_scale (F : Type) [Field F] [NumberField F] (u : (Ad F)ˣ) : NA F ≃ₜ+ NA F where
  toFun x p := (u : Ad F) * x p
  invFun x p := ((u⁻¹ : (Ad F)ˣ) : Ad F) * x p
  left_inv x := funext fun p => Units.inv_mul_cancel_left u (x p)
  right_inv x := funext fun p => Units.mul_inv_cancel_left u (x p)
  map_add' x y := funext fun p => mul_add _ _ _
  continuous_toFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)
  continuous_invFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)

open NumberField GlobalTheory.CuspRep in
private theorem cb_mem (F : Type) [Field F] [NumberField F] (a : F) (x : NA F) (hx : x ∈ ratN F 2 1) :
    (fun p => algebraMap F (Ad F) a * x p) ∈ ratN F 2 1 := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => a * y p, funext fun p => map_mul (algebraMap F (Ad F)) _ _⟩

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock :
    UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtBasic := by
  intro hM hB F _ _ _ _ μ _ D hF φ hc hl
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have hper : ∀ (h : GA F 2), ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * h) = φ (unip x * h) := by
    rintro h _ ⟨y, rfl⟩ x
    rw [hx, hx x]
    refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, cb_rat_aff, cb_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
    rfl
  have key := fun g : GA F 2 =>
    (hM (NA F) (ratN F 2 1) hco μ D hF).2 (fun x => φ (unip x * g)) (hper g)
  refine ⟨fun g => (key g).1 (hc.comp (hu.mul continuous_const)), fun y g => ?_, fun a g => ?_⟩
  · unfold cterm
    refine Eq.trans ?_ ((key g).2.1 fun _ => y)
    refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
    rw [hx, hx, ← mul_assoc, cb_aff_mul, one_mul, Units.val_one, one_mul, add_comm y]
    rfl
  · let u : (Ad F)ˣ := Units.map (algebraMap F (Ad F)).toMonoidHom a
    unfold cterm
    refine Eq.trans ?_ ((key g).2.2 (cb_scale F u⁻¹) fun x => ⟨fun h => ?_, fun h => cb_mem F ((a⁻¹ : Fˣ) : F) x h⟩)
    · refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
      refine Eq.trans ?_ (hl (aff a 0) _)
      rw [hx, hx, cb_rat_aff, map_zero, ← mul_assoc, ← mul_assoc, cb_aff_mul, cb_aff_mul, one_mul, mul_one,
        mul_zero, zero_add, add_zero]
      change φ (aff u _ * g) = φ (aff u ((u : Ad F) * (((u⁻¹ : (Ad F)ˣ) : Ad F) * x _)) * g)
      rw [Units.mul_inv_cancel_left]
    · have h2 := cb_mem F (a : F) _ h
      have e : (fun p => algebraMap F (Ad F) (a : F) * cb_scale F u⁻¹ x p) = x :=
        funext fun p => Units.mul_inv_cancel_left u (x p)
      rwa [e] at h2
end

section

open UpperTheory.V.Sd.Eis NumberField GlobalTheory.Mem.Chr.CharModel

theorem UpperTheory.eisenstein_norm_eq_abs_pow :
    UpperTheory.V.Sd.Eis.AbsPow := by
  intro F _ _ _ s
  have H := absChar_isAbsPow (F := F) s
  refine ⟨⟨absHom F s, (absChar F s).2⟩, fun y hy => ?_, fun w => ⟨H.1 w, ?_⟩⟩
  · change Complex.exp (s * logNorm F (UpperTheory.V.TR.infId F y)) = _
    have h1 : finPart F (UpperTheory.V.TR.infId F y) = 1 := by
      apply Units.ext
      change (UpperTheory.V.TR.infId F y).val.2 = 1
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).2 = 1
      change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) - 0 + 0 = 1
      simp
    have h2 : (infPart F (UpperTheory.V.TR.infId F y)).val = UpperTheory.V.TR.infEq F y.val := by
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).1 = _
      change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
      simp
    have h3 : ∀ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ = y.val w := fun w => by
      have := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.dist_eq (y.val w) 0
      have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
        map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      rw [e0, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hy w).le] at this
      exact this
    rw [logNorm, h1, logFin_one, sub_zero, logInf, h2]
    simp only [h3, InfinitePlace.mult, IsTotallyReal.isReal, if_true, Nat.cast_one, one_mul]
    rw [← Real.log_prod (fun w _ => (hy w).ne'), Real.rpow_def_of_pos (Finset.prod_pos fun w _ => hy w),
      Complex.ofReal_exp, Complex.ofReal_mul, mul_comm]
  · refine (H.2.1 w).trans ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
end
