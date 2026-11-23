module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle019
public import Formalism.LocalToGlobal.IndefiniteReal.RhoSpec
import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3

end Formalism.IndefR.CxPass
end

section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section ConjIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def cj (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.AUTREP.GAf L n → ℂ := fun g => star (f g)

theorem cj_cj (f : Formalism.AUTREP.GAf L n → ℂ) : cj (cj f) = f := by
  funext g
  simp [cj]

theorem cj_add (f f' : Formalism.AUTREP.GAf L n → ℂ) : cj (f + f') = cj f + cj f' := by
  funext g
  simp [cj]

theorem cj_smul (a : ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : cj (a • f) = star a • cj f := by
  funext g
  simp [cj, mul_comm]

def toU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (f : conjSub U) : U := ⟨cj f.1, f.2⟩

def ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : conjSub U :=
  ⟨cj u.1, by
    show cj (cj u.1) ∈ U
    rw [cj_cj]
    exact u.2⟩

def conjMap {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (T : U →ₗ[ℂ] U') : conjSub U →ₗ[ℂ] conjSub U' where
  toFun f := ofU (T (toU f))
  map_add' f f' := by
    have : toU (f + f') = toU f + toU f' := Subtype.ext (cj_add f.1 f'.1)
    apply Subtype.ext
    show cj ((T (toU (f + f')) : U') : Formalism.AUTREP.GAf L n → ℂ) =
      cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ) + cj ((T (toU f') : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_add (f := _), Submodule.coe_add, cj_add]
  map_smul' a f := by
    have : toU (a • f) = star a • toU f := Subtype.ext (cj_smul a f.1)
    apply Subtype.ext
    show cj ((T (toU (a • f)) : U') : Formalism.AUTREP.GAf L n → ℂ) = a • cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_smul, Submodule.coe_smul, cj_smul, star_star]

theorem toU_ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : toU (ofU u) = u :=
  Subtype.ext (cj_cj u.1)

theorem conjT_iso {π π' : Formalism.L2.NG.FinTyp L n} (h : π.Iso π') : (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  obtain ⟨T, hT⟩ := h
  let E : conjSub π.S ≃ₗ[ℂ] conjSub π'.S :=
    { conjMap T.toLinearMap with
      invFun := conjMap T.symm.toLinearMap
      left_inv := fun f => by
        apply Subtype.ext
        show cj ((T.symm (toU (ofU (T (toU f)))) : π.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.symm_apply_apply]
        exact cj_cj f.1
      right_inv := fun f => by
        apply Subtype.ext
        show cj ((T (toU (ofU (T.symm (toU f)))) : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.apply_symm_apply]
        exact cj_cj f.1 }
  refine ⟨E, fun h f f' hf => ?_⟩
  show cj ((T (toU f') : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h (cj ((T (toU f) : π'.S) : Formalism.AUTREP.GAf L n → ℂ))
  have h1 : ((toU f' : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h ((toU f : π.S) : Formalism.AUTREP.GAf L n → ℂ) := by
    show cj f'.1 = Formalism.L2.NG.rt L n h (cj f.1)
    rw [hf]
    rfl
  rw [hT h _ _ h1]
  rfl

theorem not_iso_conjT {π π' : Formalism.L2.NG.FinTyp L n} (h : ¬ π.Iso π') : ¬ (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  intro hc
  apply h
  have := conjT_iso hc
  unfold Formalism.L2.NG.FinTyp.Iso at this ⊢
  rwa [conjT_S, conjT_S, conjT_S, conjT_S, conjSub_conjSub, conjSub_conjSub] at this

end ConjIso

section LinIndep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_smul_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y : C) (a : ℂ) :
    ip x (a • (y : A)) = a * ip x y := by
  have h1 := hp.herm x (a • y)
  have h2 := hp.smul a y x
  have h3 := hp.herm y x
  rw [Submodule.coe_smul] at h1
  calc ip x (a • (y : A)) = starRingEnd ℂ (starRingEnd ℂ (ip x (a • (y : A)))) := by simp
    _ = starRingEnd ℂ (ip (a • (y : A)) x) := by rw [h1]
    _ = starRingEnd ℂ (starRingEnd ℂ a * ip y x) := by rw [h2]
    _ = a * starRingEnd ℂ (ip y x) := by simp
    _ = a * ip x y := by rw [h3]

theorem linIndep_of_orth {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) {ι : Type} (x : ι → C)
    (hx : ∀ i, x i ≠ 0) (horth : ∀ i j, i ≠ j → ip (x i) (x j) = 0) : LinearIndependent ℂ x := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  have h0 := congrArg (fun z : C => ip (x j) (z : A)) hg
  simp only [Submodule.coe_zero, Submodule.coe_sum] at h0
  rw [hp_zero_right hp, hp_sum_right hp (x j) s (fun i => g i • x i)] at h0
  have hterm : ∀ i ∈ s, ip (x j) ((g i • x i : C) : A) = if i = j then g j * ip (x j) (x j) else 0 := by
    intro i _
    rw [Submodule.coe_smul, hp_smul_right hp]
    split_ifs with hij
    · rw [hij]
    · rw [horth j i (Ne.symm hij), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j, if_pos hj] at h0
  have hne : ip (x j) (x j) ≠ 0 := by
    intro h
    have := hp.pos (x j) (hx j)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact (mul_eq_zero.1 h0).resolve_right hne

end LinIndep

section Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {Y : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem finite_FTR (P : RowPsi Y n) (M : Mult.DSModel Y Sp) (J : Bool → Set (GA D Y)) (χ : Bool → GA D Y → ℂ)
    (e : Bool → (GA D Y → ℂ) →ₗ[ℂ] (GA D Y → ℂ)) (μ : Bool → Measure (GA D Y)) (𝓕 : Bool → Set (GA D Y))
    (hD : ∀ b, IsotDecomp θ P M (J b) (χ b) (e b) (μ b) (𝓕 b))
    (hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart θ M (J b) (χ b) (e b)) (Mult.ipM M (μ b) (𝓕 b))) : Finite (FTR θ P M J χ e) := by
  classical
  have hfin : ∀ b, Finite {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} := by
    intro b
    haveI := (hp b).fd
    let x : {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} → Mult.goodPart θ M (J b) (χ b) (e b) :=
      fun σ => ⟨(Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose,
        ((Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1).1⟩
    have hx0 : ∀ σ, x σ ≠ 0 := fun σ h0 =>
      (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.2 (congrArg Subtype.val h0)
    have horth : ∀ σ σ', σ ≠ σ' → Mult.ipM M (μ b) (𝓕 b) (x σ) (x σ') = 0 := by
      intro σ σ' hne
      refine (hD b).2 _ _ (not_iso_conjT fun h => hne (Subtype.ext (rowRepR_inj θ σ.1 σ'.1 h))) _
        (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1 _ (Submodule.exists_mem_ne_zero_of_ne_bot σ'.2).choose_spec.1
    exact (linIndep_of_orth (hp b) x hx0 horth).finite
  have hcover : ∀ σ : FTR θ P M J χ e, ∃ b, isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥ := fun σ => rowRepR_occ θ σ
  have : Finite ((Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥})) := by
    haveI := hfin true
    haveI := hfin false
    infer_instance
  exact Finite.of_surjective (fun p : (Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥}) =>
    p.2.1) fun σ => by
      obtain ⟨b, hb⟩ := hcover σ
      exact ⟨⟨b, σ, hb⟩, rfl⟩

end Fin

end Formalism.IndefR.principalLevelFrame
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.L2.SG.RowDict

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ)
    (f : GA D (D.sp.Y 0) → ENNReal) (hf : ∀ γ ∈ GQ (D.sp.Y 0), ∀ x, f (γ * x) = f x) :
    ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕, f y ∂μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.countable_GQ (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have hR : μ.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (D.sp.Y 0) μ hH
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have he : (e : X.B.I.GA → GA D (D.sp.Y 0)) = ι.symm := rfl
  set 𝓕' : Set (GA D (D.sp.Y 0)) := ι.symm '' X.B.fund with h𝓕'def
  have hpre : e ⁻¹' 𝓕' = X.B.fund := by
    ext x
    simp only [Set.mem_preimage, h𝓕'def, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := ι.symm.injective (by rw [hxy]; rfl)
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

  have h1 : ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕', f (y * t) ∂μ := by
    have hm : Measure.map e (muX X) = (ENNReal.ofReal c • μ).restrict 𝓕' := by
      rw [← hmap, ← he, MeasurableEquiv.restrict_map, hpre]
    rw [show (∫⁻ x, f (ι.symm x * t) ∂(muX X)) = ∫⁻ y, f (y * t) ∂(Measure.map e (muX X)) from
      (lintegral_map_equiv (fun y => f (y * t)) e).symm, hm, Measure.restrict_smul, lintegral_smul_measure]
    rfl

  have hmp : MeasurePreserving (fun y : GA D (D.sp.Y 0) => y * t) μ μ := measurePreserving_mul_right μ t
  have hemb : MeasurableEmbedding (fun y : GA D (D.sp.Y 0) => y * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  have h2 : ∫⁻ y in 𝓕', f (y * t) ∂μ = ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ :=
    hmp.setLIntegral_comp_emb hemb f 𝓕'
  have himg : (fun y : GA D (D.sp.Y 0) => y * t) '' 𝓕' = (fun y => y * t⁻¹) ⁻¹' 𝓕' := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨z * t⁻¹, hz, by simp⟩
  have hFD : IsFundamentalDomain (GQ (D.sp.Y 0)) ((fun y => y * t) '' 𝓕') μ := by
    rw [himg]
    refine h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ t⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id ?_
    intro γ y
    show (γ : GA D (D.sp.Y 0)) * y * t⁻¹ = (γ : GA D (D.sp.Y 0)) * (y * t⁻¹)
    rw [mul_assoc]
  have h3 : ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ = ∫⁻ y in 𝓕, f y ∂μ :=
    hFD.setLIntegral_eq h𝓕 f (fun γ x => hf γ γ.2 x)
  rw [h1, h2, h3]

theorem squareIntegrableTransfer_of_fundamentalDomains (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 ≤ c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ) :
    SquareIntegrableTransfer μ 𝓕 X ι t c := by
  intro F hFc hinv hF
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have hmeasG : Measurable (fun x => F (ι.symm x * t)) :=
    hFc.measurable.comp ((measurable_mul_const t).comp hιs)
  have hL := lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral μ 𝓕 X ι t c hι hιs hmap hH h𝓕 h𝓕' (fun y => ENNReal.ofReal (‖F y‖ ^ 2))
    (fun γ hγ x => by simp only [hinv γ hγ x])
  have hint : Integrable (fun y => ‖F y‖ ^ 2) (μ.restrict 𝓕) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have hfin : ∫⁻ y in 𝓕, ENNReal.ofReal (‖F y‖ ^ 2) ∂μ < ⊤ := hint.lintegral_lt_top
  have hasm : AEStronglyMeasurable (fun x => F (ι.symm x * t)) (muX X) := hmeasG.aestronglyMeasurable
  have hint2 : Integrable (fun x => ‖F (ι.symm x * t)‖ ^ 2) (muX X) := by
    refine ⟨(continuous_pow 2).comp_aestronglyMeasurable hasm.norm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity), hL]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨(memLp_two_iff_integrable_sq_norm hasm).2 hint2, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint2.aestronglyMeasurable, hL,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint.aestronglyMeasurable]

theorem fund_image_of (μ : Measure (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  obtain ⟨hmf, hcov, hdis⟩ := X.B.fund_spec
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have hset : ι.symm '' X.B.fund = ι ⁻¹' X.B.fund := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨ι y, hy, by simp⟩

  have hnull : ∀ A : Set X.B.I.GA, X.B.I.muA X.B.μf A = 0 → μ (ι ⁻¹' A) = 0 := by
    intro A hA
    have h1 : Measure.map e (X.B.I.muA X.B.μf) (ι ⁻¹' A) = X.B.I.muA X.B.μf A := by
      rw [MeasurableEquiv.map_apply]
      congr 1
      ext x
      simp [e]
    have h2 : (ENNReal.ofReal c • μ) (ι ⁻¹' A) = 0 := by
      rw [← hmap]
      exact h1.trans hA
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
    rcases h2 with h | h
    · exact absurd h (by simpa using hc)
    · exact h
  rw [hset]
  refine IsFundamentalDomain.mk'' (hι hmf).nullMeasurableSet (ae_of_all _ ?_) ?_ ?_
  · intro y
    obtain ⟨γ', hγ', hmem⟩ := hcov (ι y)
    refine ⟨⟨ι.symm γ', (hrat _).2 (by simpa using hγ')⟩, ?_⟩
    show ι (ι.symm γ' * y) ∈ X.B.fund
    simpa using hmem
  · intro γ hγ
    have hγ1 : ι γ ≠ 1 := by
      intro h
      apply hγ
      ext
      simpa using congrArg ι.symm h
    have h0 := hdis (ι γ) ((hrat γ).1 γ.2) hγ1
    refine (measure_mono_null ?_ (hnull _ h0) : μ _ = 0)
    intro y hy
    obtain ⟨⟨z, hz, rfl⟩, hy2⟩ := hy
    refine ⟨⟨ι z, hz, ?_⟩, hy2⟩
    show ι γ * ι z = ι ((γ : GA D (D.sp.Y 0)) * z)
    rw [map_mul]
  · intro γ
    exact (measurePreserving_mul_left μ (γ : GA D (D.sp.Y 0))).quasiMeasurePreserving

theorem squareIntegrableTransfer_of_rational_points (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    SquareIntegrableTransfer μ 𝓕 X ι t c :=
  squareIntegrableTransfer_of_fundamentalDomains μ 𝓕 X ι t c hι hιs hc.le hmap hH h𝓕 (fund_image_of μ X ι c hι hιs hc hmap hH hrat)

theorem measurable_of_borel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA)
    (hB : BorelSpace X.B.I.GA) :
    Measurable (ι.toMulEquiv : GA D (D.sp.Y 0) → X.B.I.GA) ∧
      Measurable (ι.toMulEquiv.symm : X.B.I.GA → GA D (D.sp.Y 0)) := by
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  exact ⟨ι.continuous.measurable, ι.symm.continuous.measurable⟩

end Formalism.IndefR.AutomorphicEvaluation

end
end
