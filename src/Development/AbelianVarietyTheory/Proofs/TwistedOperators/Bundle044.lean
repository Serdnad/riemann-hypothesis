module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Fourier.FourierTransform
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (U h).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) h.continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 volume + b • (U g).toLp 2 volume‖ = ‖f.toLp 2 volume + b • g.toLp 2 volume‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add (f := _), hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

end GlobalTheory.RealWeil.SchurSchwartz

end
end

section

open Formalism.REAL Finset

namespace GlobalTheory.CapelliDiff

theorem prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by
  intro n
  induction n with
  | zero =>
    intro x y d h
    simp [h 0]
  | succ n ih =>
    intro x y d h
    rw [List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    have key := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)
    have e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod
        = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.succ).prod) := by
      rw [h 0]; noncomm_ring
    rw [e1, key, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [List.ofFn_succ, List.prod_cons]
      have h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ := by simp [Fin.succ_pos]
      rw [if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]
      have hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) =
          (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ) := by
        congr 1; funext j; simp only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      rw [hl]

theorem Tm_add_one {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add (f := _)]; abel

def extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv k).permCongr τ)

theorem extAt_succAbove {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]

theorem sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

theorem sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by
  let e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a} :=
    ((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]
  · rw [← Equiv.sum_comp e]
    rfl
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h a ha; rw [ha]; exact h
    · intro h; exact h k rfl

theorem qdet_add_one_sub (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ) :
    qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  unfold qdet qminor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have step : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod -
        (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod := by
    intro σ
    rw [prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
      (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]
    · apply Finset.sum_congr rfl
      intro k _
      congr 2
      congr 1
      funext j
      by_cases hj : Fin.castSucc j < k
      · rw [if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]
        simp [Fin.coe_castSucc]
      · rw [if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]
        simp only [id, Fin.val_succ]
        congr 1
        push_cast; ring
    · intro k
      have : u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1 := by ring
      simp only [this, Tm_add_one, id]
  simp_rw [step, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) =
      if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod else 0 := by
    intro σ
    split_ifs <;> simp
  simp_rw [h2]
  rw [sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [sign_extAt, extAt_succAbove]

end GlobalTheory.CapelliDiff

theorem GlobalTheory.qdet_add_one_sub_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
end

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompactQuotientFourier

theorem setIntegral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem inversion_at_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum
  classical
  haveI := hμ
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hχ0 : ∀ x, χ 0 x = 1 := fun x => by
    have h2 : χ 0 x * χ 0 x = χ 0 x * 1 := by rw [mul_one, ← ha, add_zero]
    exact mul_left_cancel₀ (hne 0 x) h2
  have hχx0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one, ← hx, add_zero]
    exact mul_left_cancel₀ (hne a 0) h2
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := fun a x => by
    have h1' : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, hχ0]
    have h2 : star (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
    exact mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0 := by
    intro a b
    have he : ∀ x, χ b x * star (χ a x) = χ (b - a) x := fun x => by rw [hstar, ← ha, sub_eq_add_neg]
    simp_rw [he]
    split_ifs with hab
    · subst hab
      simp [hχ0, hvol]
    · have hc' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by
        by_contra h
        push_neg at h
        exact hc' (hinj _ h)
      have key := setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀
      simp_rw [hx _ _ x₀] at key
      rw [integral_mul_const] at key
      have h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0 := by
        rw [mul_sub, key, mul_one, sub_self]
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ hk
  have hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖ := fun a x => by
    rw [norm_mul, norm_star, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * star (χ a x)
  have hScont : Continuous S :=
    continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    have hs : Summable (fun a => ‖c a * star (χ a x)‖) := by simp_rw [hterm]; exact hsum
    calc ‖S x‖ ≤ ∑' a, ‖c a * star (χ a x)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' a, ‖c a‖ := by simp_rw [hterm]
  have hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := by
    intro b
    have e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x)) := fun x => tsum_mul_left.symm
    have hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖ := fun a x => by
      rw [norm_mul, hn, one_mul, hterm]
    have hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕) := fun a =>
      hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le
    have hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ := by
      simp_rw [hnorm]
      simpa [hvol] using hsum
    have e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0) := fun a => by
      rw [← horth, ← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [e]
    rw [← integral_tsum_of_summable_integral_norm hFi hFs]
    simp_rw [e2, mul_ite, mul_one, mul_zero]
    simp
  have hdiff := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker
    μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ])
    (fun a => by
      simp only [Pi.sub_apply, mul_sub]
      have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x
      have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
      rw [integral_sub i1 i2, hcS, sub_self])
  have h0 := congrFun hdiff 0
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  simp only [S, hχx0, star_one, mul_one]

end GlobalTheory.CompactQuotientFourier
end
