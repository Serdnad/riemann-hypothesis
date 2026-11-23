module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevForget

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def forgetMap {b : Base D R} {N' : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'}
    {o : Obj b N' s} {f : S' ⟶ S} (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) :
    ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

end GlobalTheory.UPel.HT.EtLev.LevForget
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BaseChg

theorem beta_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀)
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens),
    Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) U.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.1)))
      (CommRingCat.ofHom (algebraMap R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)))) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R₀)) (Scheme.ΓSpecIso (CommRingCat.of R₁))
      (Iso.refl (CommRingCat.of (Sec s₀ U.1))) (Iso.refl (CommRingCat.of (Sec s₁ (pr ⁻¹ᵁ U.1)))) ?_ ?_ ?_ ?_
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · ext r
      change (s₀.appLE ⊤ U.1 le_top).hom r = (s₀.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom r))
      congr 1
      simp
    · ext r
      change (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) _).hom r = (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom r))
      congr 1
      simp
    · rfl
  have h1 := CommRingCat.isPushout_tensorProduct R₀ R₁ (Sec s₀ U.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (beta hp U) := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext r
      change algebraMap R₁ _ r = beta hp U (r ⊗ₜ 1)
      rw [beta_tmul, map_one, _root_.mul_one]
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext b
      change (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl).hom b = beta hp U (1 ⊗ₜ b)
      refine Eq.trans ?_ (beta_tmul hp U 1 b).symm
      rw [map_one, _root_.one_mul]
      rfl
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory.Obs.BaseChg
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma lam_idx_sq_eq_idx_of_fixed_ne_zero (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (lam : ℕ →* ℂ) (hlam : _root_.GlobalTheory.FinWeil.GoodNorm σ lam) {A A' : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (hA' : _root_.GlobalTheory.FinWeil.SelfDual γ A')
    (hidx : _root_.GlobalTheory.FinWeil.idx A A' ≠ 0) {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he0 : e ≠ 0) :
    lam (_root_.GlobalTheory.FinWeil.idx A A') ^ 2 = _root_.GlobalTheory.FinWeil.idx A A' := by
  have hAA := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A)
    (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)
  have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx
    (by rw [hAA.2]; simp) e he
  obtain ⟨hsym, hback⟩ := _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx
  have hlin : ∀ (c : ℂ) (v : M),
      _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v := by
    intro c v
    unfold _root_.GlobalTheory.FinWeil.sumOp
    simp only [map_smul]
    rw [smul_finsum]
  unfold _root_.GlobalTheory.FinWeil.normOp at hcomp
  rw [hAA.1, hAA.2, hsym, hlin, hback e he] at hcomp
  simp only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton, hW.zero, smul_smul] at hcomp
  have hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0 := hlam.1 _ hidx
  have hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ *
      (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_assoc, hcomp, sub_self]
  have h1 := (smul_eq_zero.1 hz).resolve_right he0
  field_simp at h1
  linear_combination -h1

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma mul_conj_eq_natCast_of_sq_eq (c : ℂ) (n : ℕ) (h : c ^ 2 = n) :
    c * starRingEnd ℂ c = n := by
  have hn : ‖c‖ ^ 2 = n := by rw [← norm_pow, h, Complex.norm_natCast]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  push_cast
  rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_vacuum_eq_zero
    (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x u v, B (W x u) (W x v) = B u v) {e e' : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he' : _root_.GlobalTheory.FinWeil.Fixes W A e') {z : X} (hz : z ∉ A) : B (W z e) e' = 0 := by
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hz ((hA z).2 h)
  have haz : γ a z ≠ 1 := fun h => hza (hW.swap_eq_one h)
  have key := hB a (W z e) e'
  rw [hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  have : (γ a z - 1) * B (W z e) e' = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_pair_eq (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hB : ∀ x u v, B (W x u) (W x v) = B u v) (x y : X) (e e' : M) :
    B (W x e) (W y e') = γ (w • -y) x * (starRingEnd ℂ) (γ (w • -y) y) * B (W (-y + x) e) e' := by
  rw [← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]
  simp
  ring

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForms_eq_of_eq_on_vacua (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤)
    (B₁ B₂ : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (h₁ : ∀ x u v, B₁ (W x u) (W x v) = B₁ u v)
    (h₂ : ∀ x u v, B₂ (W x u) (W x v) = B₂ u v)
    (hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ e e' = B₂ e e')
    (u v : M) : B₁ u v = B₂ u v := by
  have htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ (W z e) e' = B₂ (W z e) e' := by
    intro z e e' he he'
    by_cases hz : z ∈ A
    · rw [he z hz]
      exact hvac e e' he he'
    · rw [invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz,
        invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]
  have hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e},
      ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t := by
    rintro s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩
    rw [invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂,
      htr _ e e' he he']
  have hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s :=
    fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)
  have hflip : B₁.flip v = B₂.flip v :=
    LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])
  simpa using LinearMap.congr_fun hflip u


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.invForm_intertwiner : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam →
    ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → _root_.GlobalTheory.FinWeil.SelfDual γ (A.map φ) →
    _root_.GlobalTheory.FinWeil.idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) →
    (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map φ) e) →
    ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) →
    ∀ u v, B (T u) (T v) = B u v := by
  intro R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v
  obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx
  have hsum := fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu
  have hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B (T e) (T e') = B e e' := by
    intro e e' he he'
    by_cases he0 : e = 0
    · subst he0
      simp
    have hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n := by simpa using (hsum e he).2
    have hc2 := lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0
    rw [hn] at hc2
    have hcn := mul_conj_eq_natCast_of_sq_eq _ _ hc2
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hn ▸ hidx)
    have hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e := by
      intro e he
      rw [hTe e he]
      unfold _root_.GlobalTheory.FinWeil.normOp
      rw [hn, (hsum e he).1]
    have hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0 := by
      intro i j
      rw [← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i),
        hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel,
        hW.zero]
      split_ifs with hij
      · subst hij
        rw [neg_add_cancel, hW.zero]
      · apply invariantForm_translate_vacuum_eq_zero hW hA B hB he he'
        intro hmem
        apply hij
        obtain ⟨k, -, hk⟩ := hfu (f i) (hfB i)
        rw [hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]
    rw [hT' e he, hT' e' he']

    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply,
    smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]
    have hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1 := by
      rw [← mul_inv, hcn, inv_mul_cancel₀ hn0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination B e e' * hinv
  have key := invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B
    (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v
  simpa using key

end GlobalTheory.FinWeil
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.SUVol

theorem conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  intro E _ _ _ r X x σ hx hσ0 hσc η hη
  classical
  let One : X.Ψ → Fin r → Fin r → ℂ := fun _ a b => (1 : Matrix (Fin r) (Fin r) ℂ) a b
  let F : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) → (X.Ψ → Fin r → Fin r → ℂ) :=
    fun PQ τ => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
  have hFc : Continuous F := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.1 τ) :=
      (continuous_apply τ).comp continuous_fst
    have h2 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.2 τ) :=
      (continuous_apply τ).comp continuous_snd
    show Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
      (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
    exact (continuous_const.matrix_mul (h1.matrix_mul h2)).matrix_mul continuous_const
  have hF1 : F (One, One) = One := by
    funext τ
    have hu : IsUnit (mat x τ).det :=
      isUnit_iff_ne_zero.mpr (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ)
    have h1 : Matrix.of (One τ) = 1 := rfl
    show (mat x τ)⁻¹ * (Matrix.of (One τ) * Matrix.of (One τ)) * mat x τ = Matrix.of (One τ)
    rw [h1, Matrix.mul_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc.continuousAt (ε := η) hη
  rw [hF1] at hδF
  let A : V (nd X) → (X.Ψ → Fin r → Fin r → ℂ) := fun z τ =>
    ((((σ z)⁻¹ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hAc : ContinuousAt A 0 := by
    refine continuousAt_pi.2 fun τ => ?_
    have : ContinuousAt (fun z => (σ z)⁻¹) 0 := ContinuousAt.comp (f := σ) continuous_inv.continuousAt hσc
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).continuousAt.comp this
  have hA0 : A 0 = One := by
    funext τ
    simp only [A, One, hσ0, inv_one]
    rfl
  obtain ⟨κ, hκ, hκA⟩ := Metric.continuousAt_iff.1 hAc (ε := δ) hδ
  rw [hA0] at hκA
  refine ⟨δ, hδ, κ, hκ, fun z hz g hg τ a b => ?_⟩
  let B : X.Ψ → Fin r → Fin r → ℂ := fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hzA : dist (A z) One < δ := hκA (by simpa [dist_zero_right] using hz)
  have hgB : dist B One < δ := by
    refine (dist_pi_lt_iff hδ).2 fun τ => (dist_pi_lt_iff hδ).2 fun a => (dist_pi_lt_iff hδ).2 fun b => ?_
    rw [dist_eq_norm]
    exact hg τ a b
  have hPQ : dist (A z, B) (One, One) < δ := by
    rw [Prod.dist_eq]; exact max_lt hzA hgB
  have hout := hδF hPQ
  have hent : dist (F (A z, B) τ a b) (One τ a b) < η :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ b).trans ((dist_le_pi_dist _ _ a).trans (dist_le_pi_dist _ _ τ))) hout
  rw [dist_eq_norm] at hent
  convert hent using 3
  all_goals rfl

end GlobalTheory.SUVol
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.LieOfAdditive

theorem existsUnique_lie_of_additive : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (b : ∀ n, G.A n), (∀ n, ∃ z, cobOne O (G.A n) (b n) = (p : O) ^ n • z) → (∀ n, ∃ z, b (n + 1) = G.mulP n (b n) + (p : O) ^ n • z) → ∃! l : G.dual.Lie, ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ (b n) := by
  intro p O _ _ G b hb hc
  have hu : ∀ n, ∃ u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n},
      ∀ φ : CartierDual O (G.A n), u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ (b n)) := fun n => by
    obtain ⟨z, hz⟩ := hb n
    exact GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul O (G.A n) ((p : O) ^ n) (b n) z hz
  choose u hu using hu
  let U : ∀ n : ℕ, G.dual.omega →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n} := fun n =>
    (u n).comp ((LinearMap.proj n).comp G.dual.omegaSub.subtype)
  have hU : ∀ n (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n →
      U n w = Ideal.Quotient.mk _ (φ (b n)) := by
    intro n w φ h
    show u n (w.1 n) = _
    rw [← h, hu]
  have key : ∀ n (w : G.dual.omega) (x : O), U (n + 1) w = Ideal.Quotient.mk _ x →
      U n w = Ideal.Quotient.mk _ x := by
    intro n w x hx
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 (n + 1))
    have h1 : dUnit (R := O) (CartierDual.map (G.mulP n) φ) = w.1 n := by
      rw [← w.2 n, ← hφ]; exact (cotMap_d _ _).symm
    rw [hU n w _ h1, CartierDual.map_apply]
    rw [hU (n + 1) w φ hφ] at hx
    obtain ⟨z, hz⟩ := hc n
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hx ⊢
    rw [hz, map_add (f := _), map_smul, smul_eq_mul] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(p : O) * k - φ z, by linear_combination hk⟩
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.T.existsUnique_dual_of_compatible_mod_pow_of_adicComplete O G.dual.omega (p : O) U key
  refine ⟨l, fun n w φ h => ?_, fun l' hl' => huniq l' fun n w => ?_⟩
  · have := (hl n w).trans (hU n w φ h)
    rwa [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  · obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
    rw [hU n w φ hφ, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hl' n w φ hφ

end GlobalTheory.LieOfAdditive
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → ∀ b : H, cobOne K H b = 0 → dUnit (R := K) b = 0 → b = 0 := by
  first | exact @GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | exact GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | (intros; apply GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add (f := _), map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
end
