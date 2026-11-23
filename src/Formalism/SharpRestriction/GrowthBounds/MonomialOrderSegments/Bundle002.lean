module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.FockMonomialRight
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section General

variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

theorem integral_zero' : Integral v (0 : MvPolynomial σ K) := by
  unfold Integral
  intro α
  simp

theorem integral_add' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F + G) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_add]
  exact le_trans (le_min (hF α) (hG α)) (v.map_add _ _)

theorem integral_sum' {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by
  exact Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG)
    integral_zero' h

theorem integral_smul' {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact add_nonneg ha (hF α)

theorem integral_mul' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F * G) := by
  classical
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_nonneg (hF _) (hG _)

theorem integral_monomial' (α : σ →₀ ℕ) {c : K} (hc : 0 ≤ v c) : Integral v (monomial α c) := by
  classical
  unfold Integral
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · simp

end General

section Deg

variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

theorem ldeg_mapDomain [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L') (β : L × Fin r →₀ ℕ)
    (i' : L') :
    ldeg (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) i' =
      ∑ l, if f l = i' then ldeg β l else 0 := by
  classical
  have key : ∀ a : Fin r, (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) (i', a) =
      ∑ l, if f l = i' then β (l, a) else 0 := by
    intro a
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : f l = i'
    · simp [Finsupp.single_apply, hl]
    · simp [Finsupp.single_apply, hl]
  simp only [ldeg, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

theorem HomD_prod {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by
  classical
  have hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i := by
    intro β γ i
    simp [ldeg, Finset.sum_add_distrib]
  have hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G →
      HomD (fun i => d₁ i + d₂ i) (F * G) := by
    intro d₁ d₂ F G hF hG β hβ i
    obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)
    rw [hadd, hF β₁ h₁ i, hG β₂ h₂ i]
  induction s using Finset.induction_on with
  | empty =>
    intro β hβ i
    simp only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ
    subst hβ
    simp [ldeg]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i := by
      funext i
      rw [Finset.sum_insert ha]
    rw [e]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem HomD_rename [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L')
    (hf : Function.Injective f) (d : L → ℕ) (G : MvPolynomial (L × Fin r) K) (hG : HomD d G) :
    HomD (fun i' => ∑ l, if f l = i' then d l else 0) (rename (Prod.map f (id : Fin r → Fin r)) G) := by
  classical
  intro β hβ i'
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ hac
    simp only [Prod.map, id, Prod.mk.injEq] at hac
    exact Prod.ext (hf hac.1) hac.2
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hβ
  obtain ⟨β₀, h₀, rfl⟩ := hβ
  rw [ldeg_mapDomain]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hG β₀ h₀ l]

theorem valS_prod_le [DecidableEq L] (sg : L → Bool) (S : Finset L) {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (L × Fin r) K) :
    ∑ k ∈ s, valS sg S (f k) ≤ valS sg S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    simp [valS, lord, MvPolynomial.support_one]
    intro b hb a ha
    rw [MvPolynomial.coeff_one] at hb ha
    split_ifs at hb ha with hb0
    · rw [AddMonoidAlgebra.one_def] at ha
      unfold AddMonoidAlgebra.single at ha
      simp at ha
      rw [Finsupp.single_apply] at ha
      split_ifs at ha with ha0
      · subst ha0
        simp
      · exact absurd rfl ha
    · exact absurd rfl hb
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add le_rfl ih).trans (by apply valS_mul_le)

end Deg

end Formalism.MainNotions.PlaneGram
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

section Generic

variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)

theorem fock_proj_right {W : Set (MvPolynomial (L × Fin r) K)}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d W π) {A G : MvPolynomial (L × Fin r) K}
    (hA : A ∈ PolK K r d) (hAW : A ∈ W) (hG : G ∈ PolK K r d) : fock A (π G) = fock A G := by
  have h := (hπ G hG).2.2.2 A hA hAW
  rw [fock_sub_left] at h
  rw [fock_comm A (π G), fock_comm A G]
  exact (sub_eq_zero.mp h).symm

theorem proj_preserves (hP : PROJ K v p C0) (hD : DVRHyp v p) {S S'' : Finset L} {th th'' : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π)
    (hS : S ⊆ S'' ∨ S'' ⊆ S ∨ Disjoint S S'') {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) (hFW : F ∈ Aset sg S'' th'') : π F ∈ Aset sg S'' th'' := by
  obtain ⟨⟨π'', hπ''⟩, -⟩ := hP hD L sg r d S'' th''
  have hfix : π'' F = F := (hπ'' F hF).2.2.1 hFW
  have hcomm : π (π'' F) = π'' (π F) := by
    rcases hS with h | h | h
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF
    · exact (((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF
  have hE : π F = π'' (π F) := by rw [← hcomm, hfix]
  rw [hE]
  exact (hπ'' (π F) (hπ F hF).1).2.1

theorem bge_proj (hP : PROJ K v p C0) (hD : DVRHyp v p) {S : Finset L} {th : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π) {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) {a : ℝ} (ha : bge v a F) :
    bge v (a - (r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i)) (π F) := by
  rw [bge_iff] at ha ⊢
  have hb := ((hP hD L sg r d S th).2 π hπ).2.2 F hF
  have h2 := ha.trans hb
  generalize vBB v (π F) = x at h2 ⊢
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

theorem prodProj (hP : PROJ K v p C0) (hD : DVRHyp v p) {ι : Type} (s : Finset ι)
    (S : ι → Finset L) (th : ι → ℤ)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, S x ⊆ S y ∨ S y ⊆ S x ∨ Disjoint (S x) (S y)) :
    ∃ Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K,
      (∀ F ∈ PolK K r d, Pr F ∈ PolK K r d) ∧
      (∀ F ∈ PolK K r d, ∀ x ∈ s, Pr F ∈ Aset sg (S x) (th x)) ∧
      (∀ A ∈ PolK K r d, (∀ x ∈ s, A ∈ Aset sg (S x) (th x)) →
        ∀ G ∈ PolK K r d, fock A (Pr G) = fock A G) ∧
      (∀ F ∈ PolK K r d, ∀ a : ℝ, bge v a F →
        bge v (a - s.card * ((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i))) (Pr F)) ∧
      (∀ (S'' : Finset L) (th'' : ℤ), (∀ x ∈ s, S x ⊆ S'' ∨ Disjoint (S x) S'') →
        ∀ F ∈ PolK K r d, F ∈ Aset sg S'' th'' → Pr F ∈ Aset sg S'' th'') ∧
      (∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_,
      fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩
    intro F _ a ha
    simpa using ha
  | @insert x s hx ih =>
    have hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z) :=
      fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    obtain ⟨Pr, h1, h2, h3, h4, h5, h6⟩ := ih hpair'
    obtain ⟨⟨πx, hπx⟩, -⟩ := hP hD L sg r d (S x) (th x)
    have hPx := (hP hD L sg r d (S x) (th x)).2 πx hπx
    refine ⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F hF
      exact (hπx _ (h1 F hF)).1
    · intro F hF y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hπx _ (h1 F hF)).2.1
      · exact proj_preserves sg d hP hD hπx
          (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)
    · intro A hA hAW G hG
      rw [LinearMap.comp_apply,
        fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]
      exact h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG
    · intro F hF a ha
      have hb := bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)
      rw [LinearMap.comp_apply]
      refine bge_mono v ?_ hb
      rw [Finset.card_insert_eq_ite, if_neg hx]
      apply le_of_eq
      push_cast
      ring
    · intro S'' th'' hS F hF hFW
      have hPr := h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW
      rw [LinearMap.comp_apply]
      rcases hS x (Finset.mem_insert_self x s) with h | h
      · exact proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr
      · exact proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr
    · intro i hi hout a F hF
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]
      exact hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)

end Generic

section Torus

variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

theorem euler_eq_dg {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)
  · rw [MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]
  · rw [map_add (f := _), mul_add, hP, hQ, map_add (f := _)]

private theorem monomial_mem_PolK_of_degrees (d : L → ℕ) (ζ : L × Fin r →₀ ℕ)
    (hζ : ∀ i, ldeg ζ i = d i) : monomial ζ (1 : K) ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro α hα
  rwa [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hα)]

theorem proj_keeps_letter (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono := monomial_mem_PolK_of_degrees (K := K) d ζ hζ
  have h := hcomm a _ hmono
  rw [euler_eq_dg, euler_eq_dg] at h
  simp only [dg_monomial, mul_one] at h
  have h' := congrArg (fun G => AddMonoidAlgebra.coeff G ζ') h
  simp only [coeff_dg] at h'
  have hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) =
      ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h'
  have hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0 := by simpa using hζ'
  have hc := mul_right_cancel₀ hne h'
  exact_mod_cast hc.symm

end Torus

theorem prodProj_entries {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r]
    (d : L → ℕ) {ι : Type} (s : Finset ι) (S : ι → Finset L)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (h1 : ∀ F ∈ PolK K r d, Pr F ∈ PolK K r d)
    (h6 : ∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) :
    (∀ k, ldeg ζ' k = d k) ∧
      ∀ i, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ a, ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono := monomial_mem_PolK_of_degrees (K := K) d ζ hζ
  exact ⟨fun k => (mem_PolK_iff d _).mp (h1 _ hmono) ζ' hζ' k,
    fun i hi hout a => proj_keeps_letter d Pr i (h6 i hi hout) ζ hζ ζ' hζ' a⟩

end Formalism.MainNotions.PlaneGram
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def varE (p : ℕ) (x : D.ML × Fin D.r) : D.EA :=
  Sum.elim (fun b => Finsupp.single (Sum.inl b, x.2) 1)
    (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) 1)
      (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) (D.P p t))
        (fun t => Finsupp.single (Sum.inr t, x.2) 1))) x.1

theorem ph_X (p : ℕ) (x : D.ML × Fin D.r) :
    D.ph p (X x : MvPolynomial (D.ML × Fin D.r) K) = monomial (D.varE p x) 1 := by
  obtain ⟨i, a⟩ := x
  unfold ph
  rw [aeval_X]
  rcases i with b | t | t | t <;> simp [varE, X, monomial_pow]

theorem phE_apply_inl (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.phE p ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_apply_inr (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.phE p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) + ζ (D.mtp t, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_eq_sum (p : ℕ) (ζ : D.EM) : D.phE p ζ = ζ.sum fun x k => k • D.varE p x := by
  classical
  ext ⟨i, a⟩
  rw [Finsupp.sum_fintype _ _ (by intro x; simp), Finsupp.finsetSum_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases i with b | t
  · rw [phE_apply_inl]
    simp [varE, Finsupp.single_apply, mb, ite_and]
  · rw [phE_apply_inr]
    simp only [varE, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, if_false, Finset.sum_const_zero, zero_add,
      ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero, mlab, mw, mtp]
    have key : ∀ f : D.Tau → Fin D.r → ℕ,
        (∑ x, ∑ y, if x = t then (if y = a then f x y else 0) else 0) = f t a := by
      intro f
      rw [Finset.sum_eq_single t (by intro x _ hx; simp [hx]) (by simp)]
      simp
    rw [key, key, key]
    ring

theorem ph_monomial (p : ℕ) (ζ : D.EM) (c : K) :
    D.ph p (monomial ζ c) = monomial (D.phE p ζ) c := by
  classical
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, phE_eq_sum]
  simp only [map_pow, ph_X, monomial_pow, one_pow]
  rw [show D.ph p (C c) = C c from (D.ph p).commutes c]
  rw [Finsupp.sum, ← monomial_sum_one, C_mul_monomial, mul_one]

theorem ldeg_phE (p : ℕ) (ζ : D.EM) (h : D.GoodE p ζ) (i : D.OL) : ldeg (D.phE p ζ) i = D.dO i := by
  obtain ⟨-, -, h3, h4, -⟩ := h
  rcases i with b | t
  · simp only [ldeg, phE_apply_inl, dO, Sum.elim_inl]
    exact h3 b
  · simp only [ldeg, phE_apply_inr, dO, Sum.elim_inr, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact h4 t

theorem Good.add {p : ℕ} {Z W : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (hW : D.Good p W) :
    D.Good p (Z + W) := by
  classical
  intro ζ hζ
  rcases Finset.mem_union.mp (support_add hζ) with h | h
  · exact hZ ζ h
  · exact hW ζ h

theorem Good.smul {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (a : K) :
    D.Good p (a • Z) := fun ζ hζ => hZ ζ (support_smul hζ)

theorem Good.zero (p : ℕ) : D.Good p (0 : MvPolynomial (D.ML × Fin D.r) K) := by
  intro ζ hζ; simp at hζ

theorem Good.sum {p : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (D.ML × Fin D.r) K)
    (h : ∀ i ∈ s, D.Good p (f i)) : D.Good p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero D p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Good.add D (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Good.monomial {p : ℕ} {ζ : D.EM} (h : D.GoodE p ζ) (c : K) : D.Good p (monomial ζ c) := by
  classical
  intro ζ' hζ'
  have := support_monomial_subset hζ'
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

end TwistData

end Formalism.MainNotions.PlaneGram
end
end
