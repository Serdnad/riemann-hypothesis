module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

namespace GlobalTheory

theorem isotropic_summand_lift : ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Type) [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R), I ^ 2 = ⊥ → IsUnit (2 : R) → (∀ x y, φ x y = -φ y x) → (∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) → ∀ F N : Submodule R D, IsCompl F N → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  intro R _ I D _ _ _ _ φ hI2 h2 hskew hsurj F N hFN hF
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := by
    intro a ha b hb
    have h : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hI2] at h; exact (Submodule.mem_bot R).1 h
  have hφI : ∀ a ∈ I • (⊤ : Submodule R D), ∀ y, φ a y ∈ I := by
    intro a ha y
    refine Submodule.smul_induction_on (p := fun a => φ a y ∈ I) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x z hx hz
      simp only [map_add (f := _), LinearMap.add_apply]
      exact I.add_mem hx hz
  have hφII : ∀ a ∈ I • (⊤ : Submodule R D), ∀ b ∈ I • (⊤ : Submodule R D), φ a b = 0 := by
    intro a ha b hb
    refine Submodule.smul_induction_on (p := fun a => φ a b = 0) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have : φ m b ∈ I := by rw [hskew]; exact I.neg_mem (hφI b hb m)
      exact hII r hr _ this
    · intro x z hx hz
      simp only [map_add (f := _), LinearMap.add_apply, hx, hz, add_zero]
  have hsmul0 : ∀ r ∈ I, ∀ w ∈ I • (⊤ : Submodule R D), r • w = 0 := by
    intro r hr w hw
    refine Submodule.smul_induction_on (p := fun w => r • w = 0) hw ?_ ?_
    · intro r' hr' m _
      rw [smul_smul, hII r hr r' hr', zero_smul]
    · intro x z hx hz
      rw [smul_add, hx, hz, add_zero]

  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R D
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ x, f (s x) = x := fun x => by simpa using LinearMap.congr_fun hs x
  let e : Fin n → D := fun i => f (fun j => if i = j then 1 else 0)
  have hexp : ∀ x, x = ∑ i, s x i • e i := fun x => by
    conv_lhs => rw [← hfs x]
    exact LinearMap.pi_apply_eq_sum_univ f (s x)
  choose z hz using fun i : Fin n => hsurj ((LinearMap.proj i).comp s)
  have hz' : ∀ i x, s x i - φ x (z i) ∈ I := fun i x => by simpa using hz i x

  let P : D →ₗ[R] D := F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hFN
  have hPF : ∀ x, P x ∈ F := fun x => (Submodule.linearProjOfIsCompl F N hFN x).2
  have hPx : ∀ x ∈ F, P x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hFN ⟨x, hx⟩)
  let B : D →ₗ[R] D →ₗ[R] R := φ.compl₁₂ P P
  have hB : ∀ x y, B x y = φ (P x) (P y) := fun x y => rfl
  have hBI : ∀ x y, B x y ∈ I := fun x y => hF _ (hPF x) _ (hPF y)
  let c : R := ↑(h2.unit⁻¹)
  have hc : c * 2 = 1 := h2.val_inv_mul
  let T : D →ₗ[R] D := ∑ i, (-c) • (LinearMap.smulRight (B (e i)) (z i))
  have hT : ∀ y, T y = ∑ i, (-c) • (B (e i) y • z i) := fun y => by
    simp [T]
  have hTr : ∀ y, T y ∈ I • (⊤ : Submodule R D) := fun y => by
    rw [hT]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.smul_mem_smul (hBI _ _) Submodule.mem_top)
  have hTI : ∀ a ∈ I • (⊤ : Submodule R D), T a = 0 := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => T a = 0) ha ?_ ?_
    · intro r hr m _
      rw [map_smul]; exact hsmul0 r hr _ (hTr m)
    · intro x w hx hw
      rw [map_add (f := _), hx, hw, add_zero]
  have hTT : ∀ y, T (T y) = 0 := fun y => hTI _ (hTr y)
  have hkey0 : ∀ x y, φ x (T y) = -c * B x y := by
    intro x y
    have hBx : B x y = ∑ i, s x i * B (e i) y := by
      conv_lhs => rw [hexp x]

      simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
    have h0 : ∑ i, B (e i) y * (s x i - φ x (z i)) = 0 :=
      Finset.sum_eq_zero fun i _ => hII _ (hBI _ _) _ (hz' i x)

    rw [hT, map_sum, hBx]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    have h1 : ∑ i, -c * (s x i * B (e i) y) - ∑ i, -c * (B (e i) y * φ x (z i)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      have : ∀ i, -c * (s x i * B (e i) y) - -c * (B (e i) y * φ x (z i))
          = -c * (B (e i) y * (s x i - φ x (z i))) := fun i => by ring
      simp only [this]
      rw [← Finset.mul_sum, h0, mul_zero]
    exact (sub_eq_zero.1 h1).symm
  have hkey : ∀ x ∈ F, ∀ y ∈ F, φ x (T y) = -c * φ x y := by
    intro x hx y hy
    rw [hkey0, hB, hPx x hx, hPx y hy]
  let u : D ≃ₗ[R] D := LinearEquiv.ofLinear (LinearMap.id + T) (LinearMap.id - T)
    (LinearMap.ext fun y => by simp [hTT]) (LinearMap.ext fun y => by simp [hTT])
  have hu : ∀ x, u x = x + T x := fun x => rfl
  refine ⟨F.map (u : D →ₗ[R] D), N.map (u : D →ₗ[R] D), ?_, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap u).isCompl hFN
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ (u x) (u y) = 0
    rw [hu, hu, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply]
    have h1 := hkey x hx y hy
    have h2' := hkey y hy x hx
    have h3 := hskew (T x) y
    have h4 := hskew y x
    have h5 := hφII (T x) (hTr x) (T y) (hTr y)
    linear_combination h1 + h3 - h2' + h5 + c * h4 - (φ x y) * hc
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨x, hx, rfl⟩
      show u x ∈ _
      rw [hu]
      exact Submodule.add_mem_sup hx (hTr x)
    · refine sup_le ?_ le_sup_right
      intro x hx
      refine Submodule.mem_sup.2 ⟨u x, ⟨x, hx, rfl⟩, -T x, Submodule.neg_mem _ (hTr x), ?_⟩
      rw [hu]; abel

end GlobalTheory
end

section

universe u

namespace GlobalTheory

theorem quotient_retract_pi_quotient :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
      [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
      (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
      ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
        r ∘ₗ s = LinearMap.id := by
  intro C _ _ I H _ _ _ _ F hIF hEx
  obtain ⟨E', M, hc, hF⟩ := hEx
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' C H
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let P : H →ₗ[C] M := Submodule.linearProjOfIsCompl M E' hc.symm
  let q : H →ₗ[C] H := M.subtype ∘ₗ P
  have hPq : ∀ x, P (q x) = P x := fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm (P x)
  have hqq : ∀ x, q (q x) = q x := fun x => congrArg Subtype.val (hPq x)
  have hqE : ∀ x ∈ E', q x = 0 := fun x hx => by
    have h0 : P x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
    show ((P x : M) : H) = 0
    rw [h0]; rfl
  have hxq : ∀ x, x - q x ∈ F := by
    intro x
    rw [← hF]
    apply Submodule.mem_sup_left
    have h0 : P (x - q x) = 0 := by rw [map_sub, hPq, sub_self]
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).1 h0
  have hσπ : ∀ x, π (σ x) = x := fun x => LinearMap.congr_fun hσ x
  let s0 : H →ₗ[C] (Fin n → C ⧸ I) :=
    (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) ∘ₗ σ ∘ₗ q
  have hs0 : F ≤ LinearMap.ker s0 := by
    rw [← hF]
    refine sup_le (fun x hx => ?_) ?_
    · rw [LinearMap.mem_ker]
      show (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) (σ (q x)) = 0
      rw [hqE x hx, map_zero, map_zero]
    · refine Submodule.smul_le.2 (fun c hcI y _ => ?_)
      rw [LinearMap.mem_ker, map_smul]
      funext k
      show c • (Submodule.mkQ I (σ (q y) k)) = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.mul_mem_right _ hcI
  let s : (H ⧸ F) →ₗ[C] (Fin n → C ⧸ I) := F.liftQ s0 hs0
  let e : Fin n → (Fin n → C) := fun k j => if k = j then 1 else 0
  have hk : ∀ k, I ≤ LinearMap.ker (LinearMap.toSpanSingleton C (H ⧸ F) (F.mkQ (q (π (e k))))) := by
    intro k c hcI
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hIF (Submodule.smul_mem_smul hcI Submodule.mem_top)
  let g : Fin n → ((C ⧸ I) →ₗ[C] (H ⧸ F)) := fun k => I.liftQ _ (hk k)
  let r : (Fin n → C ⧸ I) →ₗ[C] (H ⧸ F) := ∑ k, g k ∘ₗ LinearMap.proj k
  refine ⟨n, s, r, ?_⟩
  apply Submodule.linearMap_qext
  ext x
  have h1 : r (s (F.mkQ x)) = F.mkQ (q (π (σ (q x)))) := by

    rw [LinearMap.pi_apply_eq_sum_univ π (σ (q x)), map_sum, map_sum]
    simp only [r, s, g, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, Submodule.mkQ_apply, s0, LinearMap.pi_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.toSpanSingleton_apply, map_smul, ← Submodule.Quotient.mk_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hσπ, hqq]
  show F.mkQ (q x) = F.mkQ x
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact hxq x

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem free_of_principal_maximalIdeal_of_ker_smul_le :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      IsLocalRing.maximalIdeal R = Ideal.span {x} →
      ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N →
        (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) →
        Module.Free R N := by
  intro R _ _ _ x hx N _ _ hfin hann
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hx ▸ Ideal.subset_span rfl
  let X : IsLocalRing.maximalIdeal R := ⟨x, hxm⟩
  have hrep : ∀ t : (IsLocalRing.maximalIdeal R) ⊗[R] N, ∃ n : N, t = X ⊗ₜ n := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m n =>
      obtain ⟨r, hr⟩ : ∃ r, r * x = (m : R) := by
        have hm : (m : R) ∈ Ideal.span {x} := hx ▸ m.2
        rwa [Ideal.mem_span_singleton'] at hm
      refine ⟨r • n, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1; ext; simp [X, hr]
    | add a b ha hb =>
      obtain ⟨n1, rfl⟩ := ha; obtain ⟨n2, rfl⟩ := hb
      exact ⟨n1 + n2, by rw [TensorProduct.tmul_add]⟩
  have hspan : ∀ a ∈ Ideal.span {a : R | x * a = 0}, x * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_eq_mul, mul_left_comm, hy, mul_zero]
  have hzero : ∀ n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N),
      (X ⊗ₜ[R] n : (IsLocalRing.maximalIdeal R) ⊗[R] N) = 0 := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro a ha m _
      rw [← TensorProduct.smul_tmul]
      have : a • X = 0 := by ext; simp [X, mul_comm a x, hspan a ha]
      rw [this, TensorProduct.zero_tmul]
    · intro m1 m2 h1 h2
      rw [TensorProduct.tmul_add, h1, h2, add_zero]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, rfl⟩ := hrep t
  have hxn : x • n = 0 := by
    have h2 := congrArg (TensorProduct.lid R N) ht
    simpa [X] using h2
  exact hzero n (hann n hxn)

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.SepAverage

variable {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]

theorem exists_proj (E' M : Submodule C H) (h : IsCompl E' M) :
    ∃ σ : Module.End C H, (∀ e ∈ E', σ e = 0) ∧ ∀ u, u - σ u ∈ E' := by
  refine ⟨M.projection E' h.symm, fun e he => Submodule.projection_apply_of_mem_right h.symm he, ?_⟩
  intro u
  have := Submodule.projection_add_projection_eq_self h u
  have e : u - M.projection E' h.symm u = E'.projection M h u := by
    exact (eq_sub_of_add_eq this).symm
  rw [e]; exact Submodule.projection_apply_mem _ _

theorem map_smul_top_le (I : Ideal C) (f : Module.End C H) (P : Submodule C H)
    (hf : ∀ w, f w ∈ P) : ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • P := by
  intro w hw
  have : Submodule.map f (I • (⊤ : Submodule C H)) ≤ I • P := by
    rw [Submodule.map_smul'']
    apply Submodule.smul_mono le_rfl
    rintro _ ⟨v, -, rfl⟩; exact hf v
  exact this ⟨w, hw, rfl⟩

end GlobalTheory.SepAverage

namespace GlobalTheory.SepAverage

theorem avg_comm {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    {O : Type} [Ring O] (ρ : O →+* Module.End C H) {k : ℕ} (x y : Fin k → O)
    (hsep : ∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c))
    (g : Module.End C H) (c : O) :
    ρ c * ∑ j, ρ (x j) * g * ρ (y j) = (∑ j, ρ (x j) * g * ρ (y j)) * ρ c := by
  let B : O →ₗ[ℤ] O →ₗ[ℤ] Module.End C H :=
    LinearMap.mk₂ ℤ (fun a b => ρ a * g * ρ b)
      (by intros; simp [add_mul]) (by intros; simp only [map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add]) (by intros; simp only [map_zsmul, mul_smul_comm])
  have h := congrArg (TensorProduct.lift B) (hsep c)

  simp only [map_sum, TensorProduct.lift.tmul, B, LinearMap.mk₂_apply] at h
  calc ρ c * ∑ j, ρ (x j) * g * ρ (y j) = ∑ j, ρ (c * x j) * g * ρ (y j) := by
        simp [Finset.mul_sum, map_mul, mul_assoc]
    _ = ∑ j, ρ (x j) * g * ρ (y j * c) := h
    _ = _ := by simp [Finset.sum_mul, map_mul, mul_assoc]

theorem comm_poly {C : Type} [CommRing C] {H : Type*} [AddCommGroup H] [Module C H]
    (a p : Module.End C H) (h : a * p = p * a) :
    a * (p * p * 3 - p * p * p * 2) = (p * p * 3 - p * p * p * 2) * a := by
  have hc : Commute a p := h
  exact (((hc.mul_right hc).mul_right (Commute.ofNat_right a 3)).sub_right
    (((hc.mul_right hc).mul_right hc).mul_right (Commute.ofNat_right a 2))).eq

theorem exists_idempotent_average : ∀ (C O : Type) [CommRing C] [Ring O] (I : Ideal C), I ^ 2 = ⊥ → ∀ (N : ℤ) (k : ℕ) (x y : Fin k → O), ∑ j, x j * y j = (N : O) → (∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρ : O →+* Module.End C H) (ε : Module.End C H), ε * ε = ε → (∀ c, ρ c * ε = ε * ρ c) → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ε x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → ∃ π : Module.End C H, π * π = π ∧ (∀ c, ρ c * π = π * ρ c) ∧ π * ε = π ∧ ε * π = π ∧ (∀ z, ε z = z → z - π z ∈ F) ∧ (∀ z ∈ F, ε z = z → π z ∈ I • (⊤ : Submodule C H)) := by
  intro C O _ _ I hI N k x y hxy hsep hN H _ _ ρ ε hε hρε F hIF hρF hεF hEM
  obtain ⟨E', M, hc, hEF⟩ := hEM
  obtain ⟨σ, hσE, hσ⟩ := exists_proj E' M hc
  obtain ⟨n, hn⟩ := hN.exists_left_inv
  have hE'F : E' ≤ F := hEF ▸ le_sup_left
  have hpres : ∀ f : Module.End C H, ∀ w ∈ I • (⊤ : Submodule C H), f w ∈ I • (⊤ : Submodule C H) :=
    fun f => map_smul_top_le I f ⊤ (fun _ => trivial)
  have hερ : ∀ c v, ε (ρ c v) = ρ c (ε v) := fun c v => (LinearMap.congr_fun (hρε c) v).symm
  set q : Module.End C H := ε * σ * ε with hq
  have hεq : ε * q = q := by simp only [hq, ← mul_assoc, hε]
  have hqε : q * ε = q := by simp only [hq, mul_assoc, hε]
  set p : Module.End C H := n • ∑ j, ρ (x j) * q * ρ (y j) with hp
  have hpc : ∀ c, ρ c * p = p * ρ c := by
    intro c; rw [hp, mul_smul_comm, smul_mul_assoc, avg_comm ρ x y hsep]
  have hεp : ε * p = p := by
    rw [hp, mul_smul_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← hρε, mul_assoc (ρ (x j)) ε q, hεq]
  have hpε : p * ε = p := by
    rw [hp, smul_mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (ρ (x j) * q), hρε, ← mul_assoc, mul_assoc (ρ (x j)) q ε, hqε]
  have hsum : ∀ z, ∑ j, ρ (x j) (ρ (y j) z) = (N : C) • z := by
    intro z
    have := LinearMap.congr_fun (congrArg ρ hxy) z

    simp only [map_sum, map_mul, map_intCast, LinearMap.sum_apply, Module.End.mul_apply,
    Module.End.intCast_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hpz : ∀ z, p z = n • ∑ j, ρ (x j) (ε (σ (ε (ρ (y j) z)))) := by
    intro z
    simp [hp, hq, LinearMap.sum_apply, Module.End.mul_apply]
  have ha : ∀ z, ε z = z → z - p z ∈ F := by
    intro z hz
    have key : z - p z = n • ∑ j, ρ (x j) (ε (ρ (y j) z - σ (ρ (y j) z))) := by
      have hw : ∀ j, ε (ρ (y j) z) = ρ (y j) z := fun j => by rw [hερ, hz]
      rw [hpz]
      simp only [hw, map_sub, Finset.sum_sub_distrib, hsum, smul_sub, smul_smul, hn, one_smul]
    rw [key]
    refine F.smul_mem _ (F.sum_mem fun j _ => hρF _ _ (hεF _ (hE'F (hσ _))))
  have hb : ∀ z ∈ F, p z ∈ I • (⊤ : Submodule C H) := by
    intro z hzF
    rw [hpz]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => hpres _ _ (hpres _ _ ?_))
    have hv : ε (ρ (y j) z) ∈ F := hεF _ (hρF _ _ hzF)
    rw [← hEF] at hv
    obtain ⟨e, he, t, ht, het⟩ := Submodule.mem_sup.mp hv
    rw [← het, map_add (f := _), hσE e he, zero_add]
    exact hpres σ t ht
  set u : Module.End C H := p * p - p with hu_def
  have hu : ∀ z, u z ∈ I • (⊤ : Submodule C H) := by
    intro z
    have h1 : p z = p (ε z) := by rw [← Module.End.mul_apply, hpε]
    have h2 : ε (ε z - p (ε z)) = ε z - p (ε z) := by
      rw [map_sub, ← Module.End.mul_apply ε ε, hε, ← Module.End.mul_apply ε p, hεp]
    have h3 := hb _ (ha (ε z) (by rw [← Module.End.mul_apply, hε]))
    have e : u z = -(p (ε z - p (ε z))) := by
      simp only [hu_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub, h1]
      rw [← h1]; abel
    rw [e]; exact Submodule.neg_mem _ h3
  have huu : u * u = 0 := by
    ext z
    have h := map_smul_top_le I u (I • ⊤) hu _ (hu z)
    rw [← Submodule.mul_smul, ← pow_two, hI, Submodule.bot_smul, Submodule.mem_bot] at h
    simpa using h
  refine ⟨p * p * 3 - p * p * p * 2, ?_, fun c => comm_poly _ _ (hpc c), ?_, ?_, ?_, ?_⟩
  · have e : (p * p * 3 - p * p * p * 2) * (p * p * 3 - p * p * p * 2)
        - (p * p * 3 - p * p * p * 2) = (p * p - p) * (p * p - p) * (4 * (p * p) - 4 * p - 3) := by
      noncomm_ring
    rw [← hu_def, huu, zero_mul] at e
    exact sub_eq_zero.mp e
  · simp only [sub_mul, mul_assoc, hpε]
    simp only [← mul_assoc, Commute.ofNat_left 3 ε |>.eq, Commute.ofNat_left 2 ε |>.eq]
    simp only [mul_assoc, hpε]
  · simp only [mul_sub, ← mul_assoc, hεp]
  all_goals
    have hd : ∀ z, (p * p * 3 - p * p * p * 2) z - p z ∈ I • (⊤ : Submodule C H) := by
      intro z
      have e : p * p * 3 - p * p * p * 2 - p = -((p * p - p) * (2 * p - 1)) := by noncomm_ring
      rw [← LinearMap.sub_apply, e, LinearMap.neg_apply, ← hu_def, Module.End.mul_apply]
      exact Submodule.neg_mem _ (hu _)
  · intro z hz
    have := F.sub_mem (ha z hz) (hIF (hd z))
    convert this using 1; abel
  · intro z hzF _
    have := Submodule.add_mem _ (hb z hzF) (hd z)
    convert this using 1; abel

end GlobalTheory.SepAverage
end

section

namespace GlobalTheory.ClosingLemmaSecond

theorem main : ∀ {R : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R}, q ≠ (0 : R) → ∃ (c : ℕ), ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by
  intro R _ _ _ I q hq
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {q} : Submodule R R)
  refine ⟨k, fun n a ha => ?_⟩
  have hmem : q * a ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {q} := by
    refine Submodule.mem_inf.2 ⟨?_, Ideal.mem_span_singleton.2 ⟨a, rfl⟩⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hk (n + k) (by omega), Nat.add_sub_cancel] at hmem
  have hle : I ^ n • (I ^ k • (⊤ : Submodule R R) ⊓ Ideal.span {q}) ≤ I ^ n • Ideal.span {q} :=
    Submodule.smul_le.2 fun r hr x hx => Submodule.smul_mem_smul hr (Submodule.mem_inf.1 hx).2
  have h2 := hle hmem
  rw [Ideal.smul_eq_mul, mul_comm, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨z, hz, hzq⟩ := h2
  rwa [← mul_left_cancel₀ hq hzq]

end GlobalTheory.ClosingLemmaSecond
end
