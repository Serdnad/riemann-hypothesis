module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SeqColim

theorem map_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, x => rfl
  | k + 1, x => by
      show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
      rw [h.comm, map_tr f ι h n k x]

theorem pf_of_stages (p : ℕ) {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (hG : ∀ n, Pf p (G n)) : Pf p L := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ι 0) (hG 0).char
    simpa using this
  · intro x y hxy
    obtain ⟨n, z, hz⟩ := h.surj 2 ![x, y]
    have h0 : ι n (z 0 ^ p - z 1 ^ p) = 0 := by
      have e0 := hz 0
      have e1 := hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      simp [map_sub, map_pow, e0, e1, hxy]
    obtain ⟨k, hk⟩ := h.ker n 1 (fun _ => z 0 ^ p - z 1 ^ p) (fun _ => h0)
    have hk0 := hk 0
    simp only [map_sub, map_pow, sub_eq_zero] at hk0
    have heq := (hG (n + k)).bij.1 hk0
    have e0 := hz 0
    have e1 := hz 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have := congrArg (ι (n + k)) heq
    rw [map_tr f ι h, map_tr f ι h, e0, e1] at this
    exact this
  · intro x
    obtain ⟨n, z, hz⟩ := h.surj 1 (fun _ => x)
    obtain ⟨w, hw⟩ := (hG n).bij.2 (z 0)
    refine ⟨ι n w, ?_⟩
    simp only at hw ⊢
    rw [← map_pow, hw, hz 0]

theorem solv_at_stage {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A) (hs : Solv L a c) :
    ∃ N, Solv (G N) a c := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨N₀, z, hz⟩ := h.surj n y
  have hd : ∀ i, ι N₀ ((∑ j, a i j • z j) - algebraMap A (G N₀) (c i)) = 0 := by
    intro i

    simp only [map_sub, map_sum, map_smul, AlgHom.commutes, hz, hy i, sub_self]
  obtain ⟨k, hk⟩ := h.ker N₀ m _ hd
  refine ⟨N₀ + k, fun j => tr f N₀ k (z j), fun i => ?_⟩
  have := hk i

  simp only [map_sub, map_sum, map_smul, AlgHom.commutes, sub_eq_zero] at this
  exact this

end GlobalTheory.CompanionTheory.SeqColim

namespace GlobalTheory.CompanionTheory

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := by
  intro p _ A _ G _ _ f L _ _ ι h
  exact ⟨SeqColim.pf_of_stages p f ι h, fun m n a c hs => SeqColim.solv_at_stage f ι h m n a c hs⟩

end GlobalTheory.CompanionTheory
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem smul_smul_mem_range {A B D K₁ K₀ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup D] [Module A D] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (ρ : B →ₗ[A] D) (hρ : Function.Surjective ρ) (h1 : ρ 1 = 0) (d : K₁ →ₗ[A] K₀) (s : A)
    (hGood : ∀ x : D ⊗[A] K₁, d.lTensor D x = 0 →
      ∃ v : D ⊗[A] LinearMap.ker d, (LinearMap.ker d).subtype.lTensor D v = s • x)
    (hK₁ : ∀ w : B ⊗[A] K₁, ρ.rTensor K₁ w = 0 → ∃ a : K₁, w = (1 : B) ⊗ₜ[A] a)
    (hK₀ : ∀ a : K₀, (1 : B) ⊗ₜ[A] a = 0 → s • a = 0)
    (z : K₀) (w : B ⊗[A] K₁) (hw : (1 : B) ⊗ₜ[A] z = d.lTensor B w) :
    s • s • z ∈ LinearMap.range d := by
  have comm₁ : ∀ t : B ⊗[A] K₁, d.lTensor D (ρ.rTensor K₁ t) = ρ.rTensor K₀ (d.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₂ : ∀ t : B ⊗[A] LinearMap.ker d,
      (LinearMap.ker d).subtype.lTensor D (ρ.rTensor _ t)
        = ρ.rTensor K₁ ((LinearMap.ker d).subtype.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have dker : ∀ t : B ⊗[A] LinearMap.ker d,
      d.lTensor B ((LinearMap.ker d).subtype.lTensor B t) = 0 := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  have hw' : d.lTensor D (ρ.rTensor K₁ w) = 0 := by
    rw [comm₁, ← hw]; simp [h1]
  obtain ⟨v', hv'⟩ := hGood _ hw'
  obtain ⟨v, rfl⟩ := LinearMap.rTensor_surjective (LinearMap.ker d) hρ v'
  obtain ⟨u, hu⟩ := hK₁ (s • w - (LinearMap.ker d).subtype.lTensor B v) (by
    rw [map_sub, map_smul, ← comm₂, hv', sub_self])
  have key : (1 : B) ⊗ₜ[A] (d u - s • z) = 0 := by
    have := congrArg (d.lTensor B) hu
    rw [map_sub, map_smul, dker, sub_zero, ← hw, LinearMap.lTensor_tmul] at this
    rw [TensorProduct.tmul_sub, ← this, TensorProduct.tmul_smul, sub_self]
  have h := hK₀ _ key
  refine ⟨s • u, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at h
  exact h

theorem pow_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    {p : ℕ} (hp : 2 ≤ p) (s : A) (z : M) (h : s • s • z ∈ N) : s ^ p • z ∈ N := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have : s ^ (2 + q) • z = s ^ q • s • s • z := by
    simp only [smul_smul]; congr 1; ring
  rw [this]
  exact N.smul_mem _ h

theorem mv_cov : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ : B →ₗ[A] D), IsRt p r → Pf p D → Function.Surjective ρ → ρ 1 = 0 → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ w : B ⊗[A] K, ρ.rTensor K w = 0 → ∃ a : K, w = (1 : B) ⊗ₜ[A] a) → Cov p r B := by
  intro p _ A _ B _ _ D _ _ r ρ hr hD hρ h1 hK K₁ K₀ _ _ _ _ hp₁ hp₀ d hG z hz k
  obtain ⟨w, hw⟩ := hz
  have hmem : r (k + 1) • r (k + 1) • z ∈ LinearMap.range d :=
    smul_smul_mem_range ρ hρ h1 d (r (k + 1))
      (fun x hx => by
        obtain ⟨v, hv⟩ := hG D hD x hx (k + 1)
        exact ⟨v, hv⟩)
      (hK K₁ hp₁).2
      (fun a ha => (hK K₀ hp₀).1 a ha (k + 1))
      z w hw.symm
  rw [← hr k]
  exact pow_smul_mem _ (Fact.out : p.Prime).two_le _ _ hmem

end GlobalTheory.CompanionTheory.SnakeCov
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovMono

theorem cov_self (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A) : Cov p r A := by
  intro K₁ K₀ _ _ _ _ _ _ d _ z hz k
  obtain ⟨w, hw⟩ := hz
  have key : z = d (TensorProduct.lid A K₁ w) := by
    have h1 : TensorProduct.lid A K₀ (d.lTensor A w) = d (TensorProduct.lid A K₁ w) := by
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [hw] at h1
    simpa using h1
  rw [key, ← map_smul]
  exact ⟨_, rfl⟩

theorem cov_of_algHom (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A)
    (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁]
    (φ : B →ₐ[A] B₁) (h : Cov p r B₁) : Cov p r B := by
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  obtain ⟨w, hw⟩ := hz
  refine h K₁ K₀ hK₁ hK₀ d hd z ⟨φ.toLinearMap.rTensor K₁ w, ?_⟩ k
  have h1 : φ.toLinearMap.rTensor K₀ (d.lTensor B w) = d.lTensor B₁ (φ.toLinearMap.rTensor K₁ w) := by
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [← h1, hw]
  simp

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := by
  intro p _ A _ r
  exact ⟨cov_self p A r, fun B _ _ B₁ _ _ φ h => cov_of_algHom p A r B B₁ φ h⟩

end GlobalTheory.CompanionTheory.CovMono
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.GoodBaseChange

theorem good_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A) (K₁ K₀ : Type) [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀] (d : K₁ →ₗ[A] K₀), Good p r d → Good p (fun k => algebraMap A B (r k)) (d.baseChange B) := by
  intro p _ A _ B _ _ r K₁ K₀ _ _ _ _ d hd
  intro C _ _ hC w hw k
  letI : Algebra A C := Algebra.compHom C (algebraMap A B)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁ := AlgebraTensorModule.cancelBaseChange A B C C K₁
  let e₀ := AlgebraTensorModule.cancelBaseChange A B C C K₀
  have hnat : ∀ v, e₀ ((d.baseChange B).lTensor C v) = d.lTensor C (e₁ v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [e₀, e₁, LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
      | add y y' h h' => simp only [tmul_add, map_add (f := _), h, h']
    | add v v' h h' => simp only [map_add (f := _), h, h']
  have hw' : d.lTensor C (e₁ w) = 0 := by rw [← hnat, hw, map_zero]
  have hmem := hd C hC (e₁ w) hw' k
  have hsmul : r k • e₁ w = e₁ (algebraMap A B (r k) • w) := by
    rw [← algebraMap_smul C (algebraMap A B (r k)) w, map_smul, algebraMap_smul]
    rfl
  have key : ∀ u : C ⊗[A] LinearMap.ker d,
      e₁.symm ((LinearMap.ker d).subtype.lTensor C u) ∈
        LinearMap.range ((LinearMap.ker (d.baseChange B)).subtype.lTensor C) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      have hx : (1 : B) ⊗ₜ[A] (x : K₁) ∈ LinearMap.ker (d.baseChange B) := by
        simp [LinearMap.baseChange_tmul, x.2]
      refine ⟨c ⊗ₜ ⟨_, hx⟩, ?_⟩
      simp [e₁, AlgebraTensorModule.cancelBaseChange_symm_tmul]
    | add u u' h h' => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ h h'
  obtain ⟨u, hu⟩ := hmem
  have := key u
  rw [hu, hsmul, LinearEquiv.symm_apply_apply] at this
  exact this

end GlobalTheory.CompanionTheory.GoodBaseChange
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AdicCompl

theorem completion_complete (B : Type) [CommRing B] (π : B) :
    IsAdicComplete (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π})
      (AdicCompletion (Ideal.span {π}) B) := by
  have h := AdicCompletion.isAdicComplete (R := B) (I := Ideal.span {π}) (M := B)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {π}) B)] at h
  simpa [Ideal.map_span] using h

theorem completion_surj (B : Type) [CommRing B] (π : B) (M : ℕ)
    (y : AdicCompletion (Ideal.span {π}) B) :
    ∃ x : B, y - algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M} := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y.1 M)
  refine ⟨a, ?_⟩
  have hx : y - algebraMap B (AdicCompletion (Ideal.span {π}) B) a ∈
      ((Ideal.span {π}) ^ M).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
    rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton π),
      AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  rwa [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow] at hx

theorem completion_inj (B : Type) [CommRing B] (π : B) (M : ℕ) (x : B)
    (h : algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M}) :
    x ∈ Ideal.span {π ^ M} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {π}) M) hz
  have hf : Ideal.Quotient.mk (Ideal.span {π} ^ M) (π ^ M) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  rw [map_mul, map_pow, AlgHom.commutes, ← map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    hf, mul_zero] at h1
  rw [← Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm

theorem exists_isCompl : ∀ (B : Type) [CommRing B] (π : B),
    ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := by
  intro B _ π
  exact ⟨AdicCompletion (Ideal.span {π}) B, inferInstance,
    algebraMap B (AdicCompletion (Ideal.span {π}) B),
    { compl := completion_complete B π
      surj := completion_surj B π
      inj := completion_inj B π }⟩

end GlobalTheory.CompanionTheory.AdicCompl
end
end

section

open CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OntoDLog

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem form_mul_left {a : ℕ} (c g₀ : A) (g : Fin a → A) :
    form K (c * g₀) g = c • form K g₀ g := by
  simp only [form, mul_smul]

theorem form_cons_mem {a : ℕ} (f h : A) (g : Fin a → A) :
    form K h (Fin.cons f g : Fin (a + 1) → A) ∈ relOm K (Ideal.span {f}) (a + 1) := by
  apply Submodule.subset_span
  exact ⟨h, Fin.cons f g, Or.inr ⟨0, by rw [Fin.cons_zero]; exact Ideal.mem_span_singleton_self f⟩, rfl⟩

theorem form_cons_eq_smul {a : ℕ} (f h g₀ : A) (g : Fin a → A) (k : Fin a)
    (hk : g k = f * h) :
    form K g₀ (Fin.cons f g : Fin (a + 1) → A) =
      f • form K g₀ (Fin.cons f (Function.update g k h) : Fin (a + 1) → A) := by
  set v : Fin (a + 1) → Ω[A⁄K] := fun i =>
    KaehlerDifferential.D K A ((Fin.cons f (Function.update g k h) : Fin (a + 1) → A) i) with hv
  have hcons : (fun i => KaehlerDifferential.D K A ((Fin.cons f g : Fin (a + 1) → A) i)) =
      Function.update v k.succ (f • KaehlerDifferential.D K A h + h • KaehlerDifferential.D K A f) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    | succ j =>
      by_cases hj : j = k
      · subst hj
        simp [hk, Derivation.leibniz]
      · simp [v, hj, Function.update_apply]
  have hv1 : Function.update v k.succ (KaehlerDifferential.D K A h) = v := by
    funext i
    by_cases hi : i = k.succ
    · subst hi
      simp [v]
    · simp [Function.update_apply, hi]
  have hv2 : exteriorPower.ιMulti A (a + 1) (Function.update v k.succ (KaehlerDifferential.D K A f)) = 0 := by
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := k.succ)
    · simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    · exact (Fin.succ_ne_zero k).symm
  simp only [form]
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, hv1, hv2, smul_zero, add_zero, smul_comm]

theorem dLog : DLog := by
  unfold DLog
  intro K A _ _ _ a f hf w hw ω hω
  have hex : ∀ ω ∈ relOm K (Ideal.span {f}) a,
      ∃ η ∈ relOm K (Ideal.span {f}) (a + 1), f • η = w ω := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, hg, rfl⟩ := hx
      rcases hg with hg₀ | ⟨k, hk⟩
      · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg₀
        refine ⟨form K c (Fin.cons f g), form_cons_mem f c g, ?_⟩
        rw [hw, ← form_mul_left]
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
        refine ⟨form K g₀ (Fin.cons f (Function.update g k c)), form_cons_mem f g₀ _, ?_⟩
        rw [hw, form_cons_eq_smul f c g₀ g k hc]
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨η₁, h₁, e₁⟩ := hx
      obtain ⟨η₂, h₂, e₂⟩ := hy
      exact ⟨η₁ + η₂, Submodule.add_mem _ h₁ h₂, by rw [smul_add, e₁, e₂, map_add (f := _)]⟩
    | smul c x _ hx =>
      obtain ⟨η, h₁, e₁⟩ := hx
      exact ⟨c • η, Submodule.smul_mem _ c h₁, by rw [smul_comm, e₁, map_smul]⟩
  obtain ⟨η, hη, e⟩ := hex ω hω
  refine ⟨η, ⟨hη, e⟩, ?_⟩
  rintro η' ⟨_, e'⟩
  have hz : f • (η' - η) = 0 := by rw [smul_sub, e, e', sub_self]
  exact sub_eq_zero.mp (hf _ hz)

end GlobalTheory.CompanionTheory.OntoDLog
end

section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

theorem interleave_exchange {u v w : List T} (h : Interleave u v w) :
    ∀ {u' x : List T}, Interleave u' x v →
      ∃ v', Interleave u' v' w ∧ Interleave u x v' := by
  induction h with
  | nil =>
    intro u' x h'
    cases h'
    exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left a u v w _ ih =>
    intro u' x h'
    obtain ⟨v', h₁, h₂⟩ := ih h'
    exact ⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩
  | @right a u v w _ ih =>
    intro u' x h'
    cases h' with
    | left h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨v', Interleave.left h₁, h₂⟩
    | right h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩

theorem shuffle_swap {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁

theorem shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)

end GlobalTheory.CompanionTheory.ShuffleWords
end
