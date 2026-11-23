module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory.LieIdempotents

theorem balanced_apply {K : Type} {M : Type*} [CommRing K] [AddCommGroup M] (k : ℕ) (u v : Fin k → K)
    (hyp : ∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c))
    (B : K →+ K →+ M) (c : K) : ∑ j, B (c * u j) (v j) = ∑ j, B (u j) (v j * c) := by
  have hB : ∀ (r : ℤ) (m n : K), B (r • m) n = B m (r • n) := by
    intro r m n; rw [map_zsmul, map_zsmul]; rfl
  have := congrArg (TensorProduct.liftAddHom B hB) (hyp c)

  simpa [map_sum, TensorProduct.liftAddHom_tmul] using this

end GlobalTheory.LieIdempotents

open GlobalTheory.LieIdempotents in
theorem GlobalTheory.lie_idempotents : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  intro R C K _ _ _ tR a t hcom N k u v huv hyp hN H _ _ ρF
  set n : C := ((hN.unit⁻¹ : Cˣ) : C) with hn
  have hnN : n * (N : C) = 1 := hN.val_inv_mul

  have hS : ∀ p q, ∑ j, t p (u j) * t q (v j) = if p = q then (N : R) else 0 := by
    intro p q
    split_ifs with hpq
    · subst hpq

      simp only [← map_mul, ← map_sum, huv, map_intCast]
    · set S := ∑ j, t p (u j) * t q (v j) with hSdef
      let B : K →+ K →+ R := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => t p x * t q y)
        (by intro y y'; simp [mul_add])) (by intro x x'; ext y; simp [add_mul])
      have hc : ∀ c, t p c * S = S * t q c := by
        intro c
        have := balanced_apply k u v hyp B c
        simp only [B, AddMonoidHom.mk'_apply, map_mul] at this
        rw [hSdef, Finset.mul_sum, Finset.sum_mul]
        convert this using 2 <;> ring
      have hle : Ideal.span (Set.range fun x => t p x - t q x) ≤ LinearMap.ker (LinearMap.mulLeft R S) := by
        rw [Ideal.span_le]
        rintro _ ⟨x, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
        rw [mul_sub, mul_comm S, hc, sub_self]
      rw [hcom p q hpq] at hle
      have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.mulLeft R S) := hle Submodule.mem_top
      simpa using h1
  have hSC : ∀ p q, ∑ j, tR (t p (u j)) * tR (t q (v j)) = if p = q then (N : C) else 0 := by
    intro p q
    have := congrArg tR (hS p q)

    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  have hnNx : ∀ x : Module.End C H, n • (N : C) • x = x := by
    intro x; rw [smul_smul, hnN, one_smul]
  have heig : ∀ i c, ρF c * (n • ∑ j, tR (t i (v j)) • ρF (u j)) = tR (t i c) • (n • ∑ j, tR (t i (v j)) • ρF (u j)) := by
    intro i c
    let B : K →+ K →+ Module.End C H := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => tR (t i y) • ρF x)
        (by intro y y'; simp [add_smul])) (by intro x x'; ext y : 1; simp [smul_add])
    have hb := balanced_apply k u v hyp B c
    simp only [B, AddMonoidHom.mk'_apply, map_mul] at hb
    rw [mul_smul_comm, Finset.mul_sum]
    simp only [mul_smul_comm]
    rw [hb, smul_comm (tR (t i c)) n]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [smul_smul, mul_comm]
  refine ⟨fun i => n • ∑ j, tR (t i (v j)) • ρF (u j), heig, ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    dsimp only
    generalize hΦ : n • ∑ l, tR (t j (v l)) • ρF (u l) = Φ at heig
    have hj := heig j
    rw [hΦ] at hj
    rw [smul_mul_assoc, Finset.sum_mul]
    simp only [smul_mul_assoc, hj, smul_smul, ← Finset.sum_smul]
    have hsum : ∑ l, tR (t i (v l)) * tR (t j (u l)) = ∑ l, tR (t j (u l)) * tR (t i (v l)) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hsum, hSC j i]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, hnN, one_smul]; exact hΦ.symm
    · simp [hij, Ne.symm hij]
  · intro g hg i
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hg]
  · intro F hF i x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hF _ _ hx))
  · intro F hF i w hw j
    have e : (n • ∑ l, tR (t j (v l)) • ρF (u l)) w - (if j = i then w else 0)
        = n • ∑ l, tR (t j (v l)) • (ρF (u l) w - tR (t i (u l)) • w) := by
      have hite : (if j = i then w else 0) = n • (∑ l, tR (t i (u l)) * tR (t j (v l))) • w := by
        rw [hSC i j]; by_cases hij : i = j
        · subst hij; simp [smul_smul, hnN]
        · simp [hij, Ne.symm hij]
      rw [hite]
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring_nf
    rw [e]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hw _))
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TraceCasimir

variable {A : Type} [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A]

noncomputable def trL : A →ₗ[ℤ] ℤ := LinearMap.trace ℤ A ∘ₗ LinearMap.mul ℤ A

lemma trL_apply (z : A) : trL z = LinearMap.trace ℤ A (LinearMap.mulLeft ℤ z) := rfl

lemma trL_comm (x y : A) : trL (x * y) = trL (y * x) := by
  rw [trL_apply, trL_apply, LinearMap.mulLeft_mul, LinearMap.mulLeft_mul]
  exact LinearMap.trace_mul_comm ℤ _ _

lemma trL_eq_sum {n : ℕ} (b : Module.Basis (Fin n) ℤ A) (z : A) :
    trL z = ∑ k, b.repr (z * b k) k := by
  rw [trL_apply, LinearMap.trace_eq_matrix_trace ℤ b, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ A)

noncomputable def gram : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun k l => trL (b k * b l)

noncomputable def dualD (l : Fin n) : A := ∑ m, (gram b).adjugate m l • b m

lemma trL_mul_dualD (u : A) (l : Fin n) :
    trL (u * dualD b l) = ∑ m, (gram b).adjugate m l * trL (u * b m) := by

  simp only [dualD, Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, smul_eq_mul]

lemma trL_basis_mul_dualD (k l : Fin n) :
    trL (b k * dualD b l) = if k = l then (gram b).det else 0 := by
  rw [trL_mul_dualD]
  calc ∑ m, (gram b).adjugate m l * trL (b k * b m)
      = ∑ m, gram b k m * (gram b).adjugate m l :=
        Finset.sum_congr rfl fun m _ => mul_comm _ _
    _ = (gram b * (gram b).adjugate) k l := (Matrix.mul_apply).symm
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp

lemma det_mul_repr (u : A) (k : Fin n) :
    (gram b).det * b.repr u k = trL (u * dualD b k) := by
  conv_rhs => rw [← b.sum_repr u]

  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, trL_basis_mul_dualD, smul_eq_mul]
  simp [mul_comm]

lemma det_smul_eq (u : A) : (gram b).det • u = ∑ l, trL (u * dualD b l) • b l := by
  conv_lhs => rw [← b.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, det_mul_repr]

section Nondeg

variable (hnd : ∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0)
include hnd

lemma eq_zero_of_trL_mul_basis (v : A) (hv : ∀ k, trL (v * b k) = 0) : v = 0 := by
  apply hnd v
  intro y
  rw [← trL_apply]
  conv_lhs => rw [← b.sum_repr y]

  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, hv, smul_zero,
  Finset.sum_const_zero]

lemma eq_zero_of_trL_basis_mul (v : A) (hv : ∀ k, trL (b k * v) = 0) : v = 0 :=
  eq_zero_of_trL_mul_basis b hnd v fun k => by rw [trL_comm]; exact hv k

lemma det_smul_eq' (u : A) : (gram b).det • u = ∑ l, trL (b l * u) • dualD b l := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_basis_mul b hnd
  intro k

  simp only [mul_sub, Finset.mul_sum, mul_smul_comm, map_sub, map_sum, map_zsmul, smul_eq_mul,
  trL_basis_mul_dualD, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma det_ne_zero : (gram b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv0
  have hx : ∑ k, v k • b k = 0 := by
    apply eq_zero_of_trL_mul_basis b hnd
    intro l
    have := congrFun hv l
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply] at this

    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, smul_eq_mul]
    exact this
  funext k
  exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx k

lemma sum_mul_dualD : ∑ k, b k * dualD b k = ((gram b).det : A) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_mul_basis b hnd
  intro j

  rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  have h1 : ∀ k, trL (b k * dualD b k * b j) = (gram b).det * b.repr (b j * b k) k := by
    intro k
    rw [trL_comm, ← mul_assoc, ← det_mul_repr]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, ← trL_eq_sum b, ← zsmul_eq_mul,
    map_zsmul, smul_eq_mul, sub_self]

lemma balanced (c : A) :
    ∑ k, (c * b k) ⊗ₜ[ℤ] dualD b k = ∑ k, b k ⊗ₜ[ℤ] (dualD b k * c) := by
  haveI : Module.Free ℤ (A ⊗[ℤ] A) := Module.Free.of_basis (b.tensorProduct b)
  apply smul_right_injective (A ⊗[ℤ] A) (det_ne_zero b hnd)
  dsimp only
  simp only [Finset.smul_sum]
  have hL : ∀ k, (gram b).det • ((c * b k) ⊗ₜ[ℤ] dualD b k) =
      ∑ l, trL (c * b k * dualD b l) • (b l ⊗ₜ[ℤ] dualD b k) := by
    intro k
    rw [TensorProduct.smul_tmul', det_smul_eq, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  have hR : ∀ k, (gram b).det • (b k ⊗ₜ[ℤ] (dualD b k * c)) =
      ∑ l, trL (b l * (dualD b k * c)) • (b k ⊗ₜ[ℤ] dualD b l) := by
    intro k
    rw [← TensorProduct.tmul_smul, det_smul_eq' b hnd, TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [mul_assoc, trL_comm, mul_assoc]

end Nondeg

end GlobalTheory.TraceCasimir


open GlobalTheory.TraceCasimir in
theorem GlobalTheory.exists_separability_element_of_trace_nondegenerate :
    ∀ (A : Type) [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A],
      (∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0) →
      ∃ (N : ℤ) (k : ℕ) (x y : Fin k → A), N ≠ 0 ∧ ∑ j, x j * y j = (N : A) ∧
        ∀ c : A, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c) := by
  intro A _ _ _ hnd
  let b := Module.finBasis ℤ A
  exact ⟨(gram b).det, _, b, dualD b, det_ne_zero b hnd, sum_mul_dualD b hnd, balanced b hnd⟩
end

section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory

theorem lintegral_mul_measure_inter_smul_preimage :
    ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  intro S X _ _ _ _ _ _ ν _ μ _ _ D hD E hE ψ hψ hinv
  have hmeas : Measurable (Function.uncurry fun (s : S) (y : X) =>
      ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y))) := by
    have hsm' : Measurable (fun p : S × X => p.1⁻¹ • p.2) :=
      (measurable_fst.inv).smul measurable_snd
    refine (hψ.comp measurable_snd).mul ?_
    exact ((measurable_one.indicator hE).comp measurable_fst).mul
      ((measurable_one.indicator hD).comp hsm')
  have h1 : ∀ y : X, ν (E ∩ {s | s⁻¹ • y ∈ D}) =
      ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂ν := by
    intro y
    have hm : MeasurableSet (E ∩ {s : S | s⁻¹ • y ∈ D}) :=
      hE.inter (hD.preimage (measurable_inv.smul_const y))
    rw [← lintegral_indicator_one hm]
    congr 1; ext s
    by_cases h1 : s ∈ E <;> by_cases h2 : s⁻¹ • y ∈ D <;> simp [Set.indicator, h1, h2]
  have h2 : ∀ s : S, ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ = ∫⁻ x in D, ψ x ∂μ := by
    intro s
    have hf : Measurable (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) :=
      hψ.mul (measurable_one.indicator hD)
    calc ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ
        = ∫⁻ y, (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) (s⁻¹ • y) ∂μ := by
          congr 1; ext y; simp only [hinv]
      _ = ∫⁻ x, ψ x * D.indicator (1 : X → ℝ≥0∞) x ∂μ :=
          (measurePreserving_smul s⁻¹ μ).lintegral_comp hf
      _ = ∫⁻ x in D, ψ x ∂μ := by
          rw [← lintegral_indicator hD]
          congr 1; ext x
          by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  calc ν E * ∫⁻ x in D, ψ x ∂μ
      = ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ ∂ν := by
        simp only [h2]
        rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]
    _ = ∫⁻ s, ∫⁻ y, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂μ ∂ν := by
        congr 1; ext s
        rw [← lintegral_const_mul' _ _ (by by_cases h : s ∈ E <;> simp [Set.indicator, h])]
        congr 1; ext y; ring
    _ = ∫⁻ y, ∫⁻ s, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂ν ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
        congr 1; ext y
        have hm : Measurable (fun s : S =>
            E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) :=
          (measurable_one.indicator hE).mul
            ((measurable_one.indicator hD).comp (measurable_inv.smul_const y))
        rw [h1 y]
        exact lintegral_const_mul (ψ y) hm

end GlobalTheory
end

section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem lintegral_unfold_refold (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  haveI : MeasurableConstSMul Γ X :=
    ⟨fun c => (measurable_const_smul (c : S) : Measurable fun x : X => (c : S) • x)⟩
  haveI : SMulInvariantMeasure Γ X μ :=
    ⟨fun c A hA => SMulInvariantMeasure.measure_preimage_smul (c : S) hA⟩
  haveI : MeasurableConstSMul Γ S :=
    ⟨fun c => (measurable_const_mul (c : S) : Measurable fun x : S => (c : S) * x)⟩
  haveI : SMulInvariantMeasure Γ S ν :=
    ⟨fun c A _ => measure_preimage_mul ν (c : S) A⟩
  set F : X → ℝ≥0∞ := fun y => ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) with hF
  have hQ : MeasurableSet {p : X × S | p.2 ∈ E ∧ p.2⁻¹ • p.1 ∈ D₁} :=
    (measurable_snd hE).inter (hD₁.preimage (measurable_snd.inv.smul measurable_fst))
  have hmeasν : Measurable fun y : X => ν (E ∩ {s | s⁻¹ • y ∈ D₁}) := by
    have := measurable_measure_prodMk_left (ν := ν) hQ
    exact this
  have hFm : Measurable F := hψ.mul hmeasν
  have hstep : ∀ y : X, ∑' γ : Γ, F (γ • y) = ψ y * ν {s | s⁻¹ • y ∈ D₁} := by
    intro y
    have h1 : ∀ γ : Γ, F (γ • y) = ψ y * ν (E ∩ {s | s⁻¹ • ((γ : S) • y) ∈ D₁}) := by
      intro γ
      simp only [hF, Subgroup.smul_def, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [hEf.measure_eq_tsum {s | s⁻¹ • y ∈ D₁}]
    refine tsum_congr fun γ => ?_
    congr 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq,
      Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]
    exact and_comm
  calc ∫⁻ y, F y ∂μ = ∑' γ : Γ, ∫⁻ y in D₂, F (γ • y) ∂μ := hD₂.lintegral_eq_tsum'' F
    _ = ∫⁻ y in D₂, ∑' γ : Γ, F (γ • y) ∂μ := by
      rw [lintegral_tsum]
      intro γ
      exact (hFm.comp (measurable_const_smul γ)).aemeasurable
    _ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
      simp_rw [hstep]

end GlobalTheory.CovolIndep
end

section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem isFundamentalDomain_of_ae_eq {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X]
    [MulAction Γ X] [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]
    {s t : Set X} (h : IsFundamentalDomain Γ s μ) (hst : t =ᵐ[μ] s) :
    IsFundamentalDomain Γ t μ := by
  refine ⟨h.nullMeasurableSet.congr hst.symm, ?_, ?_⟩
  ·
    have hall : ∀ᵐ x ∂μ, ∀ g : Γ, (g • x ∈ t) = (g • x ∈ s) := by
      rw [ae_all_iff]
      intro g
      exact ((measurePreserving_smul g μ).quasiMeasurePreserving.ae hst).mono fun _ hx => propext hx
    filter_upwards [h.ae_covers, hall] with x ⟨g, hg⟩ hx
    exact ⟨g, by rw [hx g]; exact hg⟩
  · intro a b hab
    have key : ∀ c : Γ, (c • t : Set X) =ᵐ[μ] (c • s : Set X) := fun c => by
      rw [← Set.preimage_smul_inv, ← Set.preimage_smul_inv]
      exact (measurePreserving_smul c⁻¹ μ).quasiMeasurePreserving.preimage_ae_eq hst
    exact (h.aedisjoint hab).congr (key a) (key b)

variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem ae_measure_setOf_smul_mem_eq_zero (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] {W : Set X} (hW : μ W = 0) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ W} = 0 := by
  set W' := toMeasurable μ W
  have hW'm : MeasurableSet W' := measurableSet_toMeasurable μ W
  have hW'0 : μ W' = 0 := by rw [measure_toMeasurable]; exact hW
  have hQ : MeasurableSet {p : X × S | p.2 • p.1 ∈ W'} :=
    hW'm.preimage (measurable_snd.smul measurable_fst)
  have h0 : μ.prod ν {p : X × S | p.2 • p.1 ∈ W'} = 0 := by
    rw [Measure.prod_apply_symm hQ]
    have : ∀ s : S, μ ((fun x => (x, s)) ⁻¹' {p : X × S | p.2 • p.1 ∈ W'}) = 0 := fun s => by
      change μ ((fun x => s • x) ⁻¹' W') = 0
      rw [measure_preimage_smul]; exact hW'0
    exact (lintegral_congr this).trans lintegral_zero
  have h1 := (Measure.measure_prod_null hQ).1 h0
  filter_upwards [h1] with y hy
  exact measure_mono_null (fun s hs => subset_toMeasurable μ W hs) hy

end GlobalTheory.CovolIndep
end
