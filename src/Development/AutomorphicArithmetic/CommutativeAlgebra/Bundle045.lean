module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRestrictScalarsField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AutomorphicArithmetic.RealSpanData.RealData

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem exists_den {Λ : Type} [AddCommGroup Λ] (t : ℚ ⊗[ℤ] Λ) :
    ∃ (n : ℤ) (z : Λ), n ≠ 0 ∧ n • t = (1 : ℚ) ⊗ₜ[ℤ] z := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q z =>
    refine ⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩
    have h : ((q.den : ℤ)) • q = q.num • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]
      exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨n, z, hn, h⟩ := ha
    obtain ⟨m, w, hm, h'⟩ := hb
    refine ⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h',
      smul_smul, smul_smul, mul_comm m n]

private theorem sep_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (a : ℚ ⊗[ℤ] Λ) (h : ∀ w, B.baseChange ℚ a w = 0) : a = 0 := by
  obtain ⟨n, z, hn, e⟩ := exists_den a
  have hz : z = 0 := by
    apply hB
    intro w
    have h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0 := by
      rw [← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]
    simpa [LinearMap.BilinForm.baseChange_tmul] using h2
  rw [hz, TensorProduct.tmul_zero] at e
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← Int.cast_smul_eq_zsmul ℚ] at e
  exact (smul_eq_zero.1 e).resolve_left hn'

private theorem adj_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (f g : Λ →ₗ[ℤ] Λ)
    (h : ∀ x y, B (f x) y = B x (g y)) (u w : ℚ ⊗[ℤ] Λ) :
    B.baseChange ℚ (f.baseChange ℚ u) w = B.baseChange ℚ u (g.baseChange ℚ w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]

private theorem anti_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (h : ∀ x, B x x = 0)
    (u w : ℚ ⊗[ℤ] Λ) : B.baseChange ℚ u w = - B.baseChange ℚ w u := by
  have anti : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h, zero_add, add_zero] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [anti x y]
      rw [mul_comm q r, neg_smul]

private theorem exists_rep {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (hE : ∀ a, (∀ w, E a w = 0) → a = 0) :
    ∃ b : Module.End ℚ V, ∀ u w, F u w = 2 * E (b u) w := by
  have inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hE a fun w => by rw [ha]; rfl
  let Φ : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm
  refine ⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩
  have h : E (Φ.symm (F u)) = F u := Φ.apply_symm_apply (F u)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]
  ring

theorem UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (Y : PLat D.O D.inv) (j : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D), (∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), j ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (j u)) → ∃ β : G.Cˣ, sh G β = β ∧ ∀ u w : ℚ ⊗[ℤ] Y.La, Y.EF.baseChange ℚ u w = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j u)) (j w) := by
  intro p _ D G L Y j hj
  haveI := D.finLa
  set E := D.EF.baseChange ℚ with hEdef
  have sepE : ∀ a, (∀ w, E a w = 0) → a = 0 := fun a h =>
    sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h
  have sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0 := fun a h => sep_bc Y.EF Y.nondeg a h
  have eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a' := fun a a' h => by
    rw [← sub_eq_zero]
    exact sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]
  let F : LinearMap.BilinForm ℚ (VQ D) :=
    ((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)
  have hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w) := fun u w => rfl
  obtain ⟨b, hb⟩ := exists_rep E F sepE
  have hinj : Function.Injective b := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have : j.symm u = 0 := sepY _ fun w => by
      have h := hb u (j w)
      rw [hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply] at h
      exact h
    simpa using this
  have comm : ∀ c : D.O, b * actQ D c = actQ D c * b := by
    intro c
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    have hc : j.symm (actQ D c u) = (DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u) := by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribSMul.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w) := fun w => by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w) := by
      rw [hF, hF, hc, hc']
      exact adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _
    have h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w) :=
      adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _
    have h3 := hb (actQ D c u) w
    have h4 := hb u (actQ D (D.inv c) w)
    simp only [Module.End.mul_apply]
    rw [h2]
    linarith
  have hsym : ∀ u w, E (b u) w = E u (b w) := by
    intro u w
    have h1 := hb u w
    have h2 := hb w u
    have h3 : F u w = - F w u := by
      rw [hF, hF]
      exact anti_bc Y.EF Y.alt _ _
    have h4 : E (b w) u = - E u (b w) := anti_bc D.EF D.alt _ _
    linarith
  obtain ⟨b₀, hb₀⟩ : ∃ x : G.C, L.rep x = b := (L.rep_range b).2 comm
  let e : VQ D ≃ₗ[ℚ] VQ D := LinearEquiv.ofInjectiveEndo b hinj
  have he : ∀ u, b (e.symm u) = u := fun u => e.apply_symm_apply u
  have he' : ∀ u, e.symm (b u) = u := fun u => e.symm_apply_apply u
  have comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap := by
    intro c
    refine LinearMap.ext fun u => hinj ?_
    have h := LinearMap.congr_fun (comm c) (e.symm u)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢
    exact h.symm
  obtain ⟨b₁, hb₁⟩ : ∃ x : G.C, L.rep x = e.symm.toLinearMap :=
    (L.rep_range e.symm.toLinearMap).2 comm'
  have h01 : b₀ * b₁ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he u
  have h10 : b₁ * b₀ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he' u
  have hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w) := L.adj
  have shsh : sh G (sh G b₀) = b₀ := G.star_star b₀
  have shmul : ∀ x y, sh G (x * y) = sh G y * sh G x := fun x y => by
    unfold sh
    rw [map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by
    unfold sh
    rw [map_one, MulOpposite.unop_one]
  have hs : sh G b₀ = b₀ := by
    apply L.rep_inj
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    rw [hadj, shsh, hb₀, hsym]
  have hs1 : sh G b₁ = b₁ := by
    have h : sh G b₁ * b₀ = 1 := by
      have h' := shmul b₀ b₁
      rw [h01, shone, hs] at h'
      exact h'.symm
    calc sh G b₁ = sh G b₁ * (b₀ * b₁) := by rw [h01, _root_.mul_one]
      _ = (sh G b₁ * b₀) * b₁ := (_root_.mul_assoc _ _ _).symm
      _ = b₁ := by rw [h, _root_.one_mul]
  refine ⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩
  have h := hb (j u) (j w)
  rw [hF, j.symm_apply_apply, j.symm_apply_apply] at h
  rw [h]
  show _ = 2 * E (L.rep b₀ (j u)) (j w)
  rw [hb₀]
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) : G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then G.psi (InfinitePlace.mk σ)
  else ((starRingEnd ℂ).mapMatrix).comp (G.psi (InfinitePlace.mk σ))

private theorem psiE_F {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) (x : G.F) :
    psiE G σ (algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (σ x) := by
  unfold psiE
  split_ifs with h
  · rw [G.psi_F, h]
  · have h2 : (InfinitePlace.mk σ).embedding = ComplexEmbedding.conjugate σ :=
      (InfinitePlace.embedding_mk_eq σ).resolve_left h
    rw [RingHom.comp_apply, G.psi_F, h2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, ComplexEmbedding.conjugate_coe_eq]

private theorem sum_psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (c : G.C) :
    ∑ σ : G.F →+* ℂ, Matrix.trace (psiE G σ c) =
      ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : G.F →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex v)) h
  have hf : (Finset.univ.filter fun σ : G.F →+* ℂ => InfinitePlace.mk σ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        rw [h]
        exact (star_star σ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne.symm]
  have h1 : psiE G v.embedding = G.psi v := by
    unfold psiE
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  have h2 : psiE G (ComplexEmbedding.conjugate v.embedding) = ((starRingEnd ℂ).mapMatrix).comp (G.psi v) := by
    unfold psiE
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne.symm]
  rw [h1, h2, RingHom.comp_apply]
  have h3 : Matrix.trace (((starRingEnd ℂ).mapMatrix) (G.psi v c)) = (starRingEnd ℂ) (Matrix.trace (G.psi v c)) := by

    simp [Matrix.trace, map_sum]
  rw [h3, Complex.add_conj]

private theorem trace_rep {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (c : G.C) :
    ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) =
      2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re := by
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * G.n * Module.finrank ℚ G.F := by
    haveI := D.freeLa
    rw [h3, L.n_eq, ← D.rankLa]
    exact Module.finrank_baseChange
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  have hq := GlobalTheory.QTrace.q_trace (F := G.F) (A := G.C) (V := VQ D) G.n G.rankC L.rep.toRingHom (psiE G) (psiE_F G) c
  rw [sum_psiE, h4] at hq
  have hn : (G.n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 G.n_pos.ne'
  have hd : ((Module.finrank ℚ G.F : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast at hq
  have hq' : ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℂ) =
      (D.m : ℂ) * ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    have : (G.n : ℂ) * (Module.finrank ℚ G.F : ℂ) ≠ 0 := mul_ne_zero hn hd
    apply mul_left_cancel₀ this
    push_cast
    linear_combination hq
  have : (((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) : ℂ) =
      ((2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    push_cast at hq' ⊢
    rw [hq', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  exact_mod_cast this

theorem UpperTheory.trace_action_eq_sum_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : ℝ ⊗[ℚ] G.C), LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D) (actOn L.rep ℝ x) = 2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psiR v x)).re := by
  intro p _ D G L x
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib, hx, hy, mul_add]
  | tmul r c =>
    have h1 : actOn L.rep ℝ (r ⊗ₜ[ℚ] c) = r • (L.rep c).baseChange ℝ := by
      rw [Algebra.smul_def]
      exact Algebra.TensorProduct.lift_tmul _ _ _ r c
    rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul]
    have h2 : (algebraMap ℚ ℝ) (LinearMap.trace ℚ (VQ D) (L.rep c)) = ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) := rfl
    rw [h2, trace_rep]
    simp only [HTGroup.psiR_tmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ← Finset.mul_sum]
    ring
end
end

section

open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩
end
