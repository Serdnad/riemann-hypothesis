module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.PairConj

section Generic

variable {S : Type*} [Ring S]

theorem unop_mul_inv (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem unop_inv_mul (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ ((y⁻¹ : Sˣ) : S)).unop * (σ (y : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem triv_conj (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) :
    ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop =
      (x : S) * b * (σ (x : S)).unop := by
  have h := unop_mul_inv σ y
  calc ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop
      = (x : S) * (((y⁻¹ : Sˣ) : S) * y) * b * ((σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop) *
          (σ (x : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h, mul_one, mul_one]

end Generic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

def shU (y : G.Cˣ) : G.Cˣ :=
  ⟨sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C), unop_mul_inv G.star y, unop_inv_mul G.star y⟩

theorem shU_val (y : G.Cˣ) : ((shU G y : G.Cˣ) : G.C) = sh G y := rfl

def conjAlg (y : G.Cˣ) : G.C →ₐ[G.F] G.C where
  toFun a := y * a * ((y⁻¹ : G.Cˣ) : G.C)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    show (y : G.C) * algebraMap G.F G.C r * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C r
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem conjAlg_injective (y : G.Cˣ) : Function.Injective (conjAlg G y) := by
  intro a b h
  have h' : (y : G.C) * a * ((y⁻¹ : G.Cˣ) : G.C) = y * b * ((y⁻¹ : G.Cˣ) : G.C) := h
  have := congrArg (fun z => ((y⁻¹ : G.Cˣ) : G.C) * z * (y : G.C)) h'
  simpa [mul_assoc] using this

variable {G} in
theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm


variable {G} in
theorem triv_conj_unit (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ)
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]
    rfl
  rw [e, triv_conj, hx]

variable {G}

theorem conj_val (β y : G.Cˣ) : ((y * β * shU G y : G.Cˣ) : G.C) = (y : G.C) * β * sh G y := by
  rw [Units.val_mul, Units.val_mul, shU_val]

def conjPair (P : Pair G) (y : G.Cˣ) : Pair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  trivR := by
    obtain ⟨z, hz⟩ := P.trivR
    have h := triv_conj_unit ℝ (P.β : G.C) y z 1 hz
    rw [← conj_val] at h
    exact ⟨_, h⟩

theorem conjPair_β (P : Pair G) (y : G.Cˣ) :
    (((conjPair P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

end GlobalTheory.LKMid.PairConj


open GlobalTheory.LKMid.PairConj in
theorem GlobalTheory.LKMid.Pair.exists_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (y : G.Cˣ),
    ∃ P' : Pair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  intro p _ G P y
  refine ⟨conjPair P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjPair_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjPair_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem inv_form_of_rel {S : Type*} [Ring S] [Algebra ℚ S] (b b' y : Sˣ) (z : S) (s : ℚ)
    (h : (b' : S) = algebraMap ℚ S s * (y * b * z)) :
    s • (z * ((b'⁻¹ : Sˣ) : S) * y) = ((b⁻¹ : Sˣ) : S) := by
  have h1 : algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S) = 1 := by rw [← h, Units.mul_inv]
  calc s • (z * ((b'⁻¹ : Sˣ) : S) * y)
      = ((b⁻¹ : Sˣ) : S) * ((y⁻¹ : Sˣ) : S) * (algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S)) * y := by
        simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [h1, mul_one, mul_assoc, Units.inv_mul, mul_one]

theorem form_of_rel {p : ℕ} [Fact p.Prime] {G : HTGroup p} (b b' y : G.Cˣ) (s : ℚ)
    (h : (b' : G.C) = algebraMap ℚ G.C s * (y * b * sh G y)) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    (star x ⬝ᵥ ((G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re =
      (s : ℝ) * (star (G.psi v y *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v y *ᵥ x))).re := by
  have hu : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have e : G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C) =
      (s : ℂ) • ((G.psi v y)ᴴ * (G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) * G.psi v y) := by
    rw [← inv_form_of_rel b b' y _ s h, map_rat_smul, map_mul, map_mul, sh, G.psi_star, Matrix.mul_smul,
      ← Rat.cast_smul_eq_qsmul ℂ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, ← Complex.ofReal_ratCast, Complex.re_ofReal_mul]

theorem mark_iff_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (μ : ℂ),
    P.Rel Q → (P.Mark μ ↔ Q.Mark μ) := by
  rintro p _ G P Q μ ⟨y, s, hs, hβ, hγ⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v y *ᵥ x, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, hγ, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ] at hpos
      exact (mul_pos_iff_of_pos_left hs').1 hpos
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x, ?_, ?_⟩
    · have e : P.γ * y⁻¹ = y⁻¹ * Q.γ := by rw [hγ]; group
      rw [Matrix.mulVec_mulVec, ← map_mul, ← Units.val_mul, e, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ, Matrix.mulVec_mulVec x (G.psi v y), ← map_mul, Units.mul_inv, map_one,
        Matrix.one_mulVec]
      exact mul_pos hs' hpos

end GlobalTheory.LKMid.Pair
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

theorem map_starT {A R' C : Type} [CommRing A] [Algebra ℚ A] [CommRing R'] [Algebra ℚ R'] [Ring C] [Algebra ℚ C]
    (σ : C →+* Cᵐᵒᵖ) (f : A →ₐ[ℚ] R') (y : A ⊗[ℚ] C) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ C) (starT σ A y).unop =
      (starT σ R' (Algebra.TensorProduct.map f (AlgHom.id ℚ C) y)).unop := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem map_conj_ext {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] {L : Type} [Field L]
    [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L) (β₁ : G.Cˣ)
    (hc : ∀ x, ι (c x) = β₁ * sh G (ι x) * ((β₁⁻¹ : G.Cˣ) : G.C)) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) =
      ((1 : K) ⊗ₜ[ℚ] (β₁ : G.C)) * (starT G.star K (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι z)).unop *
        ((1 : K) ⊗ₜ[ℚ] ((β₁⁻¹ : G.Cˣ) : G.C)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, AlgHom.id_apply,
      AlgHom.id_apply, hc]
    rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, mul_add, add_mul]

theorem map_invol {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L)
    (hcc : ∀ x, c (c x) = x) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) c (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hcc]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem selfDual_conj_eq_one {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : B →+* A) (hιR : ∀ r, ι (algebraMap R B r) = algebraMap R A r) (σ : A →+* Aᵐᵒᵖ) (cc : B →+* B) (β₁ : Aˣ)
    (X X₁ : Aˣ) (t t₁ : Rˣ) (a' : B) (m : Bˣ)
    (hc : ι (cc m) = ↑β₁ * (σ (ι m)).unop * ↑β₁⁻¹)
    (h1 : (X : A) * (ι a' * β₁) * (σ X).unop = algebraMap R A t)
    (h2 : (X₁ : A) * β₁ * (σ X₁).unop = algebraMap R A t₁) :
    ((X : A) * ι m * ↑X₁⁻¹) * ((X₁ : A) * ι (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * ↑X₁⁻¹) *
      (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = 1 := by
  have hs1 : (σ (X₁ : A)).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht1 : algebraMap R A ((t₁⁻¹ : Rˣ) : R) * algebraMap R A (t₁ : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have k1 : ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * β₁ := by
    calc ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop
        = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (((X₁⁻¹ : Aˣ) : A) * algebraMap R A (t₁ : R) *
            (σ ((X₁⁻¹ : Aˣ) : A)).unop) := by
          rw [← Algebra.commutes (t₁ : R), ← mul_assoc, ← mul_assoc, ht1, one_mul]
      _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((((X₁⁻¹ : Aˣ) : A) * X₁) * β₁ *
            ((σ X₁).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop)) := by
          rw [← h2]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs1, one_mul, mul_one]
  have hβ : (β₁ : A) * (σ (ι m)).unop = ι (cc m) * β₁ := by
    rw [hc, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have hcm : cc (m : B) * cc ((m⁻¹ : Bˣ) : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hmE : (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m =
      algebraMap R B (↑t⁻¹ * ↑t₁) * a' := by
    calc (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m
        = algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (((m : B) * ↑m⁻¹) * (cc (m : B) * cc ↑m⁻¹)) := by ring
      _ = _ := by rw [Units.mul_inv, hcm, one_mul, mul_one]
  have hR : ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R) = 1 := by
    calc ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R)
        = (((t₁⁻¹ : Rˣ) : R) * (t₁ : R)) * (((t⁻¹ : Rˣ) : R) * (t : R)) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_mul]
  set E := algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹) with hE
  clear_value E
  have eσ : (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = (σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop := by
    simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [eσ]
  calc (X : A) * ι m * ↑X₁⁻¹ * (↑X₁ * ι E * ↑X₁⁻¹) *
        ((σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop)
      = (X : A) * ι m * (((X₁⁻¹ : Aˣ) : A) * X₁) * ι E * (((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop) *
          (σ (ι m)).unop * (σ X).unop := by simp only [mul_assoc]
    _ = (X : A) * ι m * ι E * (algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (β₁ * (σ (ι m)).unop)) * (σ X).unop := by
          rw [Units.inv_mul, k1, mul_one]; simp only [mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((X : A) * (ι ((m : B) * E * cc m) * β₁) * (σ X).unop) := by
          rw [hβ, show ι ((m : B) * E * cc m) = ι m * ι E * ι (cc m) by rw [map_mul, map_mul]]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (algebraMap R A (((t⁻¹ : Rˣ) : R) * (t₁ : R)) *
          ((X : A) * (ι a' * β₁) * (σ X).unop)) := by
          rw [hmE, map_mul, hιR]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 1 := by rw [h1, ← mul_assoc, ← map_mul, ← map_mul, hR, map_one]

theorem exists_finset_of_eventually {p : ℕ} {Q : AwayP p → Prop}
    (h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), Q v) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v : AwayP p, v.1 ∉ S → Q v := by
  rw [Filter.eventually_cofinite] at h
  refine ⟨(h.image Subtype.val).toFinset, fun v hv => ?_⟩
  by_contra hq
  exact hv ((Set.Finite.mem_toFinset _).2 ⟨v, hq, rfl⟩)

theorem finite_above (p : ℕ) :
    ({v : HeightOneSpectrum ℤ | v.asIdeal = Ideal.span {(p : ℤ)}} : Set (HeightOneSpectrum ℤ)).Finite :=
  Set.Subsingleton.finite fun v hv w hw => HeightOneSpectrum.ext (hv.trans hw.symm)

theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh]

theorem sh_sh {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_unit {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h : sh G β * sh G ((β⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  rw [hβ] at h
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * sh G ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]


end GlobalTheory.LocTriv
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
end
