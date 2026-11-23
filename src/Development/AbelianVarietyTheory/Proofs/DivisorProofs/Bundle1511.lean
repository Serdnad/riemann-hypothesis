module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem quot_mul_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ)
    (t t' : Aˣ) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t' * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht : algebraMap A S ((t⁻¹ : Aˣ) : A) * algebraMap A S (t : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t⁻¹ : Aˣ) : A) * b := by
    calc ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop
        = algebraMap A S ((t⁻¹ : Aˣ) : A) * (((x⁻¹ : Sˣ) : S) * algebraMap A S (t : A) *
            (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [← Algebra.commutes (t : A), ← mul_assoc, ← mul_assoc, ht, one_mul]
      _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((((x⁻¹ : Sˣ) : S) * x) * b *
            ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)) := by
          rw [← hx]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]
  calc ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop
      = x' * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((x' : S) * b * (σ x').unop) := by
        rw [h2]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [hx', ← map_mul, mul_comm, Units.val_mul]

theorem triv_quot : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' →
    ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  intro p _ G R _ _ β x x' t t' hx hx'
  exact ⟨⟨(x' * x⁻¹, t' * t⁻¹), quot_mul_star (starT G.star R) (inC G R β) x x' t t' hx hx'⟩, rfl⟩

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem pair_form_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G P v
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu

  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    rw [P.sym] at h1
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C)
        = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]

  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  ·
    change (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _
    rw [conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]
  ·
    have hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := (Units.isUnit _).map (G.psi v)
    rw [det_mul]
    exact mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero
  ·
    rw [hH]
    calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
          G.psi v P.γ
        = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
            G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
      _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [hgg', mul_one, map_mul, map_mul]
      _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
      _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem finiteAdeleRingAway_nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (AfP p) := by
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(q : ℤ)}
      isPrime := (Ideal.span_singleton_prime hqi.ne_zero).mpr hqi
      ne_bot := by simpa using hqi.ne_zero }
  have hne : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    change Ideal.span {(q : ℤ)} = Ideal.span {(p : ℤ)} at h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
    simp at h
    omega
  exact (AfP.eval (p := p) ⟨v0, hne⟩).toRingHom.domain_nontrivial

theorem pair_toAf_injective {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : Function.Injective (P.toAf x t hx) := by
  haveI := finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [Pair.toAf, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, Prod.map_fst, Prod.map_snd,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem pair_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  intro p _ G P x t hx r z a b h
  exact pair_toAf_injective P x t hx (congrArg Prod.fst h)

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem nrmG_succ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) :
    nrmG θ (r + 1) δ = nrmG θ r δ * (⇑θ)^[r] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem iter_hom_mul {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x y : H) :
    (⇑θ)^[r] (x * y) = (⇑θ)^[r] x * (⇑θ)^[r] y := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_mul, ih]

theorem iter_hom_inv {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x : H) :
    (⇑θ)^[r] x⁻¹ = ((⇑θ)^[r] x)⁻¹ := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_inv, ih]

theorem nrmG_twConj {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H) :
    nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧
      δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  induction r with
  | zero => simp [nrmG]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [nrmG_succ, nrmG_succ, h1, iter_hom_mul, iter_hom_mul,
        iter_hom_inv, Function.iterate_succ_apply]
      group
    · rw [nrmG_succ, map_mul, ← mul_assoc, h2, mul_assoc, ← Function.iterate_succ_apply' (⇑θ), mul_assoc]

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adelic_norm_move : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  intro p _ G β M _ _ j σ hβ a u hu
  let J : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) j.toRatAlgHom
  have hJ : ∀ (r : AfP p) (m : M), J (r ⊗ₜ m) = r ⊗ₜ j m := fun r m => rfl
  have key : ∀ w : AfP p ⊗[ℚ] M, inC G (AfP p) β * (starT G.star (AfP p) (J w)).unop =
      J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom w) * inC G (AfP p) β := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have e2 : J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom (r ⊗ₜ m)) = r ⊗ₜ j (σ m) := rfl
      rw [hJ, e2, starT_tmul]
      show ((1 : AfP p) ⊗ₜ β) * (r ⊗ₜ (G.star (j m)).unop) = (r ⊗ₜ j (σ m)) * ((1 : AfP p) ⊗ₜ β)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact hβ m
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, hx, hy, map_add (f := _), add_mul]
  refine ⟨Units.map J.toMonoidHom u, ?_, ?_⟩
  · show J u * inC G (AfP p) β * (starT G.star (AfP p) (J u)).unop = _
    rw [mul_assoc, key, ← mul_assoc, ← map_mul, hu, hJ]
    show ((1 : AfP p) ⊗ₜ j a) * ((1 : AfP p) ⊗ₜ β) = (1 : AfP p) ⊗ₜ (j a * β)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y hy
    show inC G (AfP p) y * J u = J u * inC G (AfP p) y
    generalize (u : AfP p ⊗[ℚ] M) = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hJ]
      show ((1 : AfP p) ⊗ₜ y) * (r ⊗ₜ j m) = (r ⊗ₜ j m) * ((1 : AfP p) ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hy m]
    | add x z hx hz => rw [map_add (f := _), mul_add, add_mul, hx, hz]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  first
    | (unfold HTGroup.psiR; erw [Algebra.TensorProduct.lift_tmul]; rfl)
    | exact Algebra.TensorProduct.lift_tmul _ _ _ r c

theorem psiR_starT (G : HTGroup p) (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, psiR_tmul, psiR_tmul]
    rw [G.psi_star, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem Pair.gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G P v
  obtain ⟨z, hz⟩ := P.trivR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (P.β : G.C)) = G.psi v (P.β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (P.β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (P.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.LKMid
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

section Generic2

variable {S : Type*} [Ring S]

theorem triv_change (σ : S →+* Sᵐᵒᵖ) (x u : Sˣ) (b : S) :
    ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop =
      x * b * (σ x).unop := by
  have h1 : (σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop
      = x * ((((u⁻¹ : Sˣ) : S) * u) * b * ((σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop)) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Generic2

namespace Pair

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

theorem triv_conj (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ) (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]; rfl
  rw [e, triv_change, hx]

end Pair

end GlobalTheory.LKMid
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isTest_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) ''
      ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_
    fun_prop
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory
end

section

open NumberField MeasureTheory

namespace GlobalTheory.WeilM

theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  classical
  unfold GlobalTheory.ThetaSobolevBase.sumPure
  have hs : ∀ s : Finset (Fin n), MemLp (∑ i ∈ s, GlobalTheory.WeilM.pureA F (f i) (g i)) 2 μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)).add ih
  simpa using hs Finset.univ

end GlobalTheory.WeilM
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.adelic_schwartz_conj_mem : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.ConjSch.conj_mem_schA | exact GlobalTheory.ConjSch.conj_mem_schA | (intros; apply GlobalTheory.ConjSch.conj_mem_schA <;> assumption)
end
