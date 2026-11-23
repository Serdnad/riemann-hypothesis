module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MoveMark

section Field

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem exists_emb (pb : PowerBasis F M) (τ : F →+* ℂ) (z : ℂ) (hz : (minpoly F pb.gen).eval₂ τ z = 0) :
    ∃ e : M →+* ℂ, (∀ x, e (algebraMap F M x) = τ x) ∧ e pb.gen = z := by
  letI : Algebra F ℂ := τ.toAlgebra
  have h : Polynomial.aeval z (minpoly F pb.gen) = 0 := hz
  exact ⟨(pb.lift z h : M →ₐ[F] ℂ), fun x => (pb.lift z h).commutes x, pb.lift_gen z h⟩

theorem gen_ind (pb : PowerBasis F M) (q : M → Prop) (h0 : q pb.gen) (h1 : ∀ x, q (algebraMap F M x))
    (h2 : ∀ x y, q x → q y → q (x + y)) (h3 : ∀ x y, q x → q y → q (x * y)) (y : M) : q y := by
  have hy : y ∈ Algebra.adjoin F {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h0
  | algebraMap r => exact h1 r
  | add x y _ _ hx hy => exact h2 x y hx hy
  | mul x y _ _ hx hy => exact h3 x y hx hy

theorem emb_ext (pb : PowerBasis F M) (e e' : M →+* ℂ) (h1 : ∀ x, e (algebraMap F M x) = e' (algebraMap F M x))
    (h0 : e pb.gen = e' pb.gen) : e = e' :=
  RingHom.ext (gen_ind pb (fun y => e y = e' y) h0 h1 (fun x y hx hy => by simp only [map_add (f := _), hx, hy])
    (fun x y hx hy => by simp only [map_mul, hx, hy]))

theorem emb_root (pb : PowerBasis F M) (e : M →+* ℂ) :
    (minpoly F pb.gen).eval₂ (e.comp (algebraMap F M)) (e pb.gen) = 0 := by
  rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

variable [NumberField F] [IsCMField F]

theorem ne_conj (τ : F →+* ℂ) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = τ x)
    (h' : ∀ x, e' (algebraMap F M x) = τ x) : e ≠ ComplexEmbedding.conjugate e' := by
  intro he
  apply IsCMField.complexConj_ne_one F
  ext x
  apply τ.injective
  rw [IsCMField.complexEmbedding_complexConj, ← h' x]
  have := DFunLike.congr_fun he (algebraMap F M x)
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this, h]
  rfl

omit [NumberField F] [IsCMField F] in
theorem place_eq (v w : InfinitePlace F) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = w.embedding x)
    (h' : ∀ x, e' (algebraMap F M x) = v.embedding x) (he : e = e' ∨ e = ComplexEmbedding.conjugate e') : w = v := by
  rw [← w.mk_embedding, ← v.mk_embedding]
  rcases he with he | he
  · congr 1
    ext x
    rw [← h, ← h', he]
  · rw [← InfinitePlace.mk_conjugate_eq v.embedding]
    congr 1
    ext x
    rw [← h, he, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h']

end Field

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add (f := _), MulOpposite.unop_add]

variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

theorem conj_law (P : Pair G) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (σ : M →+* M)
    (hσ : ∀ x : G.F, σ (algebraMap G.F M x) = algebraMap G.F M (IsCMField.complexConj G.F x))
    (hπ : σ pb.gen * pb.gen = ((P.c : ℚ) : M)) (y : M) : (P.β : G.C) * sh G (j y) = j (σ y) * P.β := by
  refine gen_ind pb (fun y => (P.β : G.C) * sh G (j y) = j (σ y) * P.β) ?_ ?_ ?_ ?_ y
  · have h1 : (P.γ : G.C) * j (σ pb.gen) = algebraMap ℚ G.C P.c := by
      rw [← hj, ← map_mul, mul_comm, hπ, IsScalarTower.algebraMap_apply ℚ G.F G.C, ← j.commutes]
      congr 1
      simp
    show (P.β : G.C) * sh G (j pb.gen) = j (σ pb.gen) * P.β
    apply P.γ.isUnit.mul_left_cancel
    rw [hj, ← mul_assoc, P.sim, ← mul_assoc, h1]
  · intro x
    show (P.β : G.C) * sh G (j (algebraMap G.F M x)) = j (σ (algebraMap G.F M x)) * P.β
    rw [hσ, j.commutes, j.commutes, sh, G.star_F, Algebra.commutes]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x + y)) = j (σ (x + y)) * P.β
    rw [map_add (f := _), sh_add, mul_add, hx, hy, map_add (f := _), map_add (f := _), add_mul]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x * y)) = j (σ (x * y)) * P.β
    rw [map_mul, sh_mul, ← mul_assoc, hy, mul_assoc, hx, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y x]

omit [NumberField M] in
theorem comm_law (γ : G.C) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = γ) (y : G.C)
    (hy : y * γ = γ * y) (m : M) : y * j m = j m * y := by
  refine gen_ind pb (fun m => y * j m = j m * y) ?_ ?_ ?_ ?_ m
  · show y * j pb.gen = j pb.gen * y
    rw [hj, hy]
  · intro x
    show y * j (algebraMap G.F M x) = j (algebraMap G.F M x) * y
    rw [j.commutes, Algebra.commutes]
  · intro a b ha hb
    show y * j (a + b) = j (a + b) * y
    rw [map_add (f := _), mul_add, add_mul, ha, hb]
  · intro a b ha hb
    show y * j (a * b) = j (a * b) * y
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem triv_mul_inv (R : Type) [CommRing R] [Algebra ℚ R] (β β' : G.C) (x U : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hU : (U : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R U).unop = inC G R β') (hx : Triv G R β x t) :
    Triv G R β' (x * U⁻¹) t := by
  unfold Triv at hx ⊢
  have h1 : (starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [← hx, ← hU, Units.val_mul, map_mul, MulOpposite.unop_mul]
  calc _ = (x : R ⊗[ℚ] G.C) * (((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * U) * inC G R β *
        ((starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop) *
        (starT G.star R x).unop := by simp only [mul_assoc]
    _ = _ := by rw [h1, Units.inv_mul, mul_one, mul_one]


omit [NumberField M] in
theorem exists_basis (ha : G.a = 1) (P : Pair G) (μ : ℂ) (hm : P.Mark μ) (pb : PowerBasis G.F M)
    (hpol : P.pol = minpoly G.F pb.gen) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (w : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ i x, e i (algebraMap G.F M x) = w.embedding x) ∧ Function.Injective (fun i => e i pb.gen) ∧
      (∀ z : ℂ, P.pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) ∧
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ∧ (∀ i, d i ≠ 0) ∧
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨Z, lam, hinj, hroot, hZ⟩ := GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots p G P w
  have hr : ∀ i, P.pol.eval₂ w.embedding (lam i) = 0 := fun i => (hroot _).2 ⟨i, rfl⟩
  choose e he he' using fun i => exists_emb pb w.embedding (lam i) (hpol ▸ hr i)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P w
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues _ (G.psi w P.γ) ((P.c : ℚ) : ℝ) Z lam h1 h2
    (by exact_mod_cast P.c.ne_zero) (by rw [h3]; simp) hinj
    (fun i => GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm _ _ (hr i)) hZ
  have hl : (fun i => e i pb.gen) = lam := funext he'
  refine ⟨Z, d, e, he, hl ▸ hinj, fun z hz => ?_, fun y => ?_, hd, hD⟩
  · obtain ⟨i, hi⟩ := (hroot z).1 hz
    exact ⟨i, (he' i).trans hi⟩
  · refine gen_ind pb (fun y => G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ?_ ?_ ?_ ?_ y
    · show G.psi w (j pb.gen) * _ = _
      rw [hj, hl, hZ]
    · intro x
      show G.psi w (j (algebraMap G.F M x)) * _ = _
      simp only [he]
      rw [j.commutes, G.psi_F]
      exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
    · intro a b h h'
      show G.psi w (j (a + b)) * _ = _
      simp only [map_add (f := _)]
      rw [Matrix.add_mul, h, h', ← Matrix.mul_add, Matrix.diagonal_add]
    · intro a b h h'
      show G.psi w (j (a * b)) * _ = _
      simp only [map_mul]
      rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

end GlobalTheory.LKMid.MoveMark

namespace GlobalTheory.LKMid

end GlobalTheory.LKMid
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  intro p _ G β hβ y₀ s hy hsep hdeg S
  classical
  set Ec : Subalgebra ℚ G.C := Subalgebra.centralizer ℚ ({(y₀ : G.C)} : Set G.C) with hEc
  have memE : ∀ x : G.C, x ∈ Ec ↔ Commute x (y₀ : G.C) := by
    intro x
    rw [hEc, Subalgebra.mem_centralizer_iff]
    constructor
    · intro h; exact (h (y₀ : G.C) (Set.mem_singleton _)).symm
    · intro h g hg; rw [Set.mem_singleton_iff.1 hg]; exact h.eq.symm
  have hcomm : ∀ a b : Ec, a * b = b * a := fun a b => Subtype.ext
    (GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G y₀ hsep hdeg a b ((memE a).1 a.2) ((memE b).1 b.2)).eq
  letI : CommRing Ec := { (inferInstance : Ring Ec) with mul_comm := hcomm }
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  haveI : FiniteDimensional ℚ Ec := inferInstance
  haveI : IsReduced Ec := ⟨fun x ⟨k, hk⟩ => Subtype.ext (GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly p G y₀ hsep hdeg x ((memE x).1 x.2) k
    (by simpa using congrArg Subtype.val hk))⟩

  have sh_add : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := fun x y => by simp [sh]
  have sh_mul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by simp [sh]
  have sh_one : sh G 1 = 1 := by simp [sh]
  have sh_zero : sh G 0 = 0 := by simp [sh]
  have sh_alg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := fun q => by
    simp only [sh, RingHom.map_rat_algebraMap G.star q, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  have sh_sh : ∀ x, sh G (sh G x) = x := fun x => G.star_star x
  have sh_binv : sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
      rw [← hβ, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : sh G (y₀ : G.C) = 0 := by
      have := congrArg (fun t => ((β⁻¹ : G.Cˣ) : G.C) * (((y₀⁻¹ : G.Cˣ) : G.C) * t)) hy
      simpa [← mul_assoc] using this
    have : (y₀ : G.C) = 0 := by rw [← sh_sh (y₀ : G.C), h0, sh_zero]
    exact y₀.ne_zero this
  have tC_y : (β : G.C) * sh G (y₀ : G.C) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C) := by
    have := congrArg (fun t => ((y₀⁻¹ : G.Cˣ) : G.C) * t * ((β⁻¹ : G.Cˣ) : G.C)) hy
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    rw [this, mul_assoc, Units.mul_inv, mul_one, Algebra.commutes]
  have tC_mul : ∀ x y : G.C, (β : G.C) * sh G (x * y) * ((β⁻¹ : G.Cˣ) : G.C) =
      ((β : G.C) * sh G y * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro x y
    rw [sh_mul]; simp only [mul_assoc, Units.inv_mul_cancel_left]
  have tC_mem : ∀ x : G.C, Commute x (y₀ : G.C) →
      Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (y₀ : G.C) := by
    intro x hx
    have h1 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C)) := by
      rw [← tC_y]
      show _ * _ = _ * _
      rw [← tC_mul, ← tC_mul, hx.eq]
    have h2 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) ((y₀⁻¹ : G.Cˣ) : G.C) := by
      have h3 := h1.smul_right (s⁻¹)
      rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul] at h3
    simpa using h2.units_inv_right

  let τf : Ec → Ec := fun x => ⟨(β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C), (memE _).2 (tC_mem x ((memE x).1 x.2))⟩
  have τf_val : ∀ x : Ec, ((τf x : Ec) : G.C) = (β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := fun x => rfl
  have τf_inv : ∀ x, τf (τf x) = x := by
    intro x; apply Subtype.ext
    rw [τf_val, τf_val, sh_mul, sh_mul, sh_sh, hβ, sh_binv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [Units.mul_inv, mul_one]
  let τa : Ec →ₐ[ℚ] Ec :=
    { toFun := τf
      map_one' := by apply Subtype.ext; rw [τf_val]; simp [sh_one]
      map_mul' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_mul, tC_mul, ← τf_val, ← τf_val, ← Subalgebra.coe_mul, hcomm]
      map_zero' := by apply Subtype.ext; rw [τf_val]; simp [sh_zero]
      map_add' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_add, sh_add, mul_add, add_mul]; rfl
      commutes' := by
        intro q; apply Subtype.ext
        rw [τf_val]
        change (β : G.C) * sh G (algebraMap ℚ G.C q) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C q
        rw [sh_alg, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  have τa_apply : ∀ x, τa x = τf x := fun x => rfl
  let τe : Ec ≃ₐ[ℚ] Ec := AlgEquiv.ofAlgHom τa τa (AlgHom.ext fun x => τf_inv x) (AlgHom.ext fun x => τf_inv x)
  have τe_apply : ∀ x, τe x = τf x := fun x => rfl
  have τe_inv : ∀ x, τe (τe x) = x := fun x => τf_inv x

  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one G.F)
  set jF : G.F := x₁ - IsCMField.complexConj G.F x₁ with hjF
  have hjF0 : jF ≠ 0 := by
    rw [hjF, sub_ne_zero]; intro h; exact hx₁ (by rw [← h]; rfl)
  have hjFc : IsCMField.complexConj G.F jF = -jF := by
    rw [hjF, map_sub, IsCMField.complexConj_apply_apply]; ring
  have cen : ∀ z : G.F, algebraMap G.F G.C z ∈ Ec := fun z => (memE _).2 (Algebra.commutes z (y₀ : G.C))
  let jE : Ec := ⟨algebraMap G.F G.C jF, cen jF⟩
  have hjE : IsUnit jE := by
    have h : jE * ⟨algebraMap G.F G.C jF⁻¹, cen _⟩ = 1 := by
      apply Subtype.ext
      change algebraMap G.F G.C jF * algebraMap G.F G.C jF⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hjF0, map_one]
    exact ⟨⟨jE, _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have hjτ : τe jE = -jE := by
    apply Subtype.ext
    rw [τe_apply, τf_val]
    change (β : G.C) * (G.star (algebraMap G.F G.C jF)).unop * ((β⁻¹ : G.Cˣ) : G.C) = -algebraMap G.F G.C jF
    rw [G.star_F, hjFc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one, map_neg]
  obtain ⟨A', hA'⟩ := GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms Ec τe τe_inv jE hjE hjτ S
  refine ⟨A'.image Subtype.val, ?_⟩
  intro a ha hac hafix hloc

  obtain ⟨ua, rfl⟩ := ha
  have ha' : (ua : G.C) ∈ Ec := (memE _).2 hac
  set a' : Ec := ⟨ua, ha'⟩ with ha'def
  have hinvE : ((ua⁻¹ : G.Cˣ) : G.C) ∈ Ec := (memE _).2 hac.units_inv_left
  have ha'u : IsUnit a' := by
    have h : a' * ⟨_, hinvE⟩ = 1 := Subtype.ext ua.mul_inv
    exact ⟨⟨a', _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have ha'fix : τe a' = a' := Subtype.ext hafix
  have hloc' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : Ec), c ≠ 0 ∧ IsUnit b ∧
      a' = x * (algebraMap ℚ Ec c * (b * τe b)) ∧
      algebraMap ℚ Ec c * (b * τe b) = y * a' ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : Ec) * x) ∧
        IsIntegral ℤ ((d : Ec) * y) := by
    intro ℓ hℓ hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨u, z, hzc, hz⟩ := hloc ℓ hℓS
    obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.tensor_centralizer_injective_commutant_eq ℚ_[ℓ] G.C (y₀ : G.C)
    set ι := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) Ec.val with hι
    have hinCy : inC G ℚ_[ℓ] (y₀ : G.C) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (y₀ : G.C) := rfl
    obtain ⟨w, hw⟩ := hsurj z (hinCy ▸ hzc)
    obtain ⟨w2, hw2⟩ := hsurj ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ) : ℚ_[ℓ] ⊗[ℚ] G.C) (hinCy ▸ hzc.units_inv_left)
    have hww : w * w2 = 1 := hinj (by rw [map_mul, hw, hw2, Units.mul_inv, map_one])
    let Z : (ℚ_[ℓ] ⊗[ℚ] Ec)ˣ := ⟨w, w2, hww, by rw [mul_comm]; exact hww⟩
    set τℓ := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τe.toAlgHom with hτℓ
    have hkey : ∀ t : ℚ_[ℓ] ⊗[ℚ] Ec, ι (τℓ t) = inC G ℚ_[ℓ] (β : G.C) * (starT G.star ℚ_[ℓ] (ι t)).unop *
        inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        rw [hτℓ, hι, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          starT_tmul]
        simp only [inC, AlgHom.id_apply, Subalgebra.coe_val, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rfl
      | add t1 t2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, add_mul]
    have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a' = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] Ec) (u : ℚ_[ℓ]) *
        ((Z : ℚ_[ℓ] ⊗[ℚ] Ec) * τℓ (Z : ℚ_[ℓ] ⊗[ℚ] Ec)) := by
      apply hinj
      rw [map_mul, map_mul, AlgHom.commutes, hkey]
      have hZ : ι (Z : ℚ_[ℓ] ⊗[ℚ] Ec) = z := hw
      rw [hZ, hι, Algebra.TensorProduct.map_tmul]
      change inC G ℚ_[ℓ] (ua : G.C) = _
      rw [hz]
      simp only [mul_assoc]
    obtain ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩ := GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm Ec τe.toAlgHom ℓ a' u Z ha'u heq
    exact ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩
  obtain ⟨a₀, ha₀, r, e, hre⟩ := hA' a' ha'u ha'fix hloc'
  refine ⟨(a₀ : G.C), Finset.mem_image_of_mem _ ha₀, r, Units.map (Ec.val : Ec →* G.C) e, (memE _).1 (e : Ec).2, ?_⟩
  rw [τe_apply] at hre
  have := congrArg Subtype.val hre
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, τf_val] at this
  simpa using this
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem conn_lowerTriangular {n s : ℕ} {T : V n → Matrix (Fin s) (Fin s) ℂ} {x : V n}
    (h0 : ∀ᶠ y in 𝓝 x, ∀ i j, i < j → T y i j = 0) (hd : ∀ i, T x i i ≠ 0) (ξ : V n) :
    (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
  have hT : (T x)ᵀ.BlockTriangular id := fun i j hij => h0.self_of_nhds j i hij
  have hu' : IsUnit (T x)ᵀ.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have hu : IsUnit (T x).det := by rwa [Matrix.det_transpose] at hu'
  have hD : (mdel T x ξ)ᵀ.BlockTriangular id := fun i j hij => by
    rw [Matrix.transpose_apply, mdel_apply,
      del_congr (g := fun _ => (0 : ℂ)) (h0.mono fun y hy => hy j i hij)]
    simp
  letI := Matrix.invertibleOfIsUnitDet _ hu'
  have hc : (conn T x ξ).BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular hT).mul hD
  refine ⟨fun i j hij => hc hij, fun i => ?_⟩
  have h := congrFun (congrFun (transpose_mul_conn hu ξ) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.transpose_apply, Matrix.transpose_apply,
    mdel_apply] at h
  · rw [← h, inv_mul_cancel_left₀ (hd i)]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hT (show id k < id i from hk), zero_mul]
    · rw [hc (show id i < id k from hk), mul_zero]
  · simp

theorem curv_lowerTriangular : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  intro n s T d v hT hd he ξ η
  have h0 : ∀ᶠ y in 𝓝 v, ∀ i j, i < j → T y i j = 0 := he.mono fun _ h => h.1
  have hv : ∀ i, T v i i ≠ 0 := fun i => by
    rw [he.self_of_nhds.2 i]; exact_mod_cast (hd i).ne'
  have hne : ∀ᶠ y in 𝓝 v, ∀ i, T y i i ≠ 0 :=
    eventually_all.2 fun i => (hT i i).continuousAt.eventually_ne (hv i)
  have hc : ∀ᶠ x in 𝓝 v, (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
    filter_upwards [h0.eventually_nhds, hne] with x h1 h2
    exact conn_lowerTriangular h1 h2 ξ
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [curv, Matrix.neg_apply, mdbar_apply,
      dbar_congr (g := fun _ => (0 : ℂ)) (hc.mono fun y hy => hy.1 i j hij)]
    simp
  · let H : V n → Matrix (Fin 1) (Fin 1) ℂ := fun x => Matrix.of fun _ _ => T x i i
    have hH : ∀ᶠ x in 𝓝 v, conn T x ξ i i = conn H x ξ 0 0 := by
      filter_upwards [hc, hne] with x h1 h2
      rw [h1.2 i, (conn_lowerTriangular (T := H)
        (Eventually.of_forall fun _ a b hab => absurd (Subsingleton.elim a b) hab.ne)
        (fun _ => h2 i) ξ).2 0]
      rfl
    have hs : ContDiffAt ℝ 2 (d i) v := by
      have h1 : ContDiffAt ℝ 2 (fun x => (T x i i).re) v :=
        Complex.reCLM.contDiff.contDiffAt.comp v ((hT i i).of_le (by norm_cast))
      refine h1.congr_of_eventuallyEq (he.mono fun x hx => ?_)
      simp [hx.2 i]
    rw [← curv_line (H := H) hs (hd i).ne' (he.mono fun x hx => hx.2 i) ξ η 0 0, curv, curv,
      Matrix.neg_apply, Matrix.neg_apply, mdbar_apply, mdbar_apply, dbar_congr hH]

end GlobalTheory.ChernCalc
end
