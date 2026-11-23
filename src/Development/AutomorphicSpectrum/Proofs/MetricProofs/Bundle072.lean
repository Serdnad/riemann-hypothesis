module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice

open scoped Matrix

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im)
    (fun a b w => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun c a w => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul,
        Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im := rfl

theorem imForm_smul_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    imForm Hm z (Complex.I • z) = -(ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
  simp [imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]

theorem imForm_injective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Injective (imForm Hm) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have h1 := imForm_smul_I Hm z
  rw [hz] at h1
  have := hpos z h0
  simp at h1
  linarith

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)

theorem exists_symplectic_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  intro g Λ Hm hdisc hspan hH hpos hint hdual
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ (fun x y => k x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
  have hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ) :=
    fun l m => (hk l m).symm
  have hanti : ∀ l m : Λ, Ef m l = - Ef l m := fun l m => by
    apply Int.cast_injective (α := ℝ)
    have h1 := congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)
    simp only [Complex.star_def, Complex.conj_im] at h1
    push_cast
    rw [hE, hE, imForm_apply, imForm_apply]
    exact h1.symm
  have halt : Ef.IsAlt := fun l => by
    have := hanti l l
    omega
  have hinj : Function.Injective Ef := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro l hl
    have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤
        LinearMap.ker (imForm Hm (l : Fin g → ℂ)) := by
      rw [Submodule.span_le]
      intro m hm
      have := hE l ⟨m, hm⟩
      rw [hl] at this
      simpa using this.symm
    rw [hspan] at hle
    have h0 : imForm Hm (l : Fin g → ℂ) = 0 := LinearMap.ext fun y => hle (Submodule.mem_top)
    exact Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)
  have hsurj : Function.Surjective Ef := by
    intro φ
    let b := Module.finBasis ℤ Λ
    let bR := b.ofZLatticeBasis ℝ Λ
    let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ := bR.constr ℝ fun i => (φ (b i) : ℝ)
    have hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ) := by
      intro y
      have hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ) := fun i => by
        have h := bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i
        rwa [show bR i = (b i : Fin g → ℂ) by simp [bR]] at h
      conv_lhs => rw [← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr y]

      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, map_zsmul, hb]
      simp
    obtain ⟨w, hw⟩ := imForm_surjective Hm hpos ψ
    have hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ) := fun y => by rw [hw, hψ]
    have hwΛ : w ∈ Λ := hdual w fun l => ⟨φ l, hwy l⟩
    refine ⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℝ)
    rw [hE, hwy]
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank
  have hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ)
      (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ) := fun α β => (hE _ _).symm
  refine ⟨bs, ?_⟩
  have hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0 := fun i j => by
    have := hbs.left_left i j
    simpa using this
  have hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0 := fun i j => by
    have := hbs.right_right i j
    simpa using this
  have hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [this]; split_ifs <;> simp
  rintro (i | i) (j | j)
  · rw [hval, hee]; simp [Matrix.J]
  · rw [hval, hef]
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]
  · rw [hval, hanti, hef]
    by_cases h : i = j
    · subst h; simp [Matrix.J]
    · simp [Matrix.J, h, Ne.symm h, Matrix.one_apply]
  · rw [hval, hff]; simp [Matrix.J]

end GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NformRed

open scoped Matrix

variable {g : ℕ}

theorem hermForm_sum_left {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a : κ → ℤ)
    (x : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) w = ∑ i, (a i : ℂ) * hermForm Hm (x i) w := by
  simp only [hermForm, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, zsmul_eq_mul]

theorem hermForm_sum_right {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (b : κ → ℤ)
    (y : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ j, b j • y j) = ∑ j, (b j : ℂ) * hermForm Hm z (y j) := by
  have hs : star (∑ j, b j • y j) = ∑ j, b j • star (y j) := by
    simp [star_sum, star_smul]
  simp only [hermForm]
  rw [hs, Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul]

theorem hermForm_sum_sum {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : κ → ℤ)
    (x : κ → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) (∑ j, b j • x j) =
      ∑ i, ∑ j, (a i : ℂ) * (b j : ℂ) * hermForm Hm (x i) (x j) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermForm_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem re_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).re = (m : ℝ) * (n : ℝ) * c.re := by
  simp [Complex.mul_re]

theorem im_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).im = (m : ℝ) * (n : ℝ) * c.im := by
  simp [Complex.mul_im]

theorem congr_apply {κ : Type*} [Fintype κ] (P : Matrix κ κ ℤ) (M : Matrix κ κ ℝ) (α δ : κ) :
    (P.map (Int.cast : ℤ → ℝ) * M * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ =
      ∑ β, ∑ ε, (P α β : ℝ) * (P δ ε : ℝ) * M β ε := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem J_map_int : (Matrix.J (Fin g) ℤ).map (Int.cast : ℤ → ℝ) = Matrix.J (Fin g) ℝ :=
  Matrix.map_J (Fin g) (Int.castRingHom ℝ)

theorem cast_symplectic {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    P.map (Int.cast : ℤ → ℝ) * Matrix.J (Fin g) ℝ * (P.map (Int.cast : ℤ → ℝ))ᵀ =
      Matrix.J (Fin g) ℝ := by
  have h := SymplecticGroup.mem_iff.1 hP
  have h2 := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at h2
  have e : (Int.castRingHom ℝ : ℤ → ℝ) = (Int.cast : ℤ → ℝ) := rfl
  rw [e, J_map_int, Matrix.transpose_map] at h2
  exact h2

theorem left_inv_transpose {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    (-(Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ)) * Pᵀ = 1 := by
  have h := SymplecticGroup.mem_iff.1 hP
  have : Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ * Pᵀ =
      Matrix.J (Fin g) ℤ * (P * Matrix.J (Fin g) ℤ * Pᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, this, h, Matrix.J_squared, neg_neg]

noncomputable def twist {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) : Module.Basis κ ℤ M :=
  b.map (b.equivFun.trans ((Matrix.toLinearEquiv' Pᵀ ⟨Q, h, mul_eq_one_comm.1 h⟩).trans
    b.equivFun.symm))

theorem twist_apply {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) (α : κ) :
    twist b P Q h α = ∑ β, P α β • b β := by
  have h1 : b.equivFun (b α) = Pi.single α 1 := by
    ext j
    simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  simp only [twist, Module.Basis.map_apply, LinearEquiv.trans_apply, h1,
    Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  change (Pᵀ *ᵥ Pi.single α 1) β • b β = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem coe_sum_smul {n : ℕ} {κ : Type*} [Fintype κ] (Λ : Submodule ℤ (Fin n → ℂ)) (v : κ → ℤ)
    (x : κ → Λ) : ((∑ α, v α • x α : Λ) : Fin n → ℂ) = ∑ α, v α • (x α : Fin n → ℂ) := by
  simp [Submodule.coe_sum]

theorem symplectic_reduction_basis :
    ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  intro g _ Λ Hm bs hHm hpos him hsymp hposdef
  set G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
    Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re with hG
  obtain ⟨ρsq, hleast, hle, P, hP, hfirst, hdet⟩ := SymplecticReduction.full g G hsymp hposdef
  have hqf : ∀ v : Fin g ⊕ Fin g → ℤ, qf G (intVec v) =
      (hermForm Hm (∑ α, v α • (bs α : Fin g → ℂ)) (∑ α, v α • (bs α : Fin g → ℂ))).re := by
    intro v
    rw [hermForm_sum_sum, Complex.re_sum]
    simp only [Complex.re_sum, re_int_mul, qf, intVec, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hG, Matrix.of_apply]
    ring
  have hne : ∀ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 → ∑ α, v α • (bs α : Fin g → ℂ) ≠ 0 := by
    intro v hv h0
    apply hv
    have h1 : (∑ α, v α • bs α : Λ) = 0 := by
      apply Subtype.ext
      rw [coe_sum_smul]
      exact h0
    funext α
    exact Fintype.linearIndependent_iff.1 bs.linearIndependent v h1 α
  have hρpos : 0 < ρsq := by
    obtain ⟨v, hv, hval⟩ := hleast.1
    rw [hval, hqf]
    exact hpos _ (hne v hv)
  have hb' : ∀ α, ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ) =
      ∑ β, P α β • (bs β : Fin g → ℂ) := by
    intro α
    rw [twist_apply, coe_sum_smul]
  have hre : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).re =
      (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, congr_apply]
    simp only [Complex.re_sum, re_int_mul, hG, Matrix.of_apply]
  have him' : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, ← cast_symplectic hP, congr_apply]
    simp only [Complex.im_sum, im_int_mul, him]
  refine ⟨twist bs P _ (left_inv_transpose hP), Real.sqrt ρsq, Real.sqrt_pos.2 hρpos, ?_, him', ?_,
    ?_, ?_⟩
  · rw [Real.sq_sqrt hρpos.le]
    exact hle
  · rw [Real.sq_sqrt hρpos.le, hre]
    exact hfirst
  · intro l hl
    rw [Real.sq_sqrt hρpos.le]
    have hv : (fun α => bs.repr l α) ≠ 0 := by
      intro h0
      apply hl
      have : bs.repr l = 0 := by
        ext α
        exact congrFun h0 α
      simpa using this
    have hsum : (l : Fin g → ℂ) = ∑ α, bs.repr l α • (bs α : Fin g → ℂ) := by
      rw [← coe_sum_smul, bs.sum_repr]
    rw [hsum, ← hqf (fun α => bs.repr l α)]
    exact hleast.2 ⟨_, hv, rfl⟩
  · rw [Real.sq_sqrt hρpos.le]
    have : (Matrix.of fun i j : Fin g =>
        (hermForm Hm ((twist bs P _ (left_inv_transpose hP) (Sum.inl i) : Λ) : Fin g → ℂ)
          ((twist bs P _ (left_inv_transpose hP) (Sum.inl j) : Λ) : Fin g → ℂ)).re) =
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁ := by
      ext i j
      simp only [Matrix.of_apply, hre, Matrix.toBlocks₁₁]
    rw [this]
    exact hdet

end GlobalTheory.CompanionTheory.Ar.NformRed
end
