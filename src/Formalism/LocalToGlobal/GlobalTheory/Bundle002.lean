module

public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem glob_companion (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) {a : 𝓞 E} (ha : a ≠ 0) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    globLat g (Λ ⊔ Ideal.span {a} • dl σ J Λ) = globLat g Λ ⊔ Ideal.span {a} • dl σ J (globLat g Λ) := by
  rw [glob_sup hΛ (isLat_smul (hJ _ hΛ) ha), glob_smul (hJ _ hΛ) ha, glob_dl σ J hJ hΛ g hg]

theorem glob_selfdual (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (hsd : dl σ J Λ = Λ) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : dl σ J (globLat g Λ) = globLat g Λ := by
  rw [← glob_dl σ J hJ hΛ g hg, hsd]

theorem hform_mulVec_rect {A : Type} [CommRing A] (τ : A →+* A) (J' : Matrix m m A) (Q : Matrix m n A)
    (x y : n → A) : hform τ J' (Q *ᵥ x) (Q *ᵥ y) = hform τ (cT τ Q * J' * Q) x y := by
  have H : ∀ {p : Type} [Fintype p] (M : Matrix p p A) (a b : p → A),
      ∑ i, ∑ j, a i * M i j * b j = (a ᵥ* M) ⬝ᵥ b := by
    intro p _ M a b
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  unfold Formalism.UG.hform Formalism.UG.cT
  rw [show (∑ i, ∑ j, τ ((Q *ᵥ x) i) * J' i j * (Q *ᵥ y) j)
      = ((fun i => τ ((Q *ᵥ x) i)) ᵥ* J') ⬝ᵥ (Q *ᵥ y) from H _ _ _,
    show (∑ i, ∑ j, τ (x i) * ((Q.map τ)ᵀ * J' * Q) i j * y j)
      = ((fun i => τ (x i)) ᵥ* ((Q.map τ)ᵀ * J' * Q)) ⬝ᵥ y from H _ _ _]
  have hx : (fun i => τ ((Q *ᵥ x) i)) = (fun i => τ (x i)) ᵥ* (Q.map τ)ᵀ := by
    rw [Matrix.vecMul_transpose]
    ext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hx, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

end Formalism.L2.GlobalTheoryTheory.Comp

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

structure Coord (hc : CMData F E) (S : HSpace E) (n : Type) [Fintype n] where
  κ : S.V ≃ₗ[E] (n → E)
  J : Matrix n n E
  form : ∀ x y, S.hT x y = hform (hc.sig : E →+* E) J (κ x) (κ y)

variable {hc : CMData F E} {S : HSpace E}

def Coord.lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (n → E) :=
  L.map ((K.κ : S.V →ₗ[E] (n → E)).restrictScalars (𝓞 E))

theorem Coord.mem_lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) (y : n → E) : y ∈ K.lat L ↔ K.κ.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show K.κ.symm (K.κ x) ∈ L
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, K.κ.apply_symm_apply y⟩

theorem Coord.lat_dual (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) :
    K.lat (Formalism.HermitianLatticesTheory.dual S.hT L) = dl hc.sig K.J (K.lat L) := by
  ext y
  rw [K.mem_lat, Formalism.HermitianLatticesTheory.dualBasic_mem_dual, mem_dl]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    rw [K.form, LinearEquiv.apply_symm_apply] at h1
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
    exact ⟨r, hr⟩
  · intro h x hx
    have h1 := h (K.κ x) ⟨x, hx, rfl⟩
    rw [K.form, LinearEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := h1
    exact Submodule.mem_one.2 ⟨r, hr⟩

theorem Coord.isLat_lat (K : Coord hc S n) {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsFullLattice E L) :
    IsLat (K.lat L) := by
  refine ⟨Module.Finite.iff_fg.2 (hL.fg.map _), ?_⟩
  rw [eq_top_iff]
  intro y _
  have h1 : K.κ.symm y ∈ Submodule.span E (L : Set S.V) := by rw [hL.span_eq_top]; trivial
  have h2 : K.κ (K.κ.symm y) ∈ (Submodule.span E (L : Set S.V)).map (K.κ : S.V →ₗ[E] (n → E)) := ⟨_, h1, rfl⟩
  rw [LinearEquiv.apply_symm_apply, Submodule.map_span] at h2
  exact h2

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨_, Formalism.HermitianLatticesTheory.majDual_star_int r⟩, rfl⟩

end Formalism.L2.GlobalTheoryTheory.Comp

end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem lattice_character_eq (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : GL3Theta.al1 d Λ x = al1 d Λ x := rfl

theorem taylorLogMetric_U1_eq_U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : TaylorLogMetric.U1 Λ x G = U1 Λ x G := by
  funext z
  simp only [TaylorLogMetric.U1, U1, H1]
  congr 2
  ring

theorem is_theta_zero_iff (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.IsTheta0 d Λ G ↔ IsTheta0 d Λ G := by
  unfold GL3Theta.IsTheta0 IsTheta0
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    have hx' := h2 x hx z
    rwa [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z] at hx'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    rw [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]
    exact h2 x hx z

end Formalism.L2.GlobalTheoryTheory

end
end
