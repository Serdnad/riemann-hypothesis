module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem facts (eqv : n ≃ m) (I : Matrix m m ℂ) (hI : I * I = 1) (G : Matrix n n ℂ) (e : ℂ) (he : e * e = 1)
    (A : Matrix n m ℂ) (hA : Aᴴ * (e • G) * A = I) (c : Matrix m n ℂ) (hc : c = I * Aᴴ * (e • G)) :
    c * A = 1 ∧ A * c = 1 ∧ (cᴴ * c).PosDef ∧ (cᴴ * c) * G⁻¹ * (cᴴ * c) = G ∧
    (∀ a ai : Matrix n n ℂ, a * ai = 1 → aᴴ * G * a = G →
      (a * A)ᴴ * (e • G) * (a * A) = I ∧ I * (a * A)ᴴ * (e • G) = c * ai ∧
      (c * (a * A))ᴴ * I * (c * (a * A)) = I ∧
      ((c * (a * A))ᴴ * (c * (a * A)) = 1 ↔ aᴴ * (cᴴ * c) * a = cᴴ * c)) ∧
    ∀ A' : Matrix n m ℂ, A'ᴴ * (e • G) * A' = I → (A' * c)ᴴ * G * (A' * c) = G := by
  have hee : ∀ X : Matrix n n ℂ, e • e • X = X := fun X => by rw [smul_smul, he, one_smul]
  have h1 : c * A = 1 := by
    calc c * A = I * (Aᴴ * (e • G) * A) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, hI]
  have h2 : A * c = 1 := (Matrix.mul_eq_one_comm_of_equiv eqv.symm).1 h1
  have h1h : Aᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2h : cᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hS : cᴴ * I * c = e • G := by
    calc cᴴ * I * c = cᴴ * (Aᴴ * (e • G) * A) * c := by rw [hA]
      _ = (cᴴ * Aᴴ) * (e • G) * (A * c) := by simp only [Matrix.mul_assoc]
      _ = e • G := by rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
  have hSX : (e • G) * (A * I * Aᴴ) = 1 := by
    calc (e • G) * (A * I * Aᴴ) = cᴴ * I * (c * A) * I * Aᴴ := by
          rw [← hS]; simp only [Matrix.mul_assoc]
      _ = cᴴ * (I * I) * Aᴴ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hI, Matrix.mul_one, h2h]
  have hGX : G * (e • (A * I * Aᴴ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul]; exact hSX
  have hGinv : G⁻¹ = e • (A * I * Aᴴ) := Matrix.inv_eq_right_inv hGX
  have hc_inj : Function.Injective c.mulVec := by
    intro v w hvw
    have := congrArg A.mulVec hvw
    simpa [Matrix.mulVec_mulVec, h2] using this
  refine ⟨h1, h2, Matrix.PosDef.conjTranspose_mul_self c hc_inj, ?_, ?_, ?_⟩
  · calc (cᴴ * c) * G⁻¹ * (cᴴ * c) = e • (cᴴ * (c * A) * I * (Aᴴ * cᴴ) * c) := by
          rw [hGinv, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = e • (cᴴ * I * c) := by rw [h1, h1h, Matrix.mul_one, Matrix.mul_one]
      _ = G := by rw [hS, hee]
  · intro a ai hai ha
    have hia : ai * a = 1 := mul_eq_one_comm.1 hai
    have hSa : aᴴ * (e • G) * a = e • G := by rw [Matrix.mul_smul, Matrix.smul_mul, ha]
    have haS : aᴴ * (e • G) = (e • G) * ai := by
      calc aᴴ * (e • G) = aᴴ * (e • G) * (a * ai) := by rw [hai, Matrix.mul_one]
        _ = (aᴴ * (e • G) * a) * ai := by simp only [Matrix.mul_assoc]
        _ = (e • G) * ai := by rw [hSa]
    have hform : (a * A)ᴴ * (e • G) * (a * A) = I := by
      calc (a * A)ᴴ * (e • G) * (a * A) = Aᴴ * (aᴴ * (e • G) * a) * A := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hSa, hA]
    refine ⟨hform, ?_, ?_, ?_⟩
    · calc I * (a * A)ᴴ * (e • G) = I * Aᴴ * (aᴴ * (e • G)) := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = c * ai := by rw [haS, hc]; simp only [Matrix.mul_assoc]
    · calc (c * (a * A))ᴴ * I * (c * (a * A)) = (a * A)ᴴ * (cᴴ * I * c) * (a * A) := by
            rw [conjTranspose_mul c]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hS, hform]
    · have hu : (c * (a * A))ᴴ * (c * (a * A)) = Aᴴ * (aᴴ * (cᴴ * c) * a) * A := by
        rw [conjTranspose_mul c, conjTranspose_mul a]; simp only [Matrix.mul_assoc]
      rw [hu]
      constructor
      · intro h
        calc aᴴ * (cᴴ * c) * a = (cᴴ * Aᴴ) * (aᴴ * (cᴴ * c) * a) * (A * c) := by
              rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
          _ = cᴴ * (Aᴴ * (aᴴ * (cᴴ * c) * a) * A) * c := by simp only [Matrix.mul_assoc]
          _ = cᴴ * c := by rw [h, Matrix.mul_one]
      · intro h
        calc Aᴴ * (aᴴ * (cᴴ * c) * a) * A = (Aᴴ * cᴴ) * (c * A) := by
              rw [h]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1h, h1, Matrix.one_mul]
  · intro A' hA'
    have hX : e • ((A' * c)ᴴ * G * (A' * c)) = e • G := by
      calc e • ((A' * c)ᴴ * G * (A' * c)) = cᴴ * (A'ᴴ * (e • G) * A') * c := by
            rw [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
        _ = e • G := by rw [hA', hS]
    calc (A' * c)ᴴ * G * (A' * c) = e • e • ((A' * c)ᴴ * G * (A' * c)) := (hee _).symm
      _ = G := by rw [hX, hee]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply]

theorem cinv_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ A hA
  have he : ((C.eps τ : ℝ) : ℂ) * ((C.eps τ : ℝ) : ℂ) = 1 := by
    have h := C.eps_sq τ
    rw [← Complex.ofReal_mul, ← pow_two, h, Complex.ofReal_one]
  exact Adapted.facts finSumFinEquiv.symm (sgI j j') (sgI_mul_self j j') (C.gr τ) ((C.eps τ : ℝ) : ℂ) he A hA
    (C.cinv A τ) rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks

variable {j j' : ℕ}

theorem blocks_eqs (u : Matrix (Sg j j') (Sg j j') ℂ) (h : IsSgU u) :
    u.toBlocks₁₁ᴴ * u.toBlocks₁₁ - u.toBlocks₂₁ᴴ * u.toBlocks₂₁ = 1 ∧
    u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ = -1 ∧
    u.toBlocks₁₁ᴴ * u.toBlocks₁₂ - u.toBlocks₂₁ᴴ * u.toBlocks₂₂ = 0 := by
  have hu : u = fromBlocks u.toBlocks₁₁ u.toBlocks₁₂ u.toBlocks₂₁ u.toBlocks₂₂ :=
    (fromBlocks_toBlocks u).symm
  generalize u.toBlocks₁₁ = a at hu ⊢
  generalize u.toBlocks₁₂ = b at hu ⊢
  generalize u.toBlocks₂₁ = c at hu ⊢
  generalize u.toBlocks₂₂ = d at hu ⊢
  subst hu
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h4
  · simpa [sub_eq_add_neg] using h2

theorem det_unit_of_eq {m k : ℕ} {x : Matrix (Fin m) (Fin m) ℂ} {y : Matrix (Fin k) (Fin m) ℂ}
    (e : xᴴ * x = 1 + yᴴ * y) : IsUnit x.det := by
  have pd : (xᴴ * x).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self y)
  have hu : IsUnit (xᴴ * x).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) :
    moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem one_sub_mul_eq {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (ha : IsUnit a.det) (hd : IsUnit d.det) (h2 : bᴴ * b - dᴴ * d = -1)
    (h3 : aᴴ * b - cᴴ * d = 0) :
    (1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ) = 1 := by
  have hab : aᴴ * b = cᴴ * d := sub_eq_zero.1 h3
  have haH : IsUnit aᴴ.det := by
    rw [det_conjTranspose]; exact ha.star
  have hdH : IsUnit dᴴ.det := by
    rw [det_conjTranspose]; exact hd.star

  have hWH : (c * a⁻¹)ᴴ * d = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, ← hab,
      Matrix.nonsing_inv_mul_cancel_left _ _ haH]
  have hWH' : dᴴ * (c * a⁻¹) = bᴴ := by
    have := congrArg conjTranspose hWH
    simpa [conjTranspose_mul] using this
  have hdd : dᴴ * d = 1 + bᴴ * b := by
    rw [← sub_eq_zero]
    have : bᴴ * b - dᴴ * d + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel

  have key : dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ)) = dᴴ * 1 := by
    calc dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ))
        = (dᴴ * d - (dᴴ * (c * a⁻¹)) * ((c * a⁻¹)ᴴ * d)) * dᴴ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = dᴴ * 1 := by
          rw [hWH, hWH', hdd]; simp
  have := congrArg (fun x => (dᴴ)⁻¹ * x) key
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hdH] using this

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks


open GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.sgU_blocks : ∀ (j j' : ℕ) (u : Matrix (Sg j j') (Sg j j') ℂ), IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef := by
  open GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks in
  intro j j' u hu
  obtain ⟨h1, h2, h3⟩ := blocks_eqs u hu
  have ha : IsUnit u.toBlocks₁₁.det := by
    refine det_unit_of_eq (y := u.toBlocks₂₁) ?_
    rw [← h1]; abel
  have hd : IsUnit u.toBlocks₂₂.det := by
    refine det_unit_of_eq (y := u.toBlocks₁₂) ?_
    rw [← sub_eq_zero]
    have : u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel
  have hm : (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 := by
    rw [moebW_zero]
    exact one_sub_mul_eq ha hd h2 h3
  refine ⟨ha, hd, hm, ?_⟩
  have hpd : (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ).PosDef := by
    have h := Matrix.PosDef.one.mul_mul_conjTranspose_same (B := u.toBlocks₂₂)
      (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hd))
    simpa using h
  have he : 1 - moebW u 0 * (moebW u 0)ᴴ = (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ)⁻¹ :=
    (Matrix.inv_eq_left_inv hm).symm
  rw [he]
  exact hpd.inv
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem IsSgU.det_toBlocks₁₁_ne_zero {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u.toBlocks₁₁.det ≠ 0 := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, u = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  rw [toBlocks_fromBlocks₁₁]
  unfold IsSgU sgI at hu
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hu
  have h := (fromBlocks_inj.1 hu).1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg] at h
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : -(Cᴴ *ᵥ (C *ᵥ v)) = v := by
    have h2 := congrArg (fun M => M *ᵥ v) h
    simp only [Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hAv,
      Matrix.mulVec_zero, zero_add] at h2
    exact h2
  have h3 : star v ⬝ᵥ v = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ (-(Cᴴ *ᵥ (C *ᵥ v))) := by rw [h1]
      _ = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
        rw [dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have h4 : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  have h5 : 0 ≤ star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := dotProduct_star_self_nonneg _
  have h6 : star v ⬝ᵥ v = 0 := le_antisymm (by rw [h3]; exact neg_nonpos.2 h5) h4
  exact hv (dotProduct_star_self_eq_zero.1 h6)

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) : moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem continuous_matrix_inv {X m : Type} [TopologicalSpace X] [Fintype m] [DecidableEq m]
    {A : X → Matrix m m ℂ} (hA : Continuous A) (hd : ∀ x, (A x).det ≠ 0) :
    Continuous fun x => (A x)⁻¹ := by
  have h : (fun x => (A x)⁻¹) = fun x => ((A x).det)⁻¹ • (A x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hA.matrix_det.inv₀ hd).smul hA.matrix_adjugate

theorem continuous_moebBall_zero (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hc : ∀ τ, Continuous fun x => f x τ) (hu : ∀ x τ, IsSgU (f x τ)) :
    Continuous fun x => moebBall q (f x) 0 := by
  have hb : ∀ τ, (ballMat q 0 τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  refine continuous_pi fun k => ?_
  simp only [moebBall, ballPt, hb, moebW_zero]
  set τ := (q.symm k).1
  have h11 : Continuous fun x => (f x τ).toBlocks₁₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have h21 : Continuous fun x => (f x τ).toBlocks₂₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have hm := h21.matrix_mul (continuous_matrix_inv h11 fun x => (hu x τ).det_toBlocks₁₁_ne_zero)
  exact hm.matrix_elem _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)


open Classical in
theorem perExt_I_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.perExt R (Pi.single τ (Complex.I • y)) = Complex.I • C.perExt R (Pi.single τ y) := by
  ext k
  have hk := congrFun h k
  simp only [LatEmb.pBar, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hk ⊢
  linear_combination (-2 * Complex.I) * hk +
    ((C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I


open Classical in
theorem pPart_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.pPart R τ y = C.perExt R (Pi.single τ y) := by
  have h1 := perExt_I_of_pBar C R h
  ext k
  simp only [LatEmb.pPart, h1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-(1 / 2 : ℂ) * (C.perExt R (Pi.single τ y)) k) * Complex.I_mul_I


open Classical in
theorem Fm_single (τ : Ψ) (y x : Fin (j + j') → ℂ) :
    C.Fm (Pi.single τ y) (Pi.single τ x) =
      2 * (embOf (F.σ τ) C.xi * (star x ⬝ᵥ (C.gr τ *ᵥ y))).re := by
  unfold LatEmb.Fm
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem xi_block {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (x y : Fin j' → ℂ) :
    embOf (F.σ τ) C.xi * (star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ Sum.elim 0 y))) =
      -(Complex.I * (C.c : ℂ) * (star x ⬝ᵥ y)) := by
  have hs : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) = -(star x ⬝ᵥ y) := by
    have h1 : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) =
        star (Sum.elim 0 x : Sg j j' → ℂ) ⬝ᵥ (((A τ)ᴴ * C.sgr τ * A τ) *ᵥ Sum.elim 0 y) := by
      rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.dotProduct_mulVec]
    rw [h1, hA.unit τ]
    simp only [sgI, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec]
  have hg : C.sgr τ = ((C.eps τ : ℝ) : ℂ) • C.gr τ := rfl
  rw [hg, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hs
  rw [C.xi_eq τ]
  push_cast
  linear_combination (Complex.I * (C.c : ℂ)) * hs

theorem gram_last_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), (∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y') → C.IsAdapted R A → ∀ (τ : Ψ) (x y : Fin j' → ℂ), R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y) := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A hF hA τ x y
  have hx := pPart_of_pBar C R (hA.kerBar τ x)
  have hy := pPart_of_pBar C R (hA.kerBar τ y)
  have hiy := perExt_I_of_pBar C R (hA.kerBar τ y)
  have h1 := hF (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  have h2 := hF (Pi.single τ (Complex.I • (A τ *ᵥ Sum.elim 0 y))) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  rw [Fm_single, xi_block C R hA] at h1
  rw [Fm_single, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_left_comm, xi_block C R hA, hiy,
    smul_dotProduct, smul_eq_mul] at h2
  rw [RiemLat.ip, hx, hy]
  set H := C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) ⬝ᵥ
    R.Hm *ᵥ star (C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 x))) with hH
  set w := star x ⬝ᵥ y with hw
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic

theorem conj_unitary {ι : Type} [Fintype ι] (M G : Matrix ι ι ℂ)
    (h : (M.map (starRingEnd ℂ))ᵀ * G.map (starRingEnd ℂ) * M = G.map (starRingEnd ℂ)) :
    (M.map (starRingEnd ℂ))ᴴ * G * M.map (starRingEnd ℂ) = G := by
  have h2 := congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (G.map (starRingEnd ℂ)).map (starRingEnd ℂ) = G := by ext i k; simp
  have e2 : ((M.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ := by
    ext i k; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h2
  exact h2

theorem tm_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp [Matrix.map_mul]
  · intro τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp
  · intro a τ
    have hm := mem_archUnitary.1 a.2 (plc F τ)
    simp only [LatEmb.tm, tauMat, LatEmb.gr]
    by_cases h0 : (plc F τ).embedding = embOf (F.σ τ)
    · rw [if_pos h0]
      rw [gramAt, h0] at hm
      have e : ((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)ᴴ =
          (((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map
            (starRingEnd ℂ))ᵀ := by
        ext i k; simp [Matrix.conjTranspose_apply]
      rw [e]
      exact hm
    · have h' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
        (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h0
      rw [if_neg h0]
      apply conj_unitary
      have e : gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) =
          ((gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))).map (starRingEnd ℂ) := by
        rw [gramAt, h']
        ext i k
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e] at hm
      exact hm
  · intro τ
    simp only [LatEmb.tm, tauMat]
    have hc : Continuous fun a : C.Arch =>
        ((a.1 (plc F τ) : GL _ ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) :=
      Units.continuous_val.comp ((continuous_apply (plc F τ)).comp continuous_subtype_val)
    split_ifs with h
    · exact hc
    · exact hc.matrix_map Complex.continuous_conj

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic
end
end
