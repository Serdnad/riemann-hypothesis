module

public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetRect :
    ∀ (n d d' : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (E' : Fin n → Fin n → Matrix (Fin d') (Fin d') ℂ)
      (A : Matrix (Fin d) (Fin d') ℂ), (∀ a b, E a b * A = A * E' a b) → ∀ u : ℂ, Formalism.REAL.qdet E u * A = A * Formalism.REAL.qdet E' u := by
  intro n d d' E E' A h u
  have hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A = A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hT : ∀ (v : ℂ) a b, Formalism.REAL.Tm E v a b * A = A * Formalism.REAL.Tm E' v a b := by
    intro v a b
    simp only [Formalism.REAL.Tm]
    rw [Matrix.add_mul, Matrix.mul_add, h]
    split_ifs
    · rw [hs]
    · rw [Matrix.zero_mul, Matrix.mul_zero]
  have hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ),
      (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod := by
    intro m
    induction m with
    | zero => intro f g _; simp
    | succ m ih =>
      intro f g hfg
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc,
        ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]
  have hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ) := by
    intro z
    rw [← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)), ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]
    exact hs _
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.subMat :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (S : Submodule ℂ (Fin d → ℂ)),
      (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        d' = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ (∀ y, ρ' y = B * ρ y * A) ∧ ∀ y, ρ y * A = A * ρ' y := by
  intro G _ d ρ S hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let b := Module.finBasis ℂ S
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl S T hT
  let I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hIP : ∀ v, v ∈ S → I (P v) = v := by
    intro v hv
    have e : S.linearProjOfIsCompl T hT v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩
    show ((b.equivFun.symm (b.equivFun (S.linearProjOfIsCompl T hT v)) : S) : Fin d → ℂ) = v
    rw [e, LinearEquiv.symm_apply_apply]
  have hPI : P ∘ₗ I = LinearMap.id := by
    apply LinearMap.ext
    intro w
    have e : S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w :=
      Submodule.linearProjOfIsCompl_apply_left hT _
    show b.equivFun (S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w
    rw [e, LinearEquiv.apply_symm_apply]
  let A := LinearMap.toMatrix' I
  let B := LinearMap.toMatrix' P
  have hAw : ∀ w, A *ᵥ w = I w := fun w => LinearMap.toMatrix'_mulVec I w
  have hBw : ∀ v, B *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]
  have key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M := by
    intro M hM
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw,
      hIP _ (hM w)]
  have hAS : ∀ w, A *ᵥ w ∈ S := by
    intro w
    rw [hAw]
    exact (b.equivFun.symm w).2
  have hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S := by
    intro y w
    rw [← Matrix.mulVec_mulVec]
    exact hS y _ (hAS w)
  let ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => B * ρ y * A
      map_one' := by simp only [map_one, Matrix.mul_one, hBA]
      map_mul' := by
        intro x y
        simp only [map_mul, Matrix.mul_assoc]
        rw [key _ (hcol y)] }
  refine ⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩
  show ρ y * A = A * (B * ρ y * A)
  rw [Matrix.mul_assoc B, key _ (hcol y)]
end

section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ)
        = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_setOf_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (by
            intro a b h
            apply Subtype.ext
            ext i
            have := congrArg Fin.val (congrFun h i)
            simpa using this)
    _ = (N + 1) ^ (n * n) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]
end
