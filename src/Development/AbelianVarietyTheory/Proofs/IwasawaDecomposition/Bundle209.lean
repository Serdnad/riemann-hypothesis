module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameFunctionActionHolomorphicExtremalLowest
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasis
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), IsHolFam (fun _ => allPos n) fockL (vact lam) ∧ IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧ (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  first | exact @GlobalTheory.JointHarm.vact_isHolFam_isBotFam | exact GlobalTheory.JointHarm.vact_isHolFam_isBotFam | (intros; apply GlobalTheory.JointHarm.vact_isHolFam_isBotFam <;> assumption)
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift.BilFischer

variable {σ : Type} [Fintype σ]

def wt (α : σ →₀ ℕ) : ℂ := ∏ v, ((α v).factorial : ℂ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

theorem wt_add_single (α : σ →₀ ℕ) (v : σ) : wt (α + Finsupp.single v 1) = wt α * ((α v : ℂ) + 1) := by
  classical
  unfold wt
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ (fun x => ((α x).factorial : ℂ)) (Finset.mem_univ v)]
  have h3 : ∏ x ∈ Finset.univ.erase v, (((α + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ Finset.univ.erase v, ((α x).factorial : ℂ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def pair : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun α => wt α • lcoeff ℂ α

theorem pair_monomial_one (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α 1) Q = wt α * AddMonoidAlgebra.coeff Q α := by
  have := (basisMonomials σ ℂ).constr_basis ℂ (fun α => wt α • lcoeff ℂ α) α
  rw [coe_basisMonomials] at this
  unfold pair
  rw [this]
  simp

theorem pair_monomial (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α c) Q = c * (wt α * AddMonoidAlgebra.coeff Q α) := by
  have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, pair_monomial_one, smul_eq_mul]

theorem pair_mul_X (P Q : MvPolynomial σ ℂ) (v : σ) : pair (P * X v) Q = pair P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, mul_one, pair_monomial, pair_monomial, coeff_pderiv, wt_add_single]
    ring
  | add P P' h h' => simp only [add_mul, map_add (f := _), LinearMap.add_apply, h, h']

def lin (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, A v w • X w

theorem lin_X (A : σ → σ → ℂ) (v : σ) : lin A (X v) = ∑ w, A v w • X w := by
  simp [lin]

theorem pderiv_lin_X (A : σ → σ → ℂ) (v u : σ) : pderiv v (lin A (X u)) = C (A u v) := by
  classical

  rw [lin_X, map_sum, Finset.sum_eq_single v]
  · simp [smul_eq_C_mul]
  · intro w _ hw
    simp [pderiv_X, Pi.single_apply, hw]
  · simp

theorem pderiv_lin (A : σ → σ → ℂ) (v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv v (lin A Q) = ∑ w, A w v • lin A (pderiv w Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h', smul_add, Finset.sum_add_distrib]
  | mul_X P u h =>
    rw [map_mul, Derivation.leibniz, h, pderiv_lin_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [smul_eq_C_mul, mul_comm]
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem coeff_zero_lin (A : σ → σ → ℂ) (Q : MvPolynomial σ ℂ) : AddMonoidAlgebra.coeff (lin A Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  change constantCoeff (lin A Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h']
  | mul_X P u h => simp [lin_X, map_sum, smul_eq_C_mul]

theorem pair_lin (A : σ → σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pair (lin A P) Q = pair P (lin (fun v w => A w v) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have : lin A (C c) = C c := by simp [lin]
    rw [this, C_apply, pair_monomial, pair_monomial, coeff_zero_lin]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | mul_X P u h =>

    rw [pair_mul_X, pderiv_lin, map_mul, lin_X, Finset.mul_sum, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_smul_comm, map_smul, map_smul, LinearMap.smul_apply, pair_mul_X, h]

theorem pair_nondeg (Q : MvPolynomial σ ℂ) (h : ∀ P, pair P Q = 0) : Q = 0 := by
  ext α
  have := h (monomial α 1)
  rw [pair_monomial_one] at this
  simpa [wt_ne_zero] using this

theorem pair_rep (ℓ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (d : ℕ)
    (h : ∀ α : σ →₀ ℕ, d < α.degree → ℓ (monomial α 1) = 0) : ∃ Q, ∀ P, pair P Q = ℓ P := by
  classical
  have hfin : {α : σ →₀ ℕ | α.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  refine ⟨∑ α ∈ hfin.toFinset, monomial α (ℓ (monomial α 1) / wt α), fun P => ?_⟩
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [pair_monomial, this, map_smul, smul_eq_mul, coeff_sum]
    congr 1
    simp only [coeff_monomial, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hd
    · exact mul_div_cancel₀ _ (wt_ne_zero α)
    · rw [h α (not_le.1 hd), mul_zero]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']

open Classical in
theorem subst_eq_lin {ι : Type} [Fintype ι] {m n : ℕ} (a : ι → Matrix (Fin n) (Fin n) ℂ)
    (b : ι → Matrix (Fin m) (Fin m) ℂ) :
    subst a b = lin fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0 := by
  unfold subst lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v.1, Fintype.sum_prod_type]
  · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

theorem exists_pair (ι : Type) [Fintype ι] (m n : ℕ) :
    ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧
      (∀ a b P Q, B (subst a b P) Q =
        B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧
      ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ),
        (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) →
          ∃ Q, ∀ P, B P Q = ℓ P := by
  refine ⟨pair, pair_nondeg, fun a b P Q => ?_, pair_rep⟩
  rw [subst_eq_lin, subst_eq_lin, pair_lin]
  congr 3
  funext v w
  by_cases h : v.1 = w.1
  · simp [h]
  · simp [h, Ne.symm h]

end GlobalTheory.DefLift.BilFischer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem subalgebra_eq_top_of_irreducible {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (A : Subalgebra ℂ (Module.End ℂ X))
    (h : ∀ U : Submodule ℂ X, (∀ a ∈ A, ∀ x ∈ U, a x ∈ U) → U = ⊥ ∨ U = ⊤) : A = ⊤ := by
  classical
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine eq_top_iff.2 fun f _ => ?_
    rw [Subsingleton.elim f 0]
    exact A.zero_mem
  haveI : IsSimpleModule A X := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun U => ?_ }
    rcases h (U.restrictScalars ℂ) (fun a ha x hx => U.smul_mem (⟨a, ha⟩ : A) hx) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ A X).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ A X).1 h1
  have hscal : ∀ φ : Module.End A X, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  refine eq_top_iff.2 fun f _ => ?_
  let F : Module.End (Module.End A X) X :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ X
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have : f = (r : Module.End ℂ X) :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem piTensor_irreducible {ι κ : Type} [Finite ι] [DecidableEq ι] {H : ι → Type} [∀ i, AddCommGroup (H i)]
    [∀ i, Module ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] (σ : ∀ i, κ → Module.End ℂ (H i))
    (h : ∀ i, ∀ U : Submodule ℂ (H i), (∀ u, ∀ x ∈ U, σ i u x ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule ℂ (⨂[ℂ] i, H i))
    (hU : ∀ i u, ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (σ i u)) x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  cases nonempty_fintype ι
  have hcomp : ∀ (f g : ∀ i, H i →ₗ[ℂ] H i) (x : ⨂[ℂ] i, H i),
      PiTensorProduct.map (fun i => f i ∘ₗ g i) x = PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  have h1 : ∀ i (a : Module.End ℂ (H i)), ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U := by
    intro i
    let A : Subalgebra ℂ (Module.End ℂ (H i)) :=
      { carrier := {a | ∀ x ∈ U,
          PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U}
        mul_mem' := fun {a b} ha hb x hx => by
          have := ha _ (hb x hx)
          rw [← hcomp] at this
          convert this using 3
          funext ρ
          by_cases hρ : ρ = i
          · subst hρ; simp [Module.End.mul_eq_comp]
          · simp [Function.update_of_ne hρ]
        add_mem' := fun {a b} ha hb x hx => by
          rw [PiTensorProduct.map_update_add]
          exact U.add_mem (ha x hx) (hb x hx)
        algebraMap_mem' := fun c x hx => by
          rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
          have : Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (1 : Module.End ℂ (H i)) =
              fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ) := Function.update_eq_self i _
          rw [this, PiTensorProduct.map_id]
          exact U.smul_mem c hx }
    have hA : A = ⊤ := subalgebra_eq_top_of_irreducible A fun W hW =>
      h i W fun u x hx => hW (σ i u) (hU i u) x hx
    intro a
    have : a ∈ A := hA ▸ Algebra.mem_top
    exact this
  have h2 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i) (s : Finset ι), ∀ x ∈ U,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) x ∈ U := by
    intro f s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j s hj ih =>
      intro x hx
      have := h1 j (f j) _ (ih x hx)
      rw [← hcomp] at this
      convert this using 3
      funext ρ
      by_cases hρ : ρ = j
      · subst hρ; simp [hj]
      · simp [hρ]
  have h3 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i), ∀ x ∈ U, PiTensorProduct.map f x ∈ U := by
    intro f x hx
    simpa using h2 f Finset.univ x hx
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hxU, hx⟩ := (Submodule.ne_bot_iff U).1 hne
  let b := fun i => Module.finBasis ℂ (H i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
  have h4 := h3 (fun i => ((b i).coord (p i)).smulRight (v i)) x hxU
  rw [e] at h4
  exact (U.smul_mem_iff hp).1 h4

theorem tensor_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  intro D V S M h _
  classical
  haveI := fun τ => (h τ).1
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  refine ⟨inferInstance, fun x y hxy => e.injective hxy,
    fun τ u => e.symm.toLinearMap ∘ₗ actT M τ (unfr M τ u) ∘ₗ e.toLinearMap, fun τ u x => ?_, fun U hU => ?_⟩
  · rw [← he, ← he]
    simp
  · have := piTensor_irreducible (fun τ (u : Matrix.unitaryGroup (Fin V.rank) ℂ) => (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ))
      (fun τ => (h τ).2.2) (U.map e.toLinearMap) (by
        rintro τ u _ ⟨x, hx, rfl⟩
        refine ⟨_, hU τ u x hx, ?_⟩
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, actT, rep_unfr])
    rcases this with h1 | h1
    · exact Or.inl ((Submodule.map_eq_bot_iff).1 h1)
    · exact Or.inr ((Submodule.map_eq_top_iff).1 h1)

end GlobalTheory.DefLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Classical in
theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add (f := _)]; exact a.add a'
    · simp only [map_add (f := _), Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), c, c']; rfl

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_inner_l2_translate :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ u ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha _ hA u hu f
  obtain ⟨hc, ⟨C, hC⟩, heq⟩ := ha u hu
  have hfi : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have key : (fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ)
      = fun g => ∫ x, ⟪f x, a u (act g x)⟫_ℂ ∂ν := by
    funext g
    rw [L2.inner_def]
    have hm : σ (umat g) u ∈ smSub G (trRep σ P) := by
      exact sigma_mem hP hG hσ hu g.2
    refine integral_congr_ae ?_
    filter_upwards [hA _ hm] with x hx
    rw [hx, heq]
  rw [key]
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hfi.norm.mul_const C) ?_
  · intro g
    refine AEStronglyMeasurable.inner hfi.aestronglyMeasurable ?_
    exact (hc.comp (hact.comp (Continuous.prodMk_right g))).aestronglyMeasurable
  · intro g
    refine Eventually.of_forall fun x => ?_
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · refine Eventually.of_forall fun x => ?_
    exact continuous_const.inner (hc.comp (hact.comp (Continuous.prodMk_left x)))

end GlobalTheory.SmVec
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eq_zero_of_sum_inc_eq_zero_of_sum_dil_eq_zero : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [Fintype k] [DecidableEq k] [Finite W] [AddCommGroup M] [Module ℂ M] (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) → Red res t Λ π → (∀ g : Module.Dual k W, g ≠ 0 → ∃ d : Pr R V k, d.L = Λ ∧ (∀ x ∈ Λ, d.f x = g (π x)) ∧ ∑ᶠ q ∈ {q | Pr.Inc res t d q}, Φ q = 0) → (∀ q : Pr R V k, q.Ok res → q.IsKer Λ → ∑ a : kˣ, Φ (q.dil (a : k)) = 0) → ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Φ q = 0 := by
  first | exact @GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm | exact GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm | (intros; apply GlobalTheory.LevelHecke.eq_zero_of_upSum_of_norm <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E) (eP : HA (AF F) σ J ≃* HA (AF F) σ J₂) (eQ : HA (AF F) σ J' ≃* HA (AF F) σ J₂') (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')), StepData σ J x a B J' → J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) → J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * (Q : Matrix (Fin M) (Fin M) E) → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → (∀ g, FrameRel J J₂ (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) g (eP g)) → (∀ g, FrameRel J' J₂' (Q : Matrix (Fin M) (Fin M) E) g (eQ g)) → StepRel s σ J x a B J' μ μ' → StepData σ J₂ x₂ a B₂ J₂' ∧ StepRel s σ J₂ x₂ a B₂ J₂' (μ.map eP) (μ'.map eQ) := by
  first | exact @GlobalTheory.GaugeEx.stepRel_basis | exact GlobalTheory.GaugeEx.stepRel_basis | (intros; apply GlobalTheory.GaugeEx.stepRel_basis <;> assumption)
end
