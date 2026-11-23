module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section
namespace GlobalTheory.InducedPBW.Onto

private lemma UgF_mono {p q j k : ℕ} (h : j ≤ k) : UgF p q j ≤ UgF p q k :=
  Submodule.span_mono fun _ ⟨l, hl, hu⟩ => ⟨l, hl.trans h, hu⟩

theorem indF_mono {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : indF act j ≤ indF act k := by
  refine Submodule.span_mono ?_
  rintro z ⟨u, hu, v, rfl⟩
  exact ⟨u, UgF_mono h hu, v, rfl⟩

theorem indFlt_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (k : ℕ) : indFlt act k ≤ indF act k := by
  unfold indFlt
  exact iSup₂_le fun j hj => indF_mono act hj.le

theorem le_indFlt {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂ (f := fun i (_ : i < k) => indF act i) j h

theorem pLin_isHomogeneous {p q : ℕ} (Z : Mat p q) : (pLin Z).IsHomogeneous 1 := by
  unfold pLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun ab _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem prod_pLin_isHomogeneous {p q : ℕ} (l : List (Mat p q)) :
    (l.map pLin).prod.IsHomogeneous l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.length_nil]
    exact MvPolynomial.isHomogeneous_one _ _
  | cons Z l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
    exact (pLin_isHomogeneous Z).mul ih

theorem prod_mem_UgF {p q k : ℕ} (l : List (Mat p q)) (h : l.length ≤ k) :
    (l.map (ugι p q)).prod ∈ UgF p q k := Submodule.subset_span ⟨l, h, rfl⟩

theorem symProd_mem_UgF {p q k m : ℕ} (x : Fin m → Mat p q) (h : m ≤ k) :
    symProd (fun i => ugι p q (x i)) ∈ UgF p q k := by
  unfold symProd
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => ?_)
  have hmem := prod_mem_UgF (k := k) (List.ofFn fun i => x (σ i)) (by rw [List.length_ofFn]; exact h)
  rw [List.map_ofFn] at hmem
  exact hmem

theorem symU_mem_UgF {p q k : ℕ} (f : MvPolynomial (PIx p q) ℂ) (hf : f.IsHomogeneous k) :
    symU p q f ∈ UgF p q k := by

  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = k := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (hf.coeff_eq_zero hne)
  have e : MvPolynomial.monomial d (f.coeff d) =
      f.coeff d • (MvPolynomial.basisMonomials (PIx p q) ℂ) d := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [symU, Module.Basis.constr_basis]
  refine symProd_mem_UgF _ (le_of_eq ?_)
  rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hdeg]
  rfl

private lemma mkQ_tmul_prod_mem_indFlt_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ)
    (l : List (Mat p q)) (hl : l.length ≤ k) (v : V) :
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) ∈ indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  rcases lt_or_eq_of_le hl with hlt | heq
  · refine Submodule.mem_sup_left (le_indFlt act hlt ?_)
    exact Submodule.subset_span ⟨_, prod_mem_UgF l le_rfl, v, rfl⟩
  · subst heq
    have hP : (l.map pLin).prod ∈ homog (PIx p q) l.length :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (prod_pLin_isHomogeneous l)
    have hs : (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈
        (symTens p q V l.length).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
      refine ⟨LinearMap.rTensor V (homog (PIx p q) l.length).subtype
        (TensorProduct.tmul ℂ (⟨_, hP⟩ : homog (PIx p q) l.length) v), LinearMap.mem_range_self _ _, ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hsum := Submodule.add_mem_sup (hc l v) hs
    rw [sub_add_cancel] at hsum
    exact hsum

theorem indF_eq_sup (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ) :
    indF act k = indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨u, hu, v, rfl⟩
    have key : UgF p q k ≤ (indFlt act k ⊔
        (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q))).comap
        ((indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v) := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨l, hl, rfl⟩
      exact mkQ_tmul_prod_mem_indFlt_sup act hc k l hl v
    exact key hu
  · refine sup_le (indFlt_le act k) ?_
    rintro _ ⟨z, ⟨w, rfl⟩, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f v =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact Submodule.subset_span
        ⟨_, symU_mem_UgF f.1 ((MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2), v, rfl⟩
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb

end GlobalTheory.InducedPBW.Onto
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

def twoPYLin (p q : ℕ) : (Fin p → Fin q → ℂ) →ₗ[ℝ] Mat p q where
  toFun C := pY C + pY C
  map_add' B C := by rw [pY_add]; abel
  map_smul' t B := by rw [pY_smul, smul_add]; rfl

def entryLin {p q : ℕ} (a b : Ix p q) : Mat p q →ₗ[ℝ] ℂ where
  toFun M := M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Matrix.Norms.Operator in
theorem contDiff_exp_two_pY_entry (p q : ℕ) (a b : Ix p q) :
    ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => NormedSpace.exp (pY C + pY C) a b) := by
  have h1 : ContDiff ℝ 1 (NormedSpace.exp : Mat p q → Mat p q) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => (pY C + pY C : Mat p q)) :=
    (LinearMap.toContinuousLinearMap (twoPYLin p q)).contDiff
  have h3 : ContDiff ℝ 1 (fun M : Mat p q => M a b) :=
    (LinearMap.toContinuousLinearMap (entryLin a b)).contDiff
  exact h3.comp (h1.comp h2)

theorem hasStrictFDerivAt_exp_two_pY : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  intro p q B h
  have hc : ContDiff ℝ 1 (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) =>
      NormedSpace.exp (pY C + pY C) a b) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_exp_two_pY_entry p q a b
  have hs := hc.contDiffAt.hasStrictFDerivAt_fderiv (x := B) (by simp)
  refine ⟨_, hs, fun C => ?_⟩
  ext a b
  have hl : HasDerivAt (fun t : ℝ => B + t • C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const C).const_add B
  have h1 := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 a) b
  have h3 := h (pY C + pY C) a b
  have e : (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • (pY C + pY C)) a b) =
      fun t : ℝ => NormedSpace.exp (pY (B + t • C) + pY (B + t • C)) a b := by
    funext t
    have e' : pY B + pY B + t • (pY C + pY C) = pY (B + t • C) + pY (B + t • C) := by
      rw [pY_add, pY_smul, smul_add]; abel
    rw [e']
  rw [e] at h3
  exact h2.unique h3

end GlobalTheory.PolarU
end
end

section

namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable def pCoord (p q : ℕ) : (Fin p → Fin q → ℂ) →+ (PIx p q → ℂ) where
  toFun C := fun ab => pY C ab.1.1 ab.1.2
  map_zero' := by
    funext ⟨⟨a, b⟩, h⟩
    cases a <;> cases b <;> simp [pY, pOf]
  map_add' B C := by funext ab; simp [pY_add]

theorem pCoord_apply {p q : ℕ} (C : Fin p → Fin q → ℂ) (ab : PIx p q) :
    pCoord p q C ab = pY C ab.1.1 ab.1.2 := rfl

private lemma pY_inl_inr {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inl i) (Sum.inr j) = C i j := by
  simp [pY, pOf]

private lemma pY_inr_inl {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inr j) (Sum.inl i) = star (C i j) := by
  simp [pY, pOf]

private lemma pY_eq_zero_of_sameBlock {p q : ℕ} (C : Fin p → Fin q → ℂ) (a b : Ix p q)
    (h : sameBlock a b) : pY C a b = 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, pY, pOf]

private lemma not_sameBlock_inl_inr {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inl i : Ix p q) (Sum.inr j) := by
  simp [sameBlock]

private lemma not_sameBlock_inr_inl {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inr j : Ix p q) (Sum.inl i) := by
  simp [sameBlock]

theorem det_sinhc_eq_polarJacobian (p q : ℕ) (Y : Mat p q)
    (hY : ∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) :
    LinearMap.det (sP Y) = polJ Y := by

  set M : Matrix (PIx p q) (PIx p q) ℂ :=
    (sinhcAd Y).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hM

  have hj : ∀ (t : ℝ) (x : Fin p → Fin q → ℂ), pCoord p q (t • x) = (t : ℂ) • pCoord p q x := by
    intro t x
    funext ab
    simp only [pCoord_apply, pY_smul, Pi.smul_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul]

  have hspan : ∀ w : PIx p q → ℂ, ∃ a b : Fin p → Fin q → ℂ,
      w = pCoord p q a + Complex.I • pCoord p q b := by
    intro w
    let u : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
    let v : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
    refine ⟨fun i j => (u i j + star (v i j)) / 2,
      fun i j => -Complex.I * (u i j - star (v i j)) / 2, ?_⟩
    funext ⟨⟨a, b⟩, h⟩
    rcases a with i | j <;> rcases b with j' | i'
    · exact absurd (by simp [sameBlock]) h
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inl_inr]
      apply Complex.ext <;> simp [u] <;> ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inr_inl]
      apply Complex.ext <;> simp [v] <;> ring
    · exact absurd (by simp [sameBlock]) h

  have hinj : ∀ a b : Fin p → Fin q → ℂ,
      pCoord p q a + Complex.I • pCoord p q b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : ∀ i j, a i j + Complex.I * b i j = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
      simpa [pCoord_apply, pY_inl_inr] using this
    have h2 : ∀ i j, star (a i j) + Complex.I * star (b i j) = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
      simpa [pCoord_apply, pY_inr_inl] using this
    have hre : ∀ i j, a i j = 0 ∧ b i j = 0 := by
      intro i j
      have e1 := congrArg Complex.re (h1 i j)
      have e2 := congrArg Complex.im (h1 i j)
      have e3 := congrArg Complex.re (h2 i j)
      have e4 := congrArg Complex.im (h2 i j)
      simp at e1 e2 e3 e4
      constructor <;> apply Complex.ext <;> simp <;> linarith
    exact ⟨funext fun i => funext fun j => (hre i j).1,
      funext fun i => funext fun j => (hre i j).2⟩

  have hS : ∀ x, Matrix.toLin' M (pCoord p q x) = pCoord p q (sP Y x) := by
    intro x
    funext ab
    rw [Matrix.toLin'_apply, pCoord_apply, ← hY x]
    simp only [sAd, Matrix.of_apply, Matrix.mulVec, dotProduct, vecM, hM,
      Matrix.submatrix_apply, pCoord_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun cd : Ix p q × Ix p q => ¬ sameBlock cd.1 cd.2)]
    have hz : ∑ cd : {cd : Ix p q × Ix p q // ¬ ¬ sameBlock cd.1 cd.2},
        sinhcAd Y (ab.1.1, ab.1.2) cd.1 * pY x cd.1.1 cd.1.2 = 0 := by
      apply Finset.sum_eq_zero
      intro cd _
      rw [pY_eq_zero_of_sameBlock x _ _ (not_not.mp cd.2), mul_zero]
    rw [hz, add_zero]
  have key := det_complexification (Fin p → Fin q → ℂ) (PIx p q → ℂ) (pCoord p q) (sP Y)
    (Matrix.toLin' M) hj hspan hinj hS
  rw [LinearMap.det_toLin'] at key
  unfold polJ
  rw [← hM, key, Complex.ofReal_re]

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
end
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one : ∀ (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Matrix (Fin n) (Fin n) ℂ → B), AnalyticAt ℂ f 1 → (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧ (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧ ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1] Rz Z (fun z => fderiv ℂ f z (Y * z)) := by
  first | exact @GlobalTheory.SphJetCalc.leftInvariant_calculus | exact GlobalTheory.SphJetCalc.leftInvariant_calculus | (intros; apply GlobalTheory.SphJetCalc.leftInvariant_calculus <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.fock_polynomial_kFinite_both_members : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), (∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) → ∀ P : Pol p q r s, KFin T1 (fun g => F.π (g, 1)) (F.ι P) ∧ KFin T2 (fun h => F.π (1, h)) (F.ι P) := by
  first | exact @GlobalTheory.FockKFin.kfin_fock | exact GlobalTheory.FockKFin.kfin_fock | (intros; apply GlobalTheory.FockKFin.kfin_fock <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.adjoint_intertwiner_discreteSeries_descends : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : T.G →* (H →L[ℂ] H)), (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ S : D.U.H →L[ℂ] H, (∀ g x, ρ g (S x) = S (D.U.π g x)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : V →ₗ[ℂ] H) (act : Mat p q →ₗ[ℂ] Module.End ℂ V), (∀ P, KFin T (fun g => ρ g) (ι P)) → (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => ρ (T.expt (t • Y)) (ι P)) (ι (act Y P)) 0) → ∃ φ : V →ₗ[ℂ] D.HK.V, (∀ P x, inner ℂ x (D.ι (φ P)) = inner ℂ (S x) (ι P)) ∧ ∀ Z P, φ (act Z P) = D.HK.act Z (φ P) := by
  first | exact @GlobalTheory.AdjDescent.adjoint_descends | exact GlobalTheory.AdjDescent.adjoint_descends | (intros; apply GlobalTheory.AdjDescent.adjoint_descends <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.casimir_number_identity_dualPair : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  first | exact @GlobalTheory.CasimirNumber.casimir_number_identity | exact GlobalTheory.CasimirNumber.casimir_number_identity | (intros; apply GlobalTheory.CasimirNumber.casimir_number_identity <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_unitary_module_quotient_of_invariant_inner : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧ Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by
  first | exact @GlobalTheory.GKQuot.exists_unitary_quotient | exact GlobalTheory.GKQuot.exists_unitary_quotient | (intros; apply GlobalTheory.GKQuot.exists_unitary_quotient <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.fock_Kset_preserves_homogeneous_degree : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q := by
  first | exact @GlobalTheory.FockDegree.Om_Kset_homog | exact GlobalTheory.FockDegree.Om_Kset_homog | (intros; apply GlobalTheory.FockDegree.Om_Kset_homog <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) := by
  first | exact @GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint | exact GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint | (intros; apply GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.inner_coeff_eq_of_isometric_analytic_modules : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  first | exact @GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | exact GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | (intros; apply GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic <;> assumption)
end
