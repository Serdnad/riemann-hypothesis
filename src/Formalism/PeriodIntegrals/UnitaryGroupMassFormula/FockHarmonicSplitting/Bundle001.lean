module

public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockInnerSelfReNonneg
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

section

noncomputable section

open MvPolynomial Matrix FockH1Action

namespace PI.FHS

section Sums

variable {σ : Type*}

lemma fockInner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_left]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_left, ih]

lemma fockInner_sum_right {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_right]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_right, ih]

end Sums

variable {p q r s : ℕ}

lemma omE_apply_of_ne {l l' : Ln p q r s} (h : l ≠ l') (P : Pol p q r s) :
    omE l l' P = raiB l (lowB l' P) := by
  rw [FockH1Action.omE, if_neg h, add_zero]; rfl

private theorem raiB_apply_eq_X_mul_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = X m * P := by
  rw [FockH1Action.raiB, if_pos h]; rfl

private theorem raiB_apply_eq_neg_pderiv_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = -(pderiv m P) := by
  rw [FockH1Action.raiB, if_neg (by simp [h])]; rfl

private theorem lowB_apply_eq_pderiv_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = pderiv m P := by
  rw [FockH1Action.lowB, if_pos h]; rfl

private theorem lowB_apply_eq_X_mul_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = X m * P := by
  rw [FockH1Action.lowB, if_neg (by simp [h])]; rfl

lemma omE_adj {l l' : Ln p q r s} (h : linePos l ≠ linePos l') (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = - fockInner P (omE l' l Q) := by
  have hne : l ≠ l' := fun e => h (e ▸ rfl)
  rw [omE_apply_of_ne hne, omE_apply_of_ne (Ne.symm hne)]
  cases hl : FockH1Action.linePos l <;> cases hl' : FockH1Action.linePos l'
  · exact absurd (hl.trans hl'.symm) h
  · rw [lowB_apply_eq_pderiv_of_linePos hl', raiB_apply_eq_neg_pderiv_of_not_linePos hl, lowB_apply_eq_X_mul_of_not_linePos hl, raiB_apply_eq_X_mul_of_linePos hl',
      fockInner_neg_left, fockInner_pderiv, fockInner_pderiv]
  · rw [lowB_apply_eq_X_mul_of_not_linePos hl', raiB_apply_eq_X_mul_of_linePos hl, lowB_apply_eq_pderiv_of_linePos hl, raiB_apply_eq_neg_pderiv_of_not_linePos hl',
      fockInner_neg_right, neg_neg, fockInner_X_mul, fockInner_X_mul]
  · exact absurd (hl.trans hl'.symm) h

lemma omAct_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    omAct p q r s M P = ∑ l, ∑ l', M l l' • omE l l' P := by
  simp [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply]

def Mixed (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → linePos l ≠ linePos l'

lemma omAct_adj (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (hM : Mixed M) (P Q : Pol p q r s) :
    fockInner (omAct p q r s M P) Q = - fockInner P (omAct p q r s Mᴴ Q) := by
  rw [omAct_apply, omAct_apply]
  simp only [fockInner_sum_left, fockInner_sum_right, fockInner_smul_left,
    fockInner_smul_right, Matrix.conjTranspose_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hz : M l l' = 0
  · simp [hz]
  · rw [omE_adj (hM l l' hz), mul_neg]
    rfl

lemma sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [FockH1Action.sameBlock]

lemma isPC_ct {Z : Mat p q} (h : IsPC Z) : IsPC Zᴴ := by
  intro a b hab
  simp [Matrix.conjTranspose_apply, h b a (sameBlock_symm hab)]

lemma fockAct1_eq (Z : Mat p q) :
    fockAct1 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) :=
  rfl

lemma fockAct2_eq (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) :=
  rfl

lemma mixed1 {Z : Mat p q} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hcd : c = d
  · subst hcd
    have hs : ¬ FockH1Action.sameBlock a b := fun hab => hne (by rw [hZ a b hab, zero_mul])
    clear hne hZ
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hcd, mul_zero]) hne

lemma mixed2 {Z : Mat r s} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hab : a = b
  · subst hab
    have hs : ¬ FockH1Action.sameBlock c d := fun hcd => hne (by rw [hZ c d hcd, mul_zero])
    clear hne hZ
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hab, zero_mul]) hne

lemma conjTranspose_kronecker_one (Z : Mat p q) :
    (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s))ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) Zᴴ (1 : Mat r s) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hcd : c = d
  · subst hcd; simp
  · rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne (Ne.symm hcd)]; simp

lemma conjTranspose_one_kronecker (Z : Mat r s) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z)ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Zᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]; simp

theorem fockAct1_adj {Z : Mat p q} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct1 p q r s Z P) Q = - fockInner P (fockAct1 p q r s Zᴴ Q) := by
  rw [fockAct1_eq, fockAct1_eq,
    omAct_adj _ (mixed1 hZ), conjTranspose_kronecker_one]

theorem fockAct2_adj {Z : Mat r s} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct2 p q r s Z P) Q = - fockInner P (fockAct2 p q r s Zᴴ Q) := by
  rw [fockAct2_eq, fockAct2_eq,
    omAct_adj _ (mixed2 hZ), conjTranspose_one_kronecker]

end PI.FHS
end
end

section

noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def FockV (σ : Type*) : Type _ := MvPolynomial σ ℂ

instance : AddCommGroup (FockV σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))

instance : Module ℂ (FockV σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

@[instance_reducible]
def fockCore : InnerProductSpace.Core ℂ (FockV σ) where
  inner P Q := FockH1Action.fockInner (σ := σ) P Q
  conj_inner_symm x y := fockInner_conj (σ := σ) x y
  re_inner_nonneg x := by simpa using fockInner_self_re_nonneg (σ := σ) x
  add_left x y z := fockInner_add_left (σ := σ) x y z
  smul_left x y r := fockInner_smul_left (σ := σ) r x y
  definite _ h := fockInner_self_eq_zero (σ := σ) h

private lemma finiteDimensional_homog' [Fintype σ] (n : ℕ) :
    FiniteDimensional ℂ (FockH1Action.homog σ n) := by
  classical
  first
  | exact inferInstance
  | (let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n)
     have hS : (Set.Icc (0 : σ →₀ ℕ) c).Finite := Set.finite_Icc 0 c
     have hle : FockH1Action.homog σ n ≤ Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c) := by
       intro p hp
       have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
       rw [p.as_sum]
       refine Submodule.sum_mem _ (fun d hd => ?_)
       have hmono : MvPolynomial.monomial d (AddMonoidAlgebra.coeff p d)
           = AddMonoidAlgebra.coeff p d • MvPolynomial.monomial d (1 : ℂ) := by
         first
         | simp [MvPolynomial.smul_monomial]
         | rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
       rw [hmono]
       refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨by first | exact zero_le | exact bot_le | simp, ?_⟩, rfl⟩)
       have hp0 : p ≠ 0 := by
         rintro rfl
         simp at hd
       have htd : p.totalDegree ≤ n := by
         first
         | exact hph.totalDegree_le
         | exact (hph.totalDegree hp0).le
       have hsum : (d.sum fun _ e => e) ≤ n := (MvPolynomial.le_totalDegree hd).trans htd
       intro i
       have h1 : d i ≤ d.sum (fun _ e => e) := by
         by_cases hi : i ∈ d.support
         · exact Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _) hi
         · rw [Finsupp.mem_support_iff, not_not] at hi
           rw [hi]
           exact Nat.zero_le _
       simpa [c] using h1.trans hsum
     haveI : FiniteDimensional ℂ (Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c)) :=
       FiniteDimensional.span_of_finite ℂ (hS.image _)
     exact Submodule.finiteDimensional_of_le hle)



lemma exists_orth [Fintype σ] (K : Submodule ℂ (MvPolynomial σ ℂ)) (n : ℕ)
    (hK : K ≤ FockH1Action.homog σ n) (f : MvPolynomial σ ℂ) :
    ∃ y ∈ K, ∀ x ∈ K, FockH1Action.fockInner x (f - y) = 0 := by
  classical
  haveI : FiniteDimensional ℂ (FockH1Action.homog σ n) := finiteDimensional_homog' n
  have hfin : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hK
  let K' : Submodule ℂ (FockV σ) := K
  haveI : FiniteDimensional ℂ K' := hfin
  letI : NormedAddCommGroup (FockV σ) := (fockCore (σ := σ)).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (FockV σ) := by
    first
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toPreInnerProductSpaceCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ))
  haveI hproj : K'.HasOrthogonalProjection := inferInstance
  let g : FockV σ := f
  let P := K'.orthogonalProjection g
  have hP : ∀ x ∈ K', inner ℂ x (g - (P : FockV σ)) = 0 := by
    first
    | exact K'.orthogonalProjection_inner_eq_zero g
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_orthogonalProjection_mem_orthogonal g) x hx
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_starProjection_mem_orthogonal g) x hx
  have key : ∀ x y : FockV σ, inner ℂ x y = FockH1Action.fockInner (σ := σ) x y := fun _ _ => rfl
  let q : MvPolynomial σ ℂ := (P : FockV σ)
  have hsub : g - (P : FockV σ) = (show FockV σ from f - q) := rfl
  refine ⟨(P : FockV σ), P.2, fun x hx => ?_⟩
  have h1 := hP x hx
  rw [hsub] at h1
  have h2 : FockH1Action.fockInner (σ := σ) x (f - q) = 0 := (key x (f - q)).symm.trans h1
  exact h2

end PI.FHS
end
end
