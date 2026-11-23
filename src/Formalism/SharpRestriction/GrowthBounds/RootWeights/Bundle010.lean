module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Mathlib.Algebra.Module.Lattice.Full
public import Lemmata.GeneralBFactLeftAltForm.MQ
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle012
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
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem exists_clear_denominators_alt (M : Submodule O W) (y : W) (hy : y ∈ MQ (K := KK O) M) : ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  apply Bl.general_b_fact_left_alt_form.goal1
  exact hy

def latticeInter (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O L :=
  M.comap (L.subtype.restrictScalars O)

theorem latticeInter_isLattice (M : Submodule O W) (hfg : M.FG) (hMQ : MQ (K := KK O) M = ⊤) (L : Submodule (KK O) W) :
    Submodule.IsFullLattice (KK O) (latticeInter M L) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg (KK O) ?_, span_eq_top := ?_ }
  · have hN : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_
    refine (isNoetherian_submodule.1 hN) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · apply top_unique
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)
    have ha' : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ha
    have hx : a • x ∈ latticeInter M L := hax
    have hspan := (Submodule.span (KK O) (latticeInter M L : Set L)).smul_mem
      (algebraMap O (KK O) a)⁻¹ (Submodule.subset_span hx)
    rwa [← algebraMap_smul (KK O) a x, inv_smul_smul₀ ha'] at hspan
end lat

theorem lattice_adapted_basis_exists : LatticeAdaptedBasisExists := by
  intro O _ _ _ W _ _ _ _ _ M hfg hMQ L
  have := latticeInter_isLattice M hfg hMQ L
  have := Submodule.IsLattice.finite (KK O) (latticeInter M L)
  have := Submodule.IsLattice.free (KK O) (latticeInter M L)
  let bO := Module.finBasis O (latticeInter M L)
  refine ⟨_, bO.extendOfIsFullLattice (KK O), fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.extendOfIsFullLattice_apply]
    exact (bO i).2
  · obtain ⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsFullLattice (KK O)) j := by
      refine ⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩
      have h2 := congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2
      refine h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Module.Basis.extendOfIsFullLattice_apply, algebraMap_smul]
    refine ⟨c i, ?_⟩

    rw [hc, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem gl_operator_apply_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glOps K n LL S a b F = glDerivation K LL S a b F := gl_action_eq_derivation LL S a b F

theorem polynomial_gl_commutation (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S c d - glOps K n LL S c d * glOps K n LL S a b =
      (if b = c then glOps K n LL S a d else 0) - (if d = a then glOps K n LL S c b else 0) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F)
    (gl_derivation_lie_bracket (K := K) LL S a b c d)
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, gl_operator_apply_derivation]
  rw [h]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, gl_operator_apply_derivation]

theorem disjoint_letters_commute (LL : Letters ι) (S S' : Set ι) (hd : Disjoint S S') (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b := by
  classical
  have h0 : ⁅glDerivation K LL S a b, glDerivation K LL S' c d⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.commutator_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∉ S' := fun h => (Set.disjoint_left.1 hd) hl h
      simp only [gl_derivation_variable, hl, hl', if_true, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl']
    · simp only [gl_derivation_variable, hl, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl]
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F) h0
  simp only [Derivation.commutator_apply] at h
  simp only [Module.End.mul_apply, gl_operator_apply_derivation]
  exact sub_eq_zero.1 h

theorem gl_operator_union_add (LL : Letters ι) (S S' : Set ι) (hs : S ⊆ S') (a b : Fin n) :
    glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b := by
  classical
  have h0 : glDerivation K LL S' a b = glDerivation K LL S a b + glDerivation K LL (S' \ S) a b := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.add_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∈ S' := hs hl
      simp [gl_derivation_variable, hl, hl']
    · by_cases hl' : l ∈ S' <;> simp [gl_derivation_variable, hl, hl']
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.add_apply, gl_operator_apply_derivation, h0, Derivation.add_apply]

theorem variable_mul_pderiv_monomial {σ : Type} (v w : σ) (m : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
    add_comm (Finsupp.single v 1)]

open Classical in
theorem gl_derivation_monomial (LL : Letters ι) (S : Set ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a b (monomial m c) =
      ∑ l : ι, if l ∈ S then
        (if LL.vec l then monomial (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) (c * (m (l, b) : K))
         else -monomial (m - Finsupp.single (l, a) 1 + Finsupp.single (l, b) 1) (c * (m (l, a) : K)))
      else 0 := by
  simp only [glDerivation, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp only [Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp

theorem multidegree_polarization_move (m : ι × Fin n →₀ ℕ) (l : ι) (a b : Fin n) (h : m (l, b) ≠ 0) (i : ι) :
    multideg (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) i = multideg m i := by
  classical
  unfold multideg
  have hle : ∀ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) ≤ m (i, c) := by
    intro c
    rw [Finsupp.single_apply]
    split_ifs with hc
    · rw [← hc]; exact Nat.one_le_iff_ne_zero.mpr h
    · exact Nat.zero_le _
  have hs : ∑ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) =
      ∑ c : Fin n, (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    by_cases hi : i = l
    · subst hi
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm hi]
  have key : ∀ c : Fin n, (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c)
      + (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c)
      = m (i, c) + (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    intro c
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    have := hle c
    omega
  have hsum := Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => key c)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs] at hsum
  omega

theorem gl_operator_preserves_multidegree (LL : Letters ι) (S : Set ι) (d : ι → ℕ) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ Pol K n d) : glOps K n LL S a b F ∈ Pol K n d := by
  classical

  rw [gl_operator_apply_derivation, F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' : ∀ i, multideg m i = d i := (MvPolynomial.mem_restrictSupport_iff K).1 hF (by simpa using hm)
  rw [gl_derivation_monomial]
  refine Submodule.sum_mem _ fun l _ => ?_
  split_ifs
  · rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, b) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l a b h0, hm']
  · refine Submodule.neg_mem _ ?_
    rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, a) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l b a h0, hm']
  · exact Submodule.zero_mem _

theorem homogeneous_multidegree_findim (d : ι → ℕ) : FiniteDimensional K (Pol K n d) := by
  classical
  have hfin : Set.Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : ι × Fin n => d v.1))).subset ?_
    intro m hm v
    have := hm v.1
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← this]
    exact Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  have : Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := hfin
  exact Module.Finite.of_basis (basisRestrictSupport K {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i})

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_X_pderiv {R : Type*} [CommRing R] {σ : Type*} (v w : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : R)) := by
  rw [pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl,
    monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem v2con_X_pderiv_self {R : Type*} [CommRing R] {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv v (monomial m c) = monomial m (c * (m v : R)) := by
  rw [v2con_X_pderiv]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [tsub_add_cancel_of_le hle]

theorem v2con_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : R) * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply]
  simp only [Int.cast_sum, Finset.sum_mul]

  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>
    simp [h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]

theorem v2con_coeff_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glAct R LL S a a x) m = ((wtS LL S m a : ℤ) : R) * AddMonoidAlgebra.coeff x m := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [v2con_diag, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem monomials_are_weight_vectors : MonomialsAreWeightVectors := by
  intro R _ _ ι _ LL n S
  constructor
  · intro m c
    rw [weightSp, Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    change glAct R LL S a a (monomial m c) - _ = 0
    rw [v2con_diag, smul_monomial, smul_eq_mul, sub_self]
  · intro ν x hx m hm
    rw [weightSp, Submodule.mem_iInf] at hx
    funext a
    have h := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    have h2 := congrArg (AddMonoidAlgebra.coeff · m) h
    change AddMonoidAlgebra.coeff (glAct R LL S a a x) m = _ at h2
    rw [v2con_coeff_diag, MvPolynomial.coeff_smul, smul_eq_mul] at h2
    have hc : AddMonoidAlgebra.coeff x m ≠ 0 := mem_support_iff.mp hm
    have h3 := mul_right_cancel₀ hc h2
    exact_mod_cast h3

theorem v2con_stable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (N : ℕ) (a b : Fin n) (x : MvPolynomial (ι × Fin n) R)
    (hx : x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}) :
    glAct R LL S a b x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
  classical
  rw [mem_restrictSupport_iff] at hx
  have hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N →
      monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m' c' hm'
    rw [mem_restrictSupport_iff]
    intro y hy
    have := Finset.mem_singleton.mp (support_monomial_subset hy)
    subst this
    exact hm'
  have hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N →
      (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈
        restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m c u w hm
    rw [v2con_X_pderiv]
    by_cases h0 : m w = 0
    · simp [h0]
    · apply hmono
      have hle : Finsupp.single w 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have e1 : (m - Finsupp.single w 1).degree + 1 = m.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add (f := _), Finsupp.degree_single] at this
        exact this
      rw [map_add (f := _), Finsupp.degree_single]
      omega

  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hdeg : m.degree ≤ N := hx hm
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  split_ifs
  · exact hterm m _ _ _ hdeg
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hterm m _ _ _ hdeg)
  · exact Submodule.zero_mem _

theorem polynomial_locally_finite : PolynomialLocallyFinite := by
  intro R _ ι _ LL n S x
  classical
  refine ⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩
  · haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} :=
      (Finsupp.finite_of_degree_le x.totalDegree).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport R _)
  · rw [mem_restrictSupport_iff]
    intro m hm
    show m.degree ≤ x.totalDegree
    rw [Finsupp.degree_apply]
    exact le_totalDegree hm
  · intro a b y hy
    exact v2con_stable LL S _ a b y hy

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem weight_components_mem_invariant [CharZero K] (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (s : Finset (Fin n → ℤ)) : ∀ f : (Fin n → ℤ) → V, (∀ mu ∈ s, f mu ∈ weightSp E mu) →
      ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W :=
  _root_.UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant E W hW s

theorem weightSpace_independent [CharZero K] (E : GLOps n K V) : iSupIndep (weightSp E) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv h0 i hi
  have := weight_components_mem_invariant E ⊥ (fun a x hx => by simp [(Submodule.mem_bot K).1 hx]) s v hv (by simp [h0]) i hi
  simpa using this

variable (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)

@[simp] theorem restricted_operator_coe (a b : Fin n) (x : W) : ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

theorem restricted_mem_weightSpace_iff (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isHWV_iff (lam : Fin n → ℤ) (v : W) : IsHWV (restrictStableOperators E W h) lam v ↔ IsHWV E lam (v : V) := by
  unfold IsHWV
  rw [restricted_mem_weightSpace_iff]
  refine and_congr (by simp) (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isGLRep [CharZero K] (hE : IsGLRep E) : IsGLRep (restrictStableOperators E W h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    ext x
    have h1 := congrArg (fun f : Module.End K V => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restricted_operator_coe]
    rw [h1]
    split_ifs <;> simp
  · intro x
    obtain ⟨W0, hfd, hx0, hst⟩ := hE.2.1 (x : V)
    refine ⟨W0.comap W.subtype, ?_, hx0, fun a b y hy => hst a b _ hy⟩
    have h1 : FiniteDimensional K ((W0.comap W.subtype).map W.subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective W.subtype W.injective_subtype (W0.comap W.subtype)).symm
  · rw [eq_top_iff]
    intro x _
    have hx : (x : V) ∈ ⨆ mu, weightSp E mu := by rw [hE.2.2]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
    have hmem := weight_components_mem_invariant E W (fun a => h a a) f.support f (fun mu _ => hf mu)
      (by have : ∑ mu ∈ f.support, f mu = (x : V) := hsum
          rw [this]; exact x.2)
    have hx2 : x = ∑ mu ∈ f.support.attach, (⟨f mu.1, hmem mu.1 mu.2⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only
      rw [Finset.sum_attach f.support (fun mu => f mu)]
      exact hsum.symm
    rw [hx2]
    refine Submodule.sum_mem _ fun mu _ => ?_
    exact Submodule.mem_iSup_of_mem mu.1 ((restricted_mem_weightSpace_iff E W h mu.1 _).2 (hf mu.1))

end Formalism.MainNotions.G.GLWeightTheory
end
end
