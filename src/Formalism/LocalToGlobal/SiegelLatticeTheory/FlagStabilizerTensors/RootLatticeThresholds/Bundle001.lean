module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.Complex.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsGA

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ G) (g : G) :
    (a * b).coeff g = ∑ h : G, a.coeff h * b.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

theorem central_of_class (a : MonoidAlgebra ℂ G) (h : ∀ g P : G, a.coeff (P⁻¹ * g * P) = a.coeff g)
    (y : MonoidAlgebra ℂ G) : a * y = y * a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [coeff_mul_fin, coeff_mul_fin]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight g)) _ _ fun k => ?_
  have e1 : (k⁻¹ * g)⁻¹ * g = g⁻¹ * k * g := by group
  show a.coeff k * y.coeff (k⁻¹ * g) = y.coeff (k⁻¹ * g) * a.coeff ((k⁻¹ * g)⁻¹ * g)
  rw [e1, h k g]
  exact mul_comm _ _

def conjA (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => star (a.coeff g⁻¹))

theorem conjA_coeff (a : MonoidAlgebra ℂ G) (g : G) : (conjA a).coeff g = star (a.coeff g⁻¹) := by
  simp [conjA, MonoidAlgebra.coeff_ofCoeff]

theorem conjA_conjA (a : MonoidAlgebra ℂ G) : conjA (conjA a) = a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, conjA_coeff, inv_inv, star_star]

theorem conjA_mul (a b : MonoidAlgebra ℂ G) : conjA (a * b) = conjA b * conjA a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, coeff_mul_fin, coeff_mul_fin, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  have e1 : ((g * h)⁻¹ * g)⁻¹ = h := by group
  have e2 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
  show star (a.coeff h * b.coeff (h⁻¹ * g⁻¹)) =
    (conjA b).coeff (g * h) * (conjA a).coeff ((g * h)⁻¹ * g)
  rw [conjA_coeff, conjA_coeff, e1, e2, star_mul']
  exact mul_comm _ _

theorem conjA_sub (a b : MonoidAlgebra ℂ G) : conjA (a - b) = conjA a - conjA b := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp [conjA_coeff, MonoidAlgebra.coeff_sub, star_sub]

private theorem eq_zero_of_conjA_mul_self_eq_zero (x : MonoidAlgebra ℂ G) (hx : conjA x * x = 0) :
    x = 0 := by
  have h1 := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hx
  simp only [coeff_mul_fin, conjA_coeff, mul_one, MonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h1
  have h2 : ∑ h : G, ((Complex.normSq (x.coeff h⁻¹) : ℝ) : ℂ) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h2
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun h _ => Complex.normSq_nonneg (x.coeff h⁻¹))).mp h2
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have h4 := h3 g⁻¹ (Finset.mem_univ _)
  rw [inv_inv, Complex.normSq_eq_zero] at h4
  simpa using h4

private theorem eq_mul_of_commuting_idempotents_conjA_swap (e f : MonoidAlgebra ℂ G) (hef : conjA e = f)
    (hfe : conjA f = e) (he : e * e = e) (hf : f * f = f) (hc : f * e = e * f) :
    e = e * f := by
  have hx : conjA (e - e * f) * (e - e * f) = 0 := by
    rw [conjA_sub, conjA_mul, hef, hfe]
    have h1 : f * (e * f) = e * f := by rw [← mul_assoc, hc, mul_assoc, hf]
    have h2 : e * f * e = e * f := by rw [mul_assoc, hc, ← mul_assoc, he]
    have h3 : e * f * (e * f) = e * f := by rw [← mul_assoc, h2, mul_assoc, hf]
    rw [sub_mul, mul_sub, mul_sub, h1, h3, h2, hc]
    simp
  exact sub_eq_zero.mp (eq_zero_of_conjA_mul_self_eq_zero _ hx)

theorem selfadj_of_central_idem (e : MonoidAlgebra ℂ G) (hid : e * e = e) (hc : ∀ y, e * y = y * e) :
    conjA e = e := by
  have hff : conjA e * conjA e = conjA e := by rw [← conjA_mul, hid]
  have h1 := eq_mul_of_commuting_idempotents_conjA_swap e (conjA e) rfl (conjA_conjA e) hid hff
    (hc (conjA e)).symm
  have h2 := eq_mul_of_commuting_idempotents_conjA_swap (conjA e) e (conjA_conjA e) rfl hff hid
    (hc (conjA e))
  calc conjA e = conjA e * e := h2
    _ = e * conjA e := (hc _).symm
    _ = e := h1.symm

end Formalism.L2.SG.Pf.AllRowsGA
end
end

section

noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

section Trace

variable {H' H : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem hsSum_indep {ι κ : Type*} [Fintype ι] [Fintype κ] (b : OrthonormalBasis ι ℂ H') (c : OrthonormalBasis κ ℂ H')
    (A A' : H' →L[ℂ] H) : ∑ i, ⟪A (b i), A' (b i)⟫_ℂ = ∑ k, ⟪A (c k), A' (c k)⟫_ℂ := by

  set e := stdOrthonormalBasis ℂ H
  have h1 : ∀ x : H', ⟪A x, A' x⟫_ℂ = ∑ j, ⟪ContinuousLinearMap.adjoint A' (e j), x⟫_ℂ *
      ⟪x, ContinuousLinearMap.adjoint A (e j)⟫_ℂ := by
    intro x
    rw [← e.sum_inner_mul_inner (A x) (A' x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, mul_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [OrthonormalBasis.sum_inner_mul_inner]

end Trace

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V' : ι → Type*} [∀ i, NormedAddCommGroup (V' i)]
  [∀ i, InnerProductSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']

def tB (t' : (∀ i, V' i) → H') (k : ∀ i, Fin (Module.finrank ℂ (V' i))) : H' :=
  t' (fun i => stdOrthonormalBasis ℂ (V' i) (k i))

theorem tB_orthonormal (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) :
    Orthonormal ℂ (tB t') := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [tB, ht]
  have hs : ∀ i, ⟪stdOrthonormalBasis ℂ (V' i) (k i), stdOrthonormalBasis ℂ (V' i) (l i)⟫_ℂ =
      if k i = l i then 1 else 0 := fun i =>
    orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ (V' i)).orthonormal (k i) (l i)
  simp_rw [hs]
  rw [Finset.prod_boole]
  by_cases h : k = l
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hall
    exact h (funext fun i => hall i (Finset.mem_univ i))

theorem inner_tB_self_sum (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (x : ∀ i, V' i) : ⟪t' x, t' x⟫_ℂ = ∑ k, ⟪t' x, tB t' k⟫_ℂ * ⟪tB t' k, t' x⟫_ℂ := by
  simp only [tB, ht]
  calc ∏ i, ⟪x i, x i⟫_ℂ = ∏ i, ∑ j, ⟪x i, stdOrthonormalBasis ℂ (V' i) j⟫_ℂ *
        ⟪stdOrthonormalBasis ℂ (V' i) j, x i⟫_ℂ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [OrthonormalBasis.sum_inner_mul_inner]
    _ = _ := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.prod_mul_distrib]

theorem mem_span_tB (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (x : ∀ i, V' i) : t' x ∈ Submodule.span ℂ (Set.range (tB t')) := by

  have hon := tB_orthonormal t' ht
  set v := t' x with hv
  set u := ∑ k, ⟪tB t' k, v⟫_ℂ • tB t' k with hu
  have huu : ⟪u, u⟫_ℂ = ∑ k, ⟪v, tB t' k⟫_ℂ * ⟪tB t' k, v⟫_ℂ := by
    rw [hu, hon.inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_conj_symm]
  have hvu : ⟪v, u⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [huu]
    conv_lhs => rw [hu]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, mul_comm]
  have huv : ⟪u, v⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [← inner_conj_symm, hvu, inner_conj_symm]
  have hvv : ⟪v, v⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [huu, hv]
    exact inner_tB_self_sum t' ht x
  have hz : ⟪v - u, v - u⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hvu, huv, hvv]
    ring
  have hvu' : v = u := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  rw [hvu', hu]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

def tONB (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) : OrthonormalBasis (∀ i, Fin (Module.finrank ℂ (V' i))) ℂ H' :=
  OrthonormalBasis.mk (tB_orthonormal t' ht) (by
    rw [← hsp]
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact mem_span_tB t' ht x))

theorem tONB_apply (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) (k : ∀ i, Fin (Module.finrank ℂ (V' i))) :
    tONB t' ht hsp k = tB t' k := by
  unfold tONB
  rw [OrthonormalBasis.coe_mk]

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem hsSum_tensor (t' : (∀ i, V' i) → H') (ht' : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) (t : (∀ i, V i) → H)
    (ht : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) (A A' : H' →L[ℂ] H) (B B' : ∀ i, V' i →L[ℂ] V i)
    (hA : ∀ x, A (t' x) = t (fun i => B i (x i))) (hA' : ∀ x, A' (t' x) = t (fun i => B' i (x i))) :
    ∑ j, ⟪A (stdOrthonormalBasis ℂ H' j), A' (stdOrthonormalBasis ℂ H' j)⟫_ℂ =
      ∏ i, ∑ j, ⟪B i (stdOrthonormalBasis ℂ (V' i) j), B' i (stdOrthonormalBasis ℂ (V' i) j)⟫_ℂ := by
  rw [hsSum_indep (stdOrthonormalBasis ℂ H') (tONB t' ht' hsp) A A', Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tONB_apply, tB, hA, hA', ht]

end Tensor

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem wk_integrable {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : Integrable (fun g => f g * ⟪x, U g y⟫_ℂ) μ := by
  refine (hf.norm.mul_const (‖x‖ * ‖y‖)).mono' (hf.aestronglyMeasurable.mul (hm x y))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x))) (norm_nonneg _)

theorem wk_bound {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by
  calc ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖x‖ * ‖y‖) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x)))
          (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by rw [integral_mul_const, mul_assoc]

def wkForm {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ)
      (fun x₁ x₂ y => by
        simp only [inner_add_left, mul_add]
        exact integral_add (wk_integrable hU hm hf x₁ y) (wk_integrable hU hm hf x₂ y))
      (fun c x y => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; funext g; ring)
      (fun x y₁ y₂ => by
        simp only [map_add (f := _), inner_add_right, mul_add]
        exact integral_add (wk_integrable hU hm hf x y₁) (wk_integrable hU hm hf x y₂))
      (fun c x y => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring))
    (∫ g, ‖f g‖ ∂μ) (fun x y => wk_bound hU hf x y)

theorem wk_exists {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    ∃ T : E →L[ℂ] E, ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ := by
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (wkForm hU hm hf)),
    fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end Formalism.L2.SG.Pf.RConvFExistsPf
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {r : ℕ}

def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0

theorem lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]

theorem gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J

theorem rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by
  have hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  unfold Ymat
  calc (1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J) * W
        = W + W * M * ((Wᴴ * J * W)⁻¹ * (Wᴴ * J * W)) := by
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]

theorem Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem Ymat_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
