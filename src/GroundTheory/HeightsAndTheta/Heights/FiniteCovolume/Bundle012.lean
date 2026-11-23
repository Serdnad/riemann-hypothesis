module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace RationalUnipotent

def unipMap (h : HermitianForm F E W) (x₀ y : W) (c : E) : W →ₗ[E] W where
  toFun x := x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y
  map_add' a b := by
    simp only [map_add (f := _)]
    module
  map_smul' r a := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    module

omit [NumberField E] in
theorem unipMap_apply (h : HermitianForm F E W) (x₀ y : W) (c : E) (x : W) :
    unipMap h x₀ y c x = x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y := rfl


omit [NumberField E] in
theorem sesq_swap (h : HermitianForm F E W) (u v : W) :
    h.toSesq u v = conj F E (h.toSesq v u) :=
  (h.isSymm.eq v u).symm


omit [NumberField E] in
theorem sesq_smul_left (h : HermitianForm F E W) (r : E) (u v : W) :
    h.toSesq (r • u) v = conj F E r * h.toSesq u v := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

theorem unipMap_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipMap h x₀ y c (unipMap h x₀ (-y) (conj F E c) x) = x := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, map_neg, LinearMap.neg_apply, hx₀, hy, hy']
  have key : h.toSesq x₀ x * conj F E c - -h.toSesq y x +
      (h.toSesq x₀ x * c - (h.toSesq y x + -(h.toSesq x₀ x * h.toSesq y y))) = 0 := by
    linear_combination h.toSesq x₀ x * hc
  linear_combination (norm := module) key • x₀

theorem sesq_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x x' : W) :
    h.toSesq (unipMap h x₀ y c x) (unipMap h x₀ y c x') = h.toSesq x x' := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, smul_eq_mul, LinearMap.add_apply,
    sesq_smul_left, hx₀, hy, hy', map_sub, map_mul, mul_zero, add_zero]
  rw [sesq_swap h x x₀, sesq_swap h x y]
  linear_combination conj F E (h.toSesq x₀ x) * h.toSesq x₀ x' * hc

def unipElem (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) : h.unitaryGroup :=
  ⟨LinearEquiv.ofLinearMap (unipMap h x₀ y c) (unipMap h x₀ (-y) (conj F E c))
    (LinearMap.ext fun x => unipMap_unipMap h hx₀ hy hc x)
    (LinearMap.ext fun x => by
      have e := unipMap_unipMap h (y := -y) (c := conj F E c) hx₀
        (by rw [map_neg, hy, neg_zero])
        (by rw [conj_conj, add_comm, hc, map_neg, LinearMap.map_neg₂, neg_neg]) x
      rwa [neg_neg, conj_conj] at e),
    fun x x' => sesq_unipMap h hx₀ hy hc x x'⟩

theorem unipElem_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipElem h hx₀ hy hc • x = unipMap h x₀ y c x := rfl

theorem unipElem_inv_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := rfl

theorem unipMap_mem (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by
  have smul_mem : ∀ {α : E} {v : W}, α ∈ integralClosure ℤ E → v ∈ La → α • v ∈ La :=
    fun {α} {v} hα hv => hsm ⟨α, hα⟩ v hv
  rw [unipMap_apply]
  refine add_mem (add_mem hx (smul_mem ?_ hx₀)) (smul_mem (hint x₀ hx₀ x hx) hy)
  exact sub_mem (mul_mem (hint x₀ hx₀ x hx) hc) (hint y hy x hx)


omit [NumberField E] in
theorem conj_mem_integralClosure {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E :=
  (mem_integralClosure_iff ℤ E).2
    (((mem_integralClosure_iff ℤ E).1 hc).map (conj F E).toAlgHom.toRingHom.toIntAlgHom)

end RationalUnipotent


open RationalUnipotent in
theorem RationalUnipotent.proof (h : HermitianForm F E W) : RationalUnipotent.Statement h := by
  intro D La x₀ w₀ hD hx₀ hp
  refine ⟨1, one_pos, ?_⟩
  rintro y c hyW ⟨z₁, hz₁, rfl⟩ ⟨a, rfl⟩ hc
  simp only [Nat.cast_one, one_mul, one_smul] at hyW hc ⊢
  obtain ⟨hxx, hww, hxw⟩ := hp
  have hyx : h.toSesq x₀ z₁ = 0 := (mem_hypComplement.1 hyW).1
  have hyw : h.toSesq w₀ z₁ = 0 := (mem_hypComplement.1 hyW).2
  have hzx : h.toSesq z₁ x₀ = 0 := by rw [sesq_swap, hyx, map_zero]
  have hzw : h.toSesq z₁ w₀ = 0 := by rw [sesq_swap, hyw, map_zero]
  have haI : (a : E) ∈ integralClosure ℤ E :=
    (mem_integralClosure_iff ℤ E).2 (RingOfIntegers.isIntegral_coe a)
  set γ := unipElem h hxx hyx hc with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists v γ La).1 hv
      rw [hγ, unipElem_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ hz₁ haI hu
    · intro hv
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [hγ, unipElem_inv_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ (neg_mem hz₁)
        (conj_mem_integralClosure haI) hv
  · rw [hγ, unipElem_smul, unipMap_apply, hxx, hzx]
    simp
  · rw [hγ, unipElem_smul, unipMap_apply, hxw, hzw]
    simp only [one_mul, sub_zero, one_smul]
    abel
  · intro z hz
    rw [hγ, unipElem_smul, unipMap_apply, (mem_hypComplement.1 hz).1]
    simp only [zero_mul, zero_sub, zero_smul, add_zero, neg_smul]
    abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

namespace TorusEmbedding

section Linear

variable {ι : Type*} [Fintype ι]

def pair (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)

variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}

theorem pair_add (u z z' : ι → ℂ) : pair H u (z + z') = pair H u z + pair H u z' := by
  simp [pair, mulVec_add, dotProduct_add]

theorem pair_smul (u z : ι → ℂ) (c : ℂ) : pair H u (c • z) = c * pair H u z := by
  simp [pair, mulVec_smul, dotProduct_smul]

theorem add_pair (u u' z : ι → ℂ) : pair H (u + u') z = pair H u z + pair H u' z := by
  simp [pair, add_dotProduct]

theorem smul_pair (u z : ι → ℂ) (c : ℂ) : pair H (c • u) z = starRingEnd ℂ c * pair H u z := by
  simp [pair, star_smul, smul_dotProduct]

theorem pair_swap (hH : H.IsHermitian) (u z : ι → ℂ) :
    pair H u z = starRingEnd ℂ (pair H z u) := by
  rw [pair, pair, dotProduct_mulVec, ← RCLike.star_def, ← star_dotProduct_star, star_star,
    star_mulVec, hH.eq]

variable [DecidableEq ι]

def torusMat (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (s t : ℂ) : Matrix ι ι ℂ :=
  1 + (s - 1) • vecMulVec X (star Y ᵥ* H) + (t - 1) • vecMulVec Y (star X ᵥ* H)

theorem torusMat_mulVec (s t : ℂ) (z : ι → ℂ) :
    torusMat H X Y s t *ᵥ z = z + ((s - 1) * pair H Y z) • X + ((t - 1) * pair H X z) • Y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, pair,
    dotProduct_mulVec, op_smul_eq_smul, smul_smul]

theorem torusMat_one_one : torusMat H X Y 1 1 = 1 := by
  simp [torusMat]

theorem pair_Y_torusMat (hYY : pair H Y Y = 0) (hYX : pair H Y X = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H Y (torusMat H X Y s t *ᵥ z) = s * pair H Y z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hYX, hYY]; ring

theorem pair_X_torusMat (hXX : pair H X X = 0) (hXY : pair H X Y = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H X (torusMat H X Y s t *ᵥ z) = t * pair H X z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hXX, hXY]; ring

theorem torusMat_mul (hXX : pair H X X = 0) (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1)
    (hYX : pair H Y X = 1) (s t s' t' : ℂ) :
    torusMat H X Y s t * torusMat H X Y s' t' = torusMat H X Y (s * s') (t * t') := by
  refine mulVec_injective (funext fun z => ?_)
  rw [← mulVec_mulVec, torusMat_mulVec s t, pair_Y_torusMat hYY hYX, pair_X_torusMat hXX hXY,
    torusMat_mulVec s' t', torusMat_mulVec]
  module

theorem torusMat_mulVec_X (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by
  rw [torusMat_mulVec, hYX, hXX]; module

theorem torusMat_mulVec_Y (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ Y = t • Y := by
  rw [torusMat_mulVec, hYY, hXY]; module

theorem torusMat_mulVec_orth (s t : ℂ) (z : ι → ℂ) (hX : pair H X z = 0) (hY : pair H Y z = 0) :
    torusMat H X Y s t *ᵥ z = z := by
  rw [torusMat_mulVec, hX, hY]; simp

theorem torusMat_unitary (hH : H.IsHermitian) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (s t : ℂ) (hst : starRingEnd ℂ s * t = 1) :
    (torusMat H X Y s t)ᴴ * H * torusMat H X Y s t = H := by
  have hts : starRingEnd ℂ t * s = 1 := by
    have := congrArg (starRingEnd ℂ) hst
    simpa [mul_comm] using this
  have key : ∀ u z : ι → ℂ, pair H (torusMat H X Y s t *ᵥ u) (torusMat H X Y s t *ᵥ z) =
      pair H u z := by
    intro u z
    conv_lhs => rw [torusMat_mulVec s t u]
    rw [add_pair, add_pair, smul_pair, smul_pair, pair_Y_torusMat hYY hYX,
      pair_X_torusMat hXX hXY, torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul,
      pair_swap hH u X, pair_swap hH u Y]
    simp only [map_mul, map_sub, map_one]
    linear_combination (pair H X z * starRingEnd ℂ (pair H Y u)) * hst +
      (pair H Y z * starRingEnd ℂ (pair H X u)) * hts
  refine mulVec_injective (funext fun z => ?_)
  refine dotProduct_eq _ _ fun u => ?_
  rw [dotProduct_comm, dotProduct_comm (H *ᵥ z)]
  have := key (star u) z
  simp only [pair, star_star] at this
  rw [← this, star_mulVec, star_star]
  simp only [dotProduct_mulVec, vecMul_vecMul]

def torusGL (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (a : ℂˣ) : GL ι ℂ where
  val := torusMat H X Y a (starRingEnd ℂ ↑a⁻¹)
  inv := torusMat H X Y ↑a⁻¹ (starRingEnd ℂ a)
  val_inv := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.mul_inv, ← map_mul, Units.inv_mul, map_one,
      torusMat_one_one]
  inv_val := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.inv_mul, ← map_mul, Units.mul_inv, map_one,
      torusMat_one_one]

end Linear

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem place_pairs (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    pair (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
  obtain ⟨hxx, hww, hxw⟩ := hp
  have e : ∀ x y, pair (gramAt h v w) (vecAt v x w) (vecAt v y w) = w.embedding (h.toSesq x y) :=
    fun x y => (h1 w x y).symm
  refine ⟨by rw [e, hxx, map_zero], by rw [e, hww, map_zero], by rw [e, hxw, map_one], ?_⟩
  rw [pair_swap (h2 w).1, e, hxw, map_one, map_one]

variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)

def torusAt (w : InfinitePlace E) (a : ℂˣ) : GL ι ℂ :=
  torusGL (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) (place_pairs h1 h2 hp w).1
    (place_pairs h1 h2 hp w).2.1 (place_pairs h1 h2 hp w).2.2.1 (place_pairs h1 h2 hp w).2.2.2 a

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem torusAt_mem (a : InfinitePlace E → ℂˣ) :
    (fun w => torusAt h1 h2 hp w (a w)) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  have hc : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ))ᵀ = Mᴴ := fun M => by
    ext i j; simp [conjTranspose_apply]
  rw [hc]
  refine torusMat_unitary (h2 w).1 hXX hYY hXY hYX _ _ ?_
  rw [← map_mul, Units.mul_inv, map_one]

def torusHom : (InfinitePlace E → ℂˣ) →* archUnitary h v where
  toFun a := ⟨fun w => torusAt h1 h2 hp w (a w), torusAt_mem h1 h2 hp a⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (by
    simp [torusAt, torusGL, torusMat_one_one]))
  map_mul' a b := Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
    simp only [torusAt, torusGL, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    rw [torusMat_mul hXX hYY hXY hYX, ← map_mul, ← Units.val_mul, ← Units.val_mul,
      ← _root_.mul_inv_rev, mul_comm (b w)]))

theorem continuous_torusHom : Continuous (torusHom h1 h2 hp) := by
  refine Continuous.subtype_mk (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) (a w : ℂ) (starRingEnd ℂ ↑(a w)⁻¹)
    unfold torusMat
    fun_prop
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) ↑(a w)⁻¹ (starRingEnd ℂ (a w : ℂ))
    unfold torusMat
    fun_prop

end Places

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by
  intro x₀ w₀ hp
  refine ⟨torusHom h1 h2 hp, continuous_torusHom h1 h2 hp, fun a w => ?_⟩
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  refine ⟨torusMat_mulVec_X hXX hYX _ _, ?_, fun z hX hY => torusMat_mulVec_orth _ _ z hX hY⟩
  change torusMat _ _ _ _ _ *ᵥ _ = _
  rw [torusMat_mulVec_Y hYY hXY, Units.val_inv_eq_inv_val, map_inv₀]

end Main

end TorusEmbedding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
