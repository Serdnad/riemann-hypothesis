module

public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle024
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def adeleSplit (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) 𝔸[F] ≃ₜ*
      unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
        unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
  (unitaryCongr (gram h.toSesq v) (adeleRingEquivProd F) (by exact continuous_id)
      (by exact continuous_id)).trans
    (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v))

def ArchimedeanUnitaryEquiv.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ ψ : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v,
    ∀ γ : h.unitaryGroup, ψ (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def ComplementLattice.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D n : ℕ, 0 < n → ∃ D' : ℕ,
      ∀ La : AddSubgroup W, IsDIntegral h D La →
        (∀ x ∈ La, ∃ a ∈ lineCoeffs (E := E) La v₀, ∃ b ∈ lineCoeffs (E := E) La w₀,
          n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) →
        IsDIntegral h' D' (La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Complement

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

section NormalForm

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def LineNormalForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n : ℕ, 0 < n ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ v w : W, v ∈ l ∧ IsHyperbolicPair h v w ∧
        (lineCoeffs (E := E) La v, lineCoeffs (E := E) La w) ∈ KK ∧
        ∀ x ∈ La, (n : E) * h.toSesq w x ∈ lineCoeffs (E := E) La v ∧
          (n : E) * h.toSesq v x ∈ lineCoeffs (E := E) La w

end NormalForm

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Reduction

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def AdaptedReduction.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D : ℕ,
    ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n D' : ℕ, 0 < n ∧
      ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
        ∃ (g : h.unitaryGroup) (La₁ : AddSubgroup W), g • La₁ = La ∧ g • v₀ ∈ l ∧
          (lineCoeffs (E := E) La₁ v₀, lineCoeffs (E := E) La₁ w₀) ∈ KK ∧
          (∀ x ∈ La₁, ∃ a ∈ lineCoeffs (E := E) La₁ v₀, ∃ b ∈ lineCoeffs (E := E) La₁ w₀,
            n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) ∧
          IsDIntegral h' D' (La₁.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)

end Reduction

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.UpperTheory.Reformulated.B.Gub1.proof E W

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic

noncomputable section

namespace ComplementExtension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem toSesq_v_v (hp : IsHyperbolicPair h v w) : h.toSesq v v = 0 := hp.1

theorem toSesq_w_w (hp : IsHyperbolicPair h v w) : h.toSesq w w = 0 := hp.2.1

theorem toSesq_v_w (hp : IsHyperbolicPair h v w) : h.toSesq v w = 1 := hp.2.2

theorem toSesq_w_v (hp : IsHyperbolicPair h v w) : h.toSesq w v = 1 := by
  rw [← h.isSymm.eq v w, hp.2.2, map_one]

theorem toSesq_swap_eq_zero {u z : W} (hz : h.toSesq u z = 0) : h.toSesq z u = 0 := by
  rw [← h.isSymm.eq u z, hz, map_zero]

def proj (hp : IsHyperbolicPair h v w) : W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict _
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w)
    (fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
        smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp]
      constructor <;> ring)

theorem proj_apply (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem split (hp : IsHyperbolicPair h v w) (x : W) :
    h.toSesq w x • v + (proj hp x : W) + h.toSesq v x • w = x := by
  rw [proj_apply]; abel

theorem toSesq_split (hp : IsHyperbolicPair h v w) (a b a' b' : E) (z z' : hypComplement h v w) :
    h.toSesq (a • v + (z : W) + b • w) (a' • v + (z' : W) + b' • w) =
      conjHom F E a * b' + conjHom F E b * a' + h.toSesq z z' := by
  obtain ⟨hvz, hwz⟩ := mem_hypComplement.1 z.2
  obtain ⟨hvz', hwz'⟩ := mem_hypComplement.1 z'.2
  have hzv := toSesq_swap_eq_zero hvz
  have hzw := toSesq_swap_eq_zero hwz
  simp only [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp, hvz', hwz', hzv, hzw]
  ring

def extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) : W →ₗ[E] W :=
  (h.toSesq w).smulRight v + (hypComplement h v w).subtype ∘ₗ m ∘ₗ proj hp +
    (h.toSesq v).smulRight w

theorem extMap_apply (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    extMap hp m x = h.toSesq w x • v + (m (proj hp x) : W) + h.toSesq v x • w := rfl

theorem toSesq_w_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq w (extMap hp m x) = h.toSesq w x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).2
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_w_w hp, toSesq_w_v hp, this]
  ring

theorem toSesq_v_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq v (extMap hp m x) = h.toSesq v x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).1
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_v_v hp, toSesq_v_w hp, this]
  ring

theorem proj_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    proj hp (extMap hp m x) = m (proj hp x) := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_extMap, toSesq_v_extMap, extMap_apply]
  abel

theorem extMap_comp (hp : IsHyperbolicPair h v w)
    (m m' : hypComplement h v w →ₗ[E] hypComplement h v w) :
    extMap hp m ∘ₗ extMap hp m' = extMap hp (m ∘ₗ m') := by
  ext x
  rw [LinearMap.comp_apply, extMap_apply hp m, toSesq_w_extMap, toSesq_v_extMap, proj_extMap,
    extMap_apply]
  rfl

theorem extMap_id (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by
  ext x
  rw [extMap_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact split hp x

theorem proj_of_mem (hp : IsHyperbolicPair h v w) (x : hypComplement h v w) :
    proj hp (x : W) = x := by
  obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
  apply Subtype.ext
  rw [proj_apply, hvx, hwx]
  simp

theorem proj_v (hp : IsHyperbolicPair h v w) : proj hp v = 0 := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_v hp, hp.1]
  simp

theorem proj_w (hp : IsHyperbolicPair h v w) : proj hp w = 0 := by
  apply Subtype.ext
  rw [proj_apply, hp.2.1, hp.2.2]
  simp

theorem proof (h : HermitianForm F E W) : ComplementExtension.Statement h := by
  intro v w hp h' hh' m
  let M : hypComplement h v w ≃ₗ[E] hypComplement h v w := m
  let e : W ≃ₗ[E] W := LinearEquiv.ofLinearMap (extMap hp M.toLinearMap)
    (extMap hp M.symm.toLinearMap)
    (by rw [extMap_comp, LinearEquiv.comp_symm, extMap_id])
    (by rw [extMap_comp, LinearEquiv.symm_comp, extMap_id])
  have he : ∀ x, e x = extMap hp M.toLinearMap x := fun x => rfl
  have hM : ∀ a b, h.toSesq (M a : W) (M b : W) = h.toSesq (a : W) b := by
    intro a b
    rw [← hh', ← hh']
    exact m.2 a b
  have hmem : e ∈ h.unitaryGroup := by
    intro x y
    rw [he, he, extMap_apply, extMap_apply, toSesq_split hp]
    conv_rhs => rw [← split hp x, ← split hp y]
    rw [toSesq_split hp]
    simp only [LinearEquiv.coe_coe, hM]
  refine ⟨⟨e, hmem⟩, ?_, ?_, ?_⟩
  · change e v = v
    rw [he, extMap_apply, proj_v, map_zero, toSesq_w_v hp, hp.1]
    simp
  · change e w = w
    rw [he, extMap_apply, proj_w, map_zero, hp.2.1, hp.2.2]
    simp
  · intro x
    change e x = ((M x : hypComplement h v w) : W)
    obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
    rw [he, extMap_apply, proj_of_mem, hvx, hwx]
    simp

end ComplementExtension

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_coercive_of_posDef {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ (P *ᵥ z)).re :=
  _root_.UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef hP

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_coord_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by
  choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)
  set G : InfinitePlace E → Matrix ι ι ℂ := fun w =>
    (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG
  refine ⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩
  set z := invApply g y with hz
  have hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re := fun w' =>
    (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1
  have hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
    simp [hG]
  have hy : y w = G w *ᵥ z w := by
    rw [hz, invApply, mulVec_mulVec, hinv, one_mulVec]
  have hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w) := by
    intro j
    have hsq : 0 < Real.sqrt (c w) := Real.sqrt_pos.2 (hc w)
    rw [le_div_iff₀ hsq]
    have h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re :=
      (hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)] at h2
    unfold Majorant.len
    linarith
  have hlen : 0 ≤ M.len z := Real.sqrt_nonneg _
  calc ‖y w i‖ = ‖∑ j, G w i j * z w j‖ := by rw [hy]; rfl
    _ ≤ ∑ j, ‖G w i j‖ * ‖z w j‖ := (norm_sum_le _ _).trans (by simp)
    _ ≤ ∑ j, ‖G w i j‖ / Real.sqrt (c w) * M.len z := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)
    _ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]
    _ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by
        refine mul_le_mul_of_nonneg_right ?_ hlen
        refine le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j,
          ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w))
          (fun _ _ => by positivity) (Finset.mem_univ i)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LatticePointsBelowFinite.Statement h v := by
  classical
  intro M La g t hLa
  obtain ⟨S, hS⟩ := hLa.fg

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add (f := _), Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    have hall : ∀ s : La, (s : W) ∈ T := by
      intro s
      have hmem : s ∈ AddSubsemigroup.closure (S : Set La) := by
        rw [hS]
        trivial
      induction hmem using AddSubsemigroup.closure_induction with
      | mem s hs =>
        intro i
        exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      | add a b _ _ ha hb => exact T.add_mem ha hb
    intro x hx
    exact hall ⟨x, hx⟩
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  obtain ⟨K, hK0, hK⟩ := exists_coord_le_len M g
  set B : ℝ := |(d : ℝ)| * (K * t) with hB
  set A : Set E := {a | IsIntegral ℤ a ∧ ∀ φ : E →+* ℂ, ‖φ a‖ ≤ B} with hA
  have hAfin : A.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  set φ : W → ι → E := fun x i => d • v.repr x i with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have := congrFun hxy i
    simp only [hφ, zsmul_eq_mul] at this
    exact mul_left_cancel₀ hdE this
  refine ((Set.Finite.pi (t := fun _ : ι => A) fun _ => hAfin).preimage hinj.injOn).subset ?_
  rintro x ⟨hx, hxt⟩ i -
  refine ⟨hLaT hx i, fun ψ => ?_⟩
  have hw : ‖ψ (v.repr x i)‖ = ‖(InfinitePlace.mk ψ).embedding (v.repr x i)‖ := by
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  have hb := hK (vecAt v x) (InfinitePlace.mk ψ) i
  change ‖ψ (d • v.repr x i)‖ ≤ B
  rw [zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast, hw, hB]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hxt.le hK0)

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
