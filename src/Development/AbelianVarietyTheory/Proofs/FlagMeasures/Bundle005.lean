module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

private lemma inner_apply_eq_inner_apply_inv_of_isometric {G : Type} [Group G] {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (a : G) (u w : Hp) : ⟪π a u, w⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := by

  let L : Hp →ₗᵢ[ℂ] Hp := { toLinearMap := (π a : Hp →ₗ[ℂ] Hp), norm_map' := hiso a }
  have hback : π a (π a⁻¹ w) = w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hL : ⟪L u, L (π a⁻¹ w)⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := L.inner_map_map _ _
  rw [← hL]
  show ⟪π a u, w⟫_ℂ = ⟪π a u, π a (π a⁻¹ w)⟫_ℂ
  rw [hback]

theorem integratedOperator_isStarProjection_and_sandwich :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [SigmaFinite μ] [μ.IsInvInvariant] (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ (φ m : G → ℂ), Integrable φ μ → (∀ g, star (φ g⁻¹) = φ g) → (∀ x y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = m x * φ y) → m 1 = 1 → ∀ P : Hp →L[ℂ] Hp, (∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ) → IsStarProjection P ∧ ∀ x : G, P ∘L π x ∘L P = m x • P := by
  intro G _ _ _ _ _ _ μ _ _ _ _ Hp _ _ _ π hiso hcont φ m hφ hstar hconv hm1 P hP

  have hsand : ∀ x : G, P ∘L π x ∘L P = m x • P := by
    intro x
    ext1 v
    refine ext_inner_left ℂ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, hP, hP]

    have step : ∀ g : G, ⟪u, π g (π x (P v))⟫_ℂ
        = ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ := by
      intro g
      have e1 : ⟪u, π g (π x (P v))⟫_ℂ = ⟪π (g * x)⁻¹ u, P v⟫_ℂ := by
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      have e2 : ∀ h : G, ⟪π (g * x)⁻¹ u, π h v⟫_ℂ = ⟪u, π (g * x * h) v⟫_ℂ := by
        intro h
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      rw [e1, hP]
      simp_rw [e2]
      have htr := integral_mul_left_eq_self (μ := μ)
        (fun h => φ h * ⟪u, π (g * x * h) v⟫_ℂ) (g * x)⁻¹
      rw [← htr]
      congr 1
      funext k
      rw [mul_inv_cancel_left, mul_inv_rev]
    simp_rw [step]

    have hshift : Integrable (fun k => φ (x⁻¹ * k)) μ := hφ.comp_mul_left x⁻¹
    have hprod : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.2)) (μ.prod μ) :=
      hφ.mul_prod hshift
    have hsheared : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2)) (μ.prod μ) := by
      have h := (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable hprod
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp, mul_assoc]
    have hcoef : Continuous fun k : G => ⟪u, π k v⟫_ℂ := continuous_const.inner (hcont v)
    have hbound : ∀ᵐ z ∂(μ.prod μ), ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
      refine Filter.Eventually.of_forall fun z => ?_
      calc ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖π z.2 v‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [hiso]
    have hint : Integrable (Function.uncurry fun g k =>
        φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ)) (μ.prod μ) := by
      have h := hsheared.mul_bdd (hcoef.comp continuous_snd).aestronglyMeasurable hbound
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      rcases z with ⟨g, k⟩
      simp only [Function.uncurry_apply_pair, Function.comp]
      ring
    calc ∫ g, φ g * ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ ∂μ
        = ∫ g, ∫ k, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ := by
          congr 1; funext g; rw [integral_const_mul]
      _ = ∫ k, ∫ g, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ :=
          integral_integral_swap hint
      _ = ∫ k, (m x * φ k) * ⟪u, π k v⟫_ℂ ∂μ := by
          congr 1; funext k
          rw [← hconv x k, ← integral_mul_const]
          congr 1; funext g; ring
      _ = m x * ∫ k, φ k * ⟪u, π k v⟫_ℂ ∂μ := by
          rw [← integral_const_mul]
          congr 1; funext k; ring

  have hsa : IsSelfAdjoint P := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro a b
    show ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ
    rw [← inner_conj_symm (P a) b, hP b a, hP a b, ← integral_conj]
    calc ∫ g, (starRingEnd ℂ) (φ g * ⟪b, π g a⟫_ℂ) ∂μ
        = ∫ g, (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [map_mul, inner_conj_symm, inner_apply_eq_inner_apply_inv_of_isometric π hiso]
      _ = ∫ g, (starRingEnd ℂ) (φ g⁻¹) * ⟪a, π g⁻¹⁻¹ b⟫_ℂ ∂μ :=
          (integral_inv_eq_self (fun g => (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ) μ).symm
      _ = ∫ g, φ g * ⟪a, π g b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [inv_inv, starRingEnd_apply, hstar]

  have hidem : IsIdempotentElem P := by
    have h := hsand 1
    rw [map_one, hm1, one_smul] at h
    show P * P = P
    ext v
    have hv := DFunLike.congr_fun h v
    simpa using hv
  exact ⟨⟨hidem, hsa⟩, hsand⟩

end GlobalTheory
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

def skewOpsBlock (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Submodule ℝ (F →L[ℂ] F) where
  carrier := {M | ∀ x z, ⟪M x, z⟫_ℂ + ⟪x, M z⟫_ℂ = 0}
  zero_mem' := by intro x z; simp
  add_mem' := by
    intro a b ha hb x z
    have h1 := ha x z
    have h2 := hb x z
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha x z
    have h1 := ha x z
    have e : ∀ y, (c • a) y = (c : ℂ) • a y := fun y => by
      simp [Complex.coe_smul]
    simp only [e, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (c : ℂ) * h1

theorem finrank_skewOpsBlock_le (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    Module.finrank ℝ (skewOpsBlock F) ≤ Module.finrank ℂ F ^ 2 := by
  let J : (F →L[ℂ] F) →ₗ[ℝ] (F →L[ℂ] F) :=
    { toFun := fun M => Complex.I • M
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  have hJ : Function.Injective J := by
    intro a b h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hd : Disjoint (skewOpsBlock F) ((skewOpsBlock F).map J) := by
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : b = 0 := by
      ext x
      have h1 := ha x (b x)
      have h2 := hb x (b x)
      have e : ∀ y, J b y = Complex.I • b y := fun y => rfl
      simp only [e, inner_smul_left, inner_smul_right, Complex.conj_I] at h1
      have h3 : ⟪b x, b x⟫_ℂ = 0 := by
        linear_combination (Complex.I / 2) * h1 + (1 / 2 : ℂ) * h2 +
          ((⟪b x, b x⟫_ℂ - ⟪x, b (b x)⟫_ℂ) / 2) * Complex.I_mul_I
      simpa using h3
    rw [hb0, map_zero]
  haveI : FiniteDimensional ℝ (F →L[ℂ] F) := FiniteDimensional.complexToReal _
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [← (Submodule.equivMapOfInjective J hJ (skewOpsBlock F)).finrank_eq,
    finrank_real_of_complex] at h1
  have h2 : Module.finrank ℂ (F →L[ℂ] F) = Module.finrank ℂ F ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := F) (F' := F)).finrank_eq,
      Module.finrank_linearMap, sq]
  omega

theorem exists_submodule_skew_block_finrank_le (n : ℕ)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ Module.finrank ℂ E ^ 2 ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ x ∈ E, ∀ z ∈ E, ⟪T x, z⟫_ℂ + ⟪x, T z⟫_ℂ = 0) →
          E.starProjection ∘L T ∘L E.starProjection ∈ U := by
  let Φ : (E →L[ℂ] E) →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun a b => by ext1 x; rfl
      map_smul' := fun c a => by ext1 x; rfl }
  haveI : FiniteDimensional ℝ (E →L[ℂ] E) := FiniteDimensional.complexToReal _
  refine ⟨(skewOpsBlock E).map Φ,
    (Submodule.finrank_map_le Φ _).trans (finrank_skewOpsBlock_le E), ?_⟩
  intro T hT
  refine ⟨E.orthogonalProjection ∘L T ∘L E.subtypeL, ?_, ?_⟩
  · intro x z
    have := hT x x.2 z z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjection_eq_of_mem_left,
      Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact this
  · ext1 x; rfl

end GlobalTheory
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem starProjection_inf_orthogonal_eq_sub {n : ℕ}
    (A A' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : A' ≤ A) (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_inf.2
      ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y)
      (Submodule.mem_inf.1 hw).2

theorem starProjection_inf_orthogonal_eq_of_mem_orthogonal {n : ℕ}
    (C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : C' ≤ C) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ C'ᗮ) : (C ⊓ C'ᗮ).starProjection v = C.starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]
    exact Submodule.inner_right_of_mem_orthogonal hz hv
  · intro w hw
    exact C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1

theorem infDist_le_norm_block_mul (n : ℕ)
    (A A' B B' C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (D T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hD : ∀ x, ‖D x‖ = ‖x‖) (hA : A' ≤ A) (hC : C' ≤ C)
    (hB : ∀ x ∈ B, ∀ z ∈ C', ⟪z, D x⟫_ℂ = 0) (hB' : ∀ x ∈ B', ∀ z ∈ C, ⟪z, D x⟫_ℂ = 0)
    (hdim : Module.finrank ℂ C + Module.finrank ℂ B' = n)
    (hT : ∀ y ∈ A, T y ∈ B) (hT' : ∀ y ∈ A', T y ∈ B') (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) :
    Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n))) ≤
      ‖(C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection‖ * ‖y‖ := by
  have hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ := by
    have hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro a b hab
      have h0 : ‖D (a - b)‖ = 0 := by
        rw [map_sub]
        simp only [ContinuousLinearMap.coe_coe] at hab
        rw [hab, sub_self, norm_zero]
      rwa [hD, norm_eq_zero, sub_eq_zero] at h0
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact hB' x hx z hz
    · rw [← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]
      symm
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [finrank_euclideanSpace_fin]
      exact hdim
  have hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y :=
    starProjection_inf_orthogonal_eq_sub A A' hA y hy
  have hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A := by
    rw [hy1]
    exact A.sub_mem hy (hA (A'.starProjection_apply_mem y))
  set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def
  have hw : w ∈ C'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact hB _ (hT _ hy1A) z hz
  obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by
    have hmem : Cᗮ.starProjection w ∈
        B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [hmap]
      exact Cᗮ.starProjection_apply_mem w
    obtain ⟨b, hb, hbw⟩ := hmem
    exact ⟨b, hb, hbw⟩
  have hmemB' : T (A'.starProjection y) + b ∈ B' :=
    B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb
  calc Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n)))
      ≤ dist (T y) (T (A'.starProjection y) + b) := Metric.infDist_le_dist_of_mem hmemB'
    _ = ‖T ((A ⊓ A'ᗮ).starProjection y) - b‖ := by
      rw [dist_eq_norm, hy1, map_sub]
      congr 1
      abel
    _ = ‖w - Cᗮ.starProjection w‖ := by
      rw [← hD, map_sub, hbw]
    _ = ‖C.starProjection w‖ := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    _ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by
      rw [starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]
    _ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end GlobalTheory
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integrable_matrixCoeff_mul_star
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ) (x y x' y' : H) :
    Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ := by
  refine Integrable.mono' ((hsq x y).add (hsq x' y'))
    ((hmeas x y).mul (hmeas x' y').star) (Filter.Eventually.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  nlinarith [sq_nonneg (‖⟪y, σ g x⟫_ℂ‖ - ‖⟪y', σ g x'⟫_ℂ‖),
    mul_nonneg (norm_nonneg ⟪y, σ g x⟫_ℂ) (norm_nonneg ⟪y', σ g x'⟫_ℂ)]

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_self
    (hsq : ∀ x y : H, ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ ∂μ = ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have h : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal, hsq x y, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  first
    | (push_cast; rfl)
    | simp

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization (a b : ℂ) :
    a * conj b = 1 / 4 * ((a + b) * conj (a + b) - (a - b) * conj (a - b)
      + Complex.I * ((a + Complex.I * b) * conj (a + Complex.I * b))
      - Complex.I * ((a - Complex.I * b) * conj (a - Complex.I * b))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_swap_eq_polarization (x x' : H) :
    ⟪x', x⟫_ℂ = 1 / 4 * (⟪x + x', x + x'⟫_ℂ - ⟪x - x', x - x'⟫_ℂ
      + Complex.I * ⟪x + Complex.I • x', x + Complex.I • x'⟫_ℂ
      - Complex.I * ⟪x - Complex.I • x', x - Complex.I • x'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_same_left
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x x' y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hdiag := integral_matrixCoeff_mul_star_self (fun x y => (hsq x y).2)
  have hpt : ∀ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪y, σ g (x + x')⟫_ℂ * star ⟪y, σ g (x + x')⟫_ℂ
        - ⟪y, σ g (x - x')⟫_ℂ * star ⟪y, σ g (x - x')⟫_ℂ
        + Complex.I * (⟪y, σ g (x + Complex.I • x')⟫_ℂ * star ⟪y, σ g (x + Complex.I • x')⟫_ℂ)
        - Complex.I * (⟪y, σ g (x - Complex.I • x')⟫_ℂ * star ⟪y, σ g (x - Complex.I • x')⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization ⟪y, σ g x⟫_ℂ ⟪y, σ g x'⟫_ℂ]
    simp only [map_add (f := _), map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      Complex.star_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    hdiag, hdiag, hdiag, hdiag, inner_swap_eq_polarization x x']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).add ((hint _ _ _ _).const_mul _)

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization_four (a a' b b' : ℂ) :
    a * conj b' = 1 / 4 * ((a + a') * conj (b + b') - (a - a') * conj (b - b')
      - Complex.I * ((a - Complex.I * a') * conj (b - Complex.I * b'))
      + Complex.I * ((a + Complex.I * a') * conj (b + Complex.I * b'))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_eq_polarization (w w' : H) :
    ⟪w, w'⟫_ℂ = 1 / 4 * (⟪w + w', w + w'⟫_ℂ - ⟪w - w', w - w'⟫_ℂ
      - Complex.I * ⟪w + Complex.I • w', w + Complex.I • w'⟫_ℂ
      + Complex.I * ⟪w - Complex.I • w', w - Complex.I • w'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring


open MeasureTheory in
open scoped InnerProductSpace in
theorem _root_.GlobalTheory.polarised_schur_relations :
    ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), (∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) → (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) → ∀ v w v' w' : H, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  intro G _ _ μ H _ _ _ σ d hmeas hsq v w v' w'
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hone := integral_matrixCoeff_mul_star_same_left hmeas hsq
  refine ⟨hint v w v' w', ?_⟩
  have hpt : ∀ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪w + w', σ g v⟫_ℂ * star ⟪w + w', σ g v'⟫_ℂ
        - ⟪w - w', σ g v⟫_ℂ * star ⟪w - w', σ g v'⟫_ℂ
        - Complex.I * (⟪w + Complex.I • w', σ g v⟫_ℂ * star ⟪w + Complex.I • w', σ g v'⟫_ℂ)
        + Complex.I * (⟪w - Complex.I • w', σ g v⟫_ℂ * star ⟪w - Complex.I • w', σ g v'⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization_four ⟪w, σ g v⟫_ℂ ⟪w', σ g v⟫_ℂ
      ⟪w, σ g v'⟫_ℂ ⟪w', σ g v'⟫_ℂ]
    simp only [inner_add_left, inner_sub_left, inner_smul_left, Complex.conj_I, Complex.star_def,
      neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    hone, hone, hone, hone, inner_eq_polarization w w']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).sub ((hint _ _ _ _).const_mul _)

end GlobalTheory
end
