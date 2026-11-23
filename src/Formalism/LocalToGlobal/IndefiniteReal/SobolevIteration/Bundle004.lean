module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem mul_mem_KAt {G s a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KAt G s) (hb : b ∈ KAt G s) :
    a * b ∈ KAt G s := by
  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have hb' : b ∈ Formalism.QuantumDeterminants.UH G ∧ b * s = s * b := hb
  have h1 : aᴴ * G * a = G := ha'.1
  have h2 : bᴴ * G * b = G := hb'.1
  show a * b ∈ Formalism.QuantumDeterminants.UH G ∧ a * b * s = s * (a * b)
  refine ⟨?_, ?_⟩
  · show (a * b)ᴴ * G * (a * b) = G
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  · calc a * b * s = a * (b * s) := Matrix.mul_assoc _ _ _
      _ = a * (s * b) := by rw [hb'.2]
      _ = (a * s) * b := (Matrix.mul_assoc _ _ _).symm
      _ = (s * a) * b := by rw [ha'.2]
      _ = s * (a * b) := Matrix.mul_assoc _ _ _

theorem inv_mem_KAt {G s a : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (ha : a ∈ KAt G s) :
    a⁻¹ ∈ KAt G s := by

  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have h1 : aᴴ * G * a = G := ha'.1
  have hleft : (G⁻¹ * aᴴ * G) * a = 1 := by
    calc (G⁻¹ * aᴴ * G) * a = G⁻¹ * (aᴴ * G * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hG]
  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hleft
  have hright : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have hleft' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  show a⁻¹ ∈ Formalism.QuantumDeterminants.UH G ∧ a⁻¹ * s = s * a⁻¹
  refine ⟨?_, ?_⟩
  · show (a⁻¹)ᴴ * G * a⁻¹ = G
    calc (a⁻¹)ᴴ * G * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * G * a) * a⁻¹ := by rw [h1]
      _ = (a * a⁻¹)ᴴ * G * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hright]; simp
  · calc a⁻¹ * s = a⁻¹ * s * (a * a⁻¹) := by rw [hright, Matrix.mul_one]
      _ = a⁻¹ * (s * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha'.2]
      _ = (a⁻¹ * a) * s * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = s * a⁻¹ := by rw [hleft', Matrix.one_mul]

def Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s}
  mul_mem' {a b} ha hb := by
    show ((a * b : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_mul]; exact mul_mem_KAt ha hb
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_one]; exact one_mem_KAt G s
  inv_mem' {a} ha := by
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Matrix.coe_units_inv]; exact inv_mem_KAt (det_G_unit hs) ha

theorem isCompact_Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) :
    IsCompact ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by

  have hGu : IsUnit G.det := det_G_unit hs
  haveI : CompactSpace (KAt G s) := isCompact_iff_compactSpace.mp (isCompact_KAt hs)
  have hl : ∀ k ∈ KAt G s, (G⁻¹ * kᴴ * G) * k = 1 := fun k hk => by
    have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hr : ∀ k ∈ KAt G s, k * (G⁻¹ * kᴴ * G) = 1 := fun k hk => by
    rw [← Matrix.inv_eq_left_inv (hl k hk)]
    exact Matrix.mul_nonsing_inv k (Matrix.isUnit_det_of_left_inverse (hl k hk))
  let F : KAt G s → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun k =>
    ⟨k.1, G⁻¹ * k.1ᴴ * G, hr k.1 k.2, hl k.1 k.2⟩
  have hF : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
      continuous_const
  have he : ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) =
      Set.range F := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u.1, hu⟩, Units.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [he]
  exact isCompact_range hF

private theorem exists_Kg_coe_eq_of_mem_KAt {G s k : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) (hk : k ∈ KAt G s) :
    ∃ u : Kg hs, ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k := by
  have hGu : IsUnit G.det := det_G_unit hs
  have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
  have hleft : (G⁻¹ * kᴴ * G) * k = 1 := by
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hdet : IsUnit k.det := Matrix.isUnit_det_of_left_inverse hleft
  exact ⟨⟨⟨k, k⁻¹, Matrix.mul_nonsing_inv k hdet, Matrix.nonsing_inv_mul k hdet⟩, hk⟩, rfl⟩

theorem haarExists_holds : HaarExists := by
  intro n G s hs
  haveI : CompactSpace (Kg hs) := isCompact_iff_compactSpace.mp (isCompact_Kg hs)
  letI : MeasurableSpace (Kg hs) := borel (Kg hs)
  haveI : BorelSpace (Kg hs) := ⟨rfl⟩
  let ν : Measure (Kg hs) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.haarMeasure_self (G := Kg hs) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let φ : Kg hs → (Fin n → Fin n → ℂ) := fun u =>
    Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hφ : Continuous φ := by
    show Continuous (fun u : Kg hs => ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
    exact Units.continuous_val.comp continuous_subtype_val
  have hφm : Measurable φ := hφ.measurable
  have hcl : IsClosed {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isClosed_KAt G s
  refine ⟨ν.map φ, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Measure.map_apply hφm MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  · rw [ae_map_iff hφm.aemeasurable hcl.measurableSet]
    exact ae_of_all _ fun u => by
      show ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
      exact u.2
  · intro k₀ hk₀
    obtain ⟨u₀, hu₀⟩ := exists_Kg_coe_eq_of_mem_KAt hs hk₀
    have hT : Continuous (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) := by
      show Continuous (fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
      exact continuous_const.matrix_mul continuous_id
    have hL : Measurable (fun u : Kg hs => u₀ * u) := (continuous_const.mul continuous_id).measurable
    have hcomp : (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) ∘ φ =
        φ ∘ (fun u : Kg hs => u₀ * u) := by
      funext u
      show Matrix.of.symm (k₀ * ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.of.symm (((u₀ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      rw [hu₀]
    rw [Measure.map_map hT.measurable hφm, hcomp, ← Measure.map_map hφm hL,
      map_mul_left_eq_self]
  · rintro U hU ⟨k, hkU, hkK⟩
    obtain ⟨u, hu⟩ := exists_Kg_coe_eq_of_mem_KAt hs hkK
    rw [Measure.map_apply hφm hU.measurableSet]
    refine (hU.preimage hφ).measure_pos ν ⟨u, ?_⟩
    show Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ U
    rw [hu]
    exact hkU

end Formalism.IndefR.Tow.SobPf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

theorem avgKFin_holds : AvgKFin := by
  intro n H _ _ _ G s π hs hπ μ hμ q w
  classical
  have := hμ.1
  set N := q.totalDegree with hN
  let e : (Var n →₀ ℕ) → H := fun m => ∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ
  let W : Submodule ℂ H := Submodule.span ℂ (e '' Mon n N)
  have hfin : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ ((finite_Mon n N).image e)
  have hmemW : ∀ q' : MvPolynomial (Var n) ℂ, q'.totalDegree ≤ N →
      (∫ k, evP q' k • π (Matrix.of k) w ∂μ) ∈ W := by
    intro q' hq'
    have hint : ∀ m : Var n →₀ ℕ,
        Integrable (fun k => evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) μ :=
      fun m => integrable_avg hs hπ hμ (continuous_evP _) w
    have e1 : (fun k => evP q' k • π (Matrix.of k) w) = fun k => ∑ m ∈ q'.support,
        q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) := by
      funext k
      rw [evalMatrix_eq_sum_monomial q' k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul]
    have hint' : ∀ m ∈ q'.support, Integrable
        (fun k => q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w)) μ :=
      fun m _ => (hint m).smul (q'.coeff m)
    rw [e1, integral_finsetSum _ hint']
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [integral_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
    exact (MvPolynomial.le_totalDegree hm).trans hq'
  refine ⟨W, hfin, hmemW q le_rfl, ?_⟩
  intro k₀ hk₀ x hx
  have hG := det_G_unit hs
  have hk₀d := det_UH_unit hG hk₀.1
  have key : ∀ q' : MvPolynomial (Var n) ℂ, π k₀ (∫ k, evP q' k • π (Matrix.of k) w ∂μ) =
      ∫ k, evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k • π (Matrix.of k) w ∂μ := by
    intro q'
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hs hπ hμ (continuous_evP _) w)]
    have hT : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k) :=
      (continuous_const.matrix_mul continuous_id : Continuous fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
    let F : (Fin n → Fin n → ℂ) → H := fun k' =>
      evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k' • π (Matrix.of k') w
    have hFm : AEStronglyMeasurable F (μ.map fun k => Matrix.of.symm (k₀ * Matrix.of k)) := by
      rw [hμ.2.2.1 k₀ hk₀]; exact (integrable_avg hs hπ hμ (continuous_evP _) w).1
    have h1 : ∫ k', F k' ∂μ = ∫ k, F (Matrix.of.symm (k₀ * Matrix.of k)) ∂μ := by
      conv_lhs => rw [← hμ.2.2.1 k₀ hk₀]
      exact integral_map hT.aemeasurable hFm
    show _ = ∫ k', F k' ∂μ
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hμ.2.1] with k hk
    simp only [F]
    rw [evalMatrix_bind₁_mulLeft, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hk₀d, Matrix.one_mul,
      Equiv.symm_apply_apply, hπ.2.1 _ hk₀.1 _ hk.1, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_smul]
  have hstep : ∀ m ∈ Mon n N, π k₀ (e m) ∈ W := by
    intro m hm
    show π k₀ (∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ) ∈ W
    rw [key]
    refine hmemW _ ((totalDegree_bind_le _ _).trans ?_)
    rw [MvPolynomial.totalDegree_monomial m one_ne_zero]
    exact hm
  have hle : W ≤ W.comap (π k₀ : H →ₗ[ℂ] H) := by
    show Submodule.span ℂ (e '' Mon n N) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hstep m hm
  exact hle hx

end KFin

theorem avgKFin_holds : AvgKFin := KFin.avgKFin_holds

end Formalism.IndefR.Tow.SobPf

end
end
