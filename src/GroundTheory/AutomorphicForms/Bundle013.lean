module

public import GroundTheory.AutomorphicForms.Cartan
public import GroundTheory.AutomorphicForms.HeckeAlgebraLevel
public import GroundTheory.AutomorphicForms.WhittakerCriterion
public import GroundTheory.AutomorphicForms.WhittakerGroups
public import Mathlib.Topology.Algebra.Group.Units
import GroundTheory.AutomorphicForms.MeasuresModulus
public import GroundTheory.AutomorphicForms.MeasuresGL
public import GroundTheory.AutomorphicForms.WhittakerDistribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Measure Matrix GLnLocal HeckeAlgebra

namespace Spherical

variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

def transposeInv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  invFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

variable {F n}

@[simp]
theorem coe_transposeInv (g : GL (Fin n) F) :
    ((transposeInv F n g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

@[simp]
theorem coe_inv_transposeInv (g : GL (Fin n) F) :
    (((transposeInv F n g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

theorem transposeInv_transposeInv (g : GL (Fin n) F) : transposeInv F n (transposeInv F n g) = g :=
  (transposeInv F n).left_inv g

theorem transposeInv_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    transposeInv F n k ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hk ⊢
  exact ⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩

theorem transposeInv_mem_integralGL_iff {k : GL (Fin n) F} :
    transposeInv F n k ∈ integralGL F n ↔ k ∈ integralGL F n :=
  ⟨fun h => by simpa [transposeInv_transposeInv] using transposeInv_mem_integralGL h,
    transposeInv_mem_integralGL⟩

theorem inv_transposeInv_diagPow [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (l : Fin n → ℤ) : (transposeInv F n (Cartan.diagPow F n l))⁻¹ = Cartan.diagPow F n l := by
  ext i j
  rw [coe_inv_transposeInv, Cartan.coe_diagPow, diagonal_transpose]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_transposeInv : Continuous (transposeInv F n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin n) F => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact Units.continuous_val.matrix_transpose

def transposeInvHomeomorph : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toEquiv := (transposeInv F n).toEquiv
  continuous_toFun := continuous_transposeInv
  continuous_invFun := continuous_transposeInv

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

theorem map_transposeInv : μ.map (transposeInv F n) = μ := by
  have hH : (μ.map (transposeInv F n)).IsHaarMeasure :=
    (transposeInv F n).isHaarMeasure_map μ continuous_transposeInv
      (transposeInvHomeomorph (F := F) (n := n)).continuous_invFun
  set K := integralGL F n
  have hK0 : μ K ≠ 0 := (isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul (μ.map (transposeInv F n)) μ
  have hpre : transposeInv F n ⁻¹' (K : Set (GL (Fin n) F)) = K := by
    ext x
    exact transposeInv_mem_integralGL_iff
  have hK : μ.map (transposeInv F n) K = μ K := by
    rw [map_apply continuous_transposeInv.measurable (isOpen_integralGL F n).measurableSet, hpre]
  have hc : haarScalarFactor (μ.map (transposeInv F n)) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hK] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]

theorem integral_comp_transposeInv (f : GL (Fin n) F → ℂ) :
    ∫ g, f (transposeInv F n g) ∂μ = ∫ g, f g ∂μ := by
  have := integral_map_equiv (μ := μ) (transposeInvHomeomorph (F := F) (n := n)).toMeasurableEquiv f
  change ∫ g, f g ∂(μ.map (transposeInv F n)) = _ at this
  rw [map_transposeInv] at this
  exact this.symm

theorem apply_inv_transposeInv {f : GL (Fin n) F → ℂ}
    (hf : ∀ k ∈ integralGL F n, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) (g : GL (Fin n) F) :
    f (transposeInv F n g)⁻¹ = f g := by
  obtain ⟨l, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have : (transposeInv F n (k₁ * Cartan.diagPow F n l * k₂))⁻¹ =
      (transposeInv F n k₂)⁻¹ * Cartan.diagPow F n l * (transposeInv F n k₁)⁻¹ := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_transposeInv_diagPow, mul_assoc]
  have h₁ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₁)
  have h₂ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₂)
  rw [this, (hf _ h₁ _).2, (hf _ h₂ _).1, (hf _ hk₂ _).2, (hf _ hk₁ _).1]

variable {μ}

theorem heckeAlgebraLevel_mul_comm
    (a b : HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) : a * b = b * a := by
  have ha := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) a
  have hb := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) b
  have hab := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) (a * b)
  refine HeckeAlgebraLevel.ext (isCompact_integralGL F n) (isOpen_integralGL F n)
    (HeckeAlgebra.ext fun x => ?_)
  rw [HeckeAlgebraLevel.val_mul, HeckeAlgebraLevel.val_mul]
  rw [HeckeAlgebra.mul_apply (b : HeckeAlgebra μ)]
  set c := (transposeInv F n x)⁻¹
  have step1 : ∫ y, (b : HeckeAlgebra μ) y * (a : HeckeAlgebra μ) (y⁻¹ * x) ∂μ =
      ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e1 := apply_inv_transposeInv hb y
    have e2 := apply_inv_transposeInv ha (y⁻¹ * x)
    have hyx : (transposeInv F n (y⁻¹ * x))⁻¹ = c * transposeInv F n y := by
      rw [map_mul, map_inv (transposeInv F n), _root_.mul_inv_rev, inv_inv]
    show _ * _ = _ * _
    rw [← e1, ← e2, hyx]
  have step2 : ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ =
      ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ :=
    integral_comp_transposeInv μ (fun w => (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w))
  have step3 : ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ =
      ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) c := by
    have key := integral_mul_left_eq_self (μ := μ)
      (fun y => (a : HeckeAlgebra μ) y * (b : HeckeAlgebra μ) (y⁻¹ * c)) c
    rw [HeckeAlgebra.mul_apply, ← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
    ring
  rw [step1, step2, step3]
  have := apply_inv_transposeInv hab x
  rw [HeckeAlgebraLevel.val_mul] at this
  exact this.symm

instance instCommRing :
    CommRing (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) :=
  { (inferInstance : Ring (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n))) with
    mul_comm := heckeAlgebraLevel_mul_comm }

end Spherical

namespace HeckeAlgebra.HeckeAlgebraLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

instance : IsScalarTower ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_assoc c a b := ext hKc hKo (by
    change ((c • a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) * (b : HeckeAlgebra μ) =
      c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ))
    rw [val_smul, smul_mul_assoc])

instance : SMulCommClass ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_comm c a b := ext hKc hKo (by
    change c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) =
      (a : HeckeAlgebra μ) * ((c • b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ)
    rw [val_smul, mul_smul_comm])

instance instAlgebra : Algebra ℂ (HeckeAlgebraLevel μ K hKc hKo) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => (mul_smul_comm c a b))

end HeckeAlgebra.HeckeAlgebraLevel

end GroundTheory.Automorphic
end
end

section

namespace GroundTheory.Automorphic

namespace Whittaker

open MeasureTheory Measure ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem biEquivariantSigmaInvariant_GL (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) :
    BiEquivariantSigmaInvariant (Iwasawa.unipotent F n)
      (fun u => psiN ψ₀ (u : GL (Fin n) F)) sigmaHomeo := by
  intro D hD f
  have key := distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by
    have e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f :=
      Subtype.ext (coe_biTranslL u₁ u₂ f).symm
    rw [e]
    exact hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f
  have e : compHomeoL sigmaHomeo f =
      (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) := Subtype.ext rfl
  rw [e]
  exact key

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul

theorem map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by
  have hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := continuous_theta
  have hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F) := hθc.measurable
  have : (μ.map theta).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc
  set c := haarScalarFactor (μ.map theta) μ
  have e : μ.map theta = c • μ := isMulLeftInvariant_eq_smul (μ.map theta) μ
  have e2 : μ = (c * c) • μ := by
    have h1 : (μ.map theta).map theta = μ := by
      rw [Measure.map_map hθm hθm]
      have : (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id := funext theta_theta
      rw [this, Measure.map_id]
    have h2 : (μ.map theta).map theta = (c * c) • μ := by
      rw [e, Measure.map_smul, e, smul_smul]
      exact hθm.aemeasurable
    exact h1.symm.trans h2
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have hc : c = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h' := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    have hcc : (c * c : NNReal) = 1 := by exact_mod_cast h'
    have hr : ((c : ℝ) * (c : ℝ)) = 1 := by exact_mod_cast hcc
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have eθ : μ.map theta = μ := by rw [e, hc, one_smul]
  have hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta := by
    funext g
    simp [theta]
  rw [hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]
  exact Measures.inv_eq_self_GL F n μ

end Measure

theorem rank_whittaker_le_one_of_contragredient (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne

end Whittaker

end GroundTheory.Automorphic
end
