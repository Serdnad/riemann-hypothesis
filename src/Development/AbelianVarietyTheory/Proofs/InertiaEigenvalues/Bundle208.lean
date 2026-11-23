module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103

@[expose] public section

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.approximatedTraceSystem_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  first | exact @GlobalTheory.polyApprox_trc_locally_cauchy | exact GlobalTheory.polyApprox_trc_locally_cauchy | (intros; apply GlobalTheory.polyApprox_trc_locally_cauchy <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.ClFin

variable {K : UQ} (B : InvAlg K)

def sigU : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)

theorem sigU_val (u : B.Aˣ) : ((sigU B u : B.Aˣ) : B.A) = B.σ u := rfl

def fixG : Subgroup B.Aˣ where
  carrier := {x | B.σ (x : B.A) = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = 1 := by
      calc B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = B.σ ((a⁻¹ : B.Aˣ) : B.A) * B.σ (a : B.A) := by
            rw [ha]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * ((a⁻¹ : B.Aˣ) : B.A)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, h, one_mul]

def normHom : B.Aˣ →* fixG B where
  toFun u := ⟨u * sigU B u, by
    show B.σ ((u : B.A) * B.σ u) = (u : B.A) * B.σ u
    rw [map_mul, B.σ_σ, mul_comm]⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp [sigU_val]
  map_mul' := by
    intro a b
    apply Subtype.ext; apply Units.ext
    simp only [Units.val_mul, sigU_val, map_mul, Subgroup.coe_mul]
    ring

theorem finite_quot (hsq : Finite (B.Aˣ ⧸ (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range))
    (hmu : Set.Finite {x : B.A | x ^ 2 = 1}) : Finite (fixG B ⧸ (normHom B).range) := by
  set Sq := (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range
  set φ : fixG B →* B.Aˣ ⧸ Sq := (QuotientGroup.mk' Sq).comp (fixG B).subtype
  haveI : Finite (fixG B ⧸ φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  set M := {x : fixG B | ((x : B.Aˣ) : B.A) ^ 2 = 1}
  haveI : Finite M := by
    have : Finite {x : B.A | x ^ 2 = 1} := hmu.to_subtype
    refine Finite.of_injective (fun x : M => (⟨((x.1 : B.Aˣ) : B.A), x.2⟩ : {x : B.A | x ^ 2 = 1})) ?_
    intro a b h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact congrArg Subtype.val h
  let g : (fixG B ⧸ φ.ker) × M → fixG B ⧸ (normHom B).range :=
    fun p => QuotientGroup.mk (Quotient.out p.1 * p.2.1)
  refine Finite.of_surjective g ?_
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set x₀ : fixG B := Quotient.out (QuotientGroup.mk x : fixG B ⧸ φ.ker)
  have hx₀ : x₀⁻¹ * x ∈ φ.ker := by
    have : (QuotientGroup.mk x₀ : fixG B ⧸ φ.ker) = QuotientGroup.mk x := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  rw [MonoidHom.mem_ker] at hx₀
  simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx₀
  obtain ⟨y, hy⟩ := hx₀
  rw [powMonoidHom_apply] at hy

  have hfix : B.σ ((y : B.A) ^ 2) = (y : B.A) ^ 2 := by
    have := (x₀⁻¹ * x).2
    rw [← Units.val_pow_eq_pow_val, hy]
    exact this
  set ε : B.Aˣ := y * (sigU B y)⁻¹
  have hε2 : (ε : B.A) ^ 2 = 1 := by
    have h1 : ((sigU B y : B.Aˣ) : B.A) ^ 2 = (y : B.A) ^ 2 := by rw [sigU_val, ← map_pow, hfix]
    have h1' : (sigU B y) ^ 2 = y ^ 2 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h1])
    have h2 : ((sigU B y)⁻¹ : B.Aˣ) ^ 2 = (y ^ 2)⁻¹ := by rw [inv_pow, h1']
    rw [← Units.val_pow_eq_pow_val]
    simp only [ε, mul_pow, h2, mul_inv_cancel, Units.val_one]
  have hεfix : B.σ (ε : B.A) = ε := by

    have hσ : B.σ (ε : B.A) * (ε : B.A) = 1 := by
      have hyinv : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
        have : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
          calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A)
              = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * B.σ (B.σ (y : B.A)) := by rw [B.σ_σ]
            _ = 1 := by rw [← map_mul, ← sigU_val, Units.inv_mul, map_one]
        calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A)
            = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by
              rw [Units.mul_inv, mul_one]
          _ = ((y⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, this, one_mul]
      simp only [ε, Units.val_mul, map_mul, hyinv]
      calc B.σ (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A))
          = (((sigU B y) : B.Aˣ) : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A) *
              ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by rw [sigU_val]; ring
        _ = 1 := by rw [Units.mul_inv, Units.mul_inv, one_mul]
    calc B.σ (ε : B.A) = B.σ (ε : B.A) * ((ε : B.A) * (ε : B.A)) := by rw [← sq, hε2, mul_one]
      _ = ε := by rw [← mul_assoc, hσ, one_mul]
  let εG : fixG B := ⟨ε, hεfix⟩
  refine ⟨(QuotientGroup.mk x, ⟨εG, hε2⟩), ?_⟩
  show QuotientGroup.mk (x₀ * εG) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  refine ⟨y, ?_⟩
  apply Subtype.ext; apply Units.ext

  have hxy : ((x : fixG B) : B.Aˣ) = (x₀ : B.Aˣ) * y ^ 2 := by
    rw [hy]; simp
  show ((y : B.A) * B.σ (y : B.A)) = (((x₀ * εG)⁻¹ * x : fixG B) : B.Aˣ).val
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxy, εG, ε]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, sigU_val]
  have : ((x₀ : B.Aˣ)⁻¹ : B.Aˣ).val * (x₀ : B.Aˣ).val = 1 := Units.inv_mul _
  have hy1 : (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv y
  rw [sq]
  linear_combination (-(B.σ (y : B.A) * (y : B.A))) * hy1 +
    (-(B.σ (y : B.A) * (y : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A))) * this

def toCl : fixG B ⧸ (normHom B).range → B.Cl :=
  Quotient.lift (fun x : fixG B => (Quot.mk _ ⟨(x : B.Aˣ), x.2⟩ : B.Cl)) (by
    intro a b hab
    have h := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨u, hu⟩ := h
    apply Quot.sound
    refine ⟨u, ?_⟩
    have hb : (b : B.Aˣ) = (a : B.Aˣ) * ((normHom B u : fixG B) : B.Aˣ) := by
      rw [hu]; simp
    show ((b : B.Aˣ) : B.A) = ((a : B.Aˣ) : B.A) * ((u : B.A) * B.σ (u : B.A))
    rw [hb, Units.val_mul]
    rfl)

theorem toCl_surjective : Function.Surjective (toCl B) := by
  intro k
  induction k using Quot.ind with
  | mk x => exact ⟨QuotientGroup.mk ⟨x.1, x.2⟩, rfl⟩

theorem finite_Cl (K : UQ) (B : InvAlg K) : Finite B.Cl := by
  have hsq := GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields K.E (GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic K) B.A
  have hmu := GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero K.E B.A
  haveI := finite_quot B hsq hmu
  exact Finite.of_surjective _ (toCl_surjective B)

theorem finite_Cl_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl :=
  fun K B _ => finite_Cl K B

end GlobalTheory.UnitLemma.ClFin
end

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.OrbitFinite

theorem orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B hsep x hxu hxσ
  by_cases h0 : ∃ L0, L0 ∈ B.X x
  swap
  · push_neg at h0
    haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩
    refine ⟨?_, fun L hL => absurd hL (h0 L)⟩
    unfold Orb
    infer_instance
  obtain ⟨L0, hL0⟩ := h0
  have hgi : IsIntegral K.O B.g := isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable K B hsep hgi

  have hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L := by
    intro L hL a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hL.2.1
    | algebraMap r =>
      intro y hy
      rw [← Algebra.smul_def]
      exact L.smul_mem r hy
    | add a b _ _ ha hb =>
      intro y hy
      rw [add_mul]
      exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
  have hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L :=
    fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hSf, hSl, hS⟩ := GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits K B hsep x hxu hxσ c hc0
    set W : Set (Submodule K.O B.A) :=
      (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW
    have hWf : W.Finite :=
      (hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left
    haveI : Finite W := hWf.to_subtype
    let f : W → Orb K.O B.T (B.X x) := fun M => Quot.mk _ ⟨M.1, M.2.2⟩
    apply Finite.of_surjective f
    intro o
    set L := (Quot.out o).1 with hLdef
    have hL : L ∈ B.X x := (Quot.out o).2
    obtain ⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩ := GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice K B x c hc0 L hL (hcL L hL)
    obtain ⟨t, ht, htS⟩ := hS J hJl hJs hJ1 hJ2
    have hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) =
        mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J) := by
      unfold mulLat
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext y
      simp [mul_left_comm]
    have hmem : mulLat K.O (t : B.A) L ∈ W := by
      refine ⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices K B x t ht L hL⟩
      rw [hcomm]
      exact Submodule.map_mono hJc
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [← Quot.out_eq o]
    exact (Quot.sound ⟨t, ht, rfl⟩).symm
  · intro L hL
    refine ⟨?_, GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩
    rintro t ⟨hs, -⟩
    refine ⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩
    refine isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_
    rw [← mul_assoc, Units.mul_inv, one_mul]
    exact hy

end GlobalTheory.UnitLemma.OrbitFinite
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WhitCollapse

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_normF (A : Et F E) : Continuous (fun t : A.K => Algebra.norm F t) := by
  classical
  let b := Module.finBasis F A.K
  have h : (fun t : A.K => Algebra.norm F t) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : A.K => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight F (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight F (b j)))

theorem norm_eta (x : F) : ‖eta x‖ = 1 := by
  unfold eta; split_ifs <;> simp

theorem measurable_etaK [Unram F E] (A : Et F E) : Measurable A.etaK := by
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨-, -, -, hlc⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hc : ContinuousOn (eta : F → ℂ) {0}ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    exact hlc.continuous
  have hm : Measurable (eta : F → ℂ) := measurable_of_continuousOn_compl_singleton 0 hc
  exact hm.comp (continuous_normF A).measurable

theorem collapse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ U A ψ hψ μK hμ φ' hφ a c hc
  have := U.charZero; have := U.ultraF; have := U.lcF
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOKo, hOKc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := GlobalTheory.FourKFub.psiK_continuous A ψ hψ
  have hηm := measurable_etaK A
  have hφc : Continuous φ' := hφ.1.continuous
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribSMul.toAddMonoidHom A.K c)
  have hMset : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    show c • z ∈ (R : Set A.K) ↔ c • z ∈ A.OK
    rw [hR]
  have hMo : IsOpen (M : Set A.K) := by rw [hMset]; exact hOKo.preimage (continuous_const_smul c)
  have hMc : IsCompact (M : Set A.K) := by
    rw [hMset]
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z; constructor
      · intro h; exact ⟨c • z, h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]; exact hOKc.image (continuous_const_smul _)
  have hMm : MeasurableSet (M : Set A.K) := hMo.measurableSet
  have hMcl : IsClosed (M : Set A.K) := hMc.isClosed
  set χ : A.K → ℂ := (M : Set A.K).indicator (fun _ => 1) with hχdef
  have hχc : Continuous χ := IsClopen.continuous_indicator ⟨hMcl, hMo⟩ continuous_const
  let K0 : A.K × (A.K × A.K) → ℂ := fun q =>
    χ q.1 * φ' (q.2.2, q.2.1) * A.psiK ψ (q.2.1 * q.1 * q.2.2) * A.psiK ψ (-(a * q.1))
  have hK0c : Continuous K0 := by fun_prop
  have hK0s : HasCompactSupport K0 := by
    refine HasCompactSupport.intro (hMc.prod (hφ.2.isCompact.image continuous_swap)) ?_
    rintro ⟨z, t, b⟩ hq
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with hz | hp
    · simp [K0, χ, hz]
    · have : φ' (b, t) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(b, t), h, rfl⟩)
      simp [K0, this]
  have hK0i : Integrable K0 (μK.prod (μK.prod μK)) := hK0c.integrable_of_hasCompactSupport hK0s
  let H : A.K × (A.K × A.K) → ℂ := fun q => K0 q * A.etaK q.2.1
  have hH : Integrable H (μK.prod (μK.prod μK)) :=
    hK0i.mul_bdd (c := 1) (hηm.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall fun q => (norm_eta _).le)

  have hsymm : (Algebra.traceForm F A.K).IsSymm := ⟨fun x y => by simp [mul_comm]⟩
  have hI := fun y => ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) hsymm hnd μK hμ).1 M hMo hMc).2 y
  set N : Set A.K := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hNdef
  have hN : {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} = N := by
    ext y
    simp only [Set.mem_setOf_eq, N, Algebra.traceForm_apply]
    constructor
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset]; exact hx)
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset] at hx; exact hx)
  set vol : ℂ := (((μK (M : Set A.K)).toReal : ℝ) : ℂ) with hvol
  let Q : A.K × A.K → ℂ := fun p => vol * (φ' (p.2, p.1) * N.indicator (fun _ => (1 : ℂ)) (p.1 * p.2 - a) * A.etaK p.1)
  have h3 : ∀ p : A.K × A.K, ∫ z, H (z, p) ∂μK = Q p := by
    rintro ⟨t, b⟩
    have e1 : ∀ z, H (z, (t, b)) = (φ' (b, t) * A.etaK t) *
        (M : Set A.K).indicator (fun z => ψ (Algebra.traceForm F A.K z (t * b - a))) z := by
      intro z
      by_cases hz : z ∈ (M : Set A.K)
      · rw [Set.indicator_of_mem hz]
        simp only [H, K0, χ, Set.indicator_of_mem hz, Algebra.traceForm_apply]
        have : A.psiK ψ (t * z * b) * A.psiK ψ (-(a * z)) = ψ (Algebra.trace F A.K (z * (t * b - a))) := by
          rw [← GlobalTheory.FourKFub.psiK_add]; simp only [Et.psiK]; congr 2; ring
        linear_combination (φ' (b, t) * A.etaK t) * this
      · simp [H, K0, χ, hz]
    simp_rw [e1]
    rw [integral_const_mul, integral_indicator hMm, hI, hN]
    simp only [Q]
    by_cases hy : t * b - a ∈ N
    · simp [Set.indicator_of_mem hy, vol]; ring
    · simp [Set.indicator_of_notMem hy]
  have hQi : Integrable Q (μK.prod μK) :=
    (hH.integral_prod_right (f := H)).congr (Eventually.of_forall h3)
  rw [← hMset, ← integral_indicator hMm]
  trans ∫ z, ∫ p, H (z, p) ∂(μK.prod μK) ∂μK
  · refine integral_congr_ae ?_
    filter_upwards [hH.prod_right_ae] with z hz
    rw [integral_prod _ hz]
    by_cases hzM : z ∈ (M : Set A.K)
    · rw [Set.indicator_of_mem hzM, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [H, K0, χ, Set.indicator_of_mem hzM]
      rw [← integral_mul_const, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      simp only
      ring
    · simp [Set.indicator_of_notMem hzM, H, K0, χ]
  rw [integral_integral_swap (f := fun z p => H (z, p)) hH]
  simp_rw [h3]
  rw [integral_prod Q hQi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Q, vol]
  rw [← integral_mul_const, ← integral_const_mul]

end GlobalTheory.WhitCollapse
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem charIntegral_inv_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ c : F, c ≠ 0 → ∀ b : A.K, ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * b) ∂μK = Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => ((μK {z : A.K | c • z ∈ A.OK}).toReal : ℂ)) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ c hc b
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribSMul.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    simp [M, ← hR]
  have hMO : IsOpen (M : Set A.K) := by
    rw [hM]
    exact hO.preimage (continuous_const_smul c)
  have hMC : IsCompact (M : Set A.K) := by
    rw [hM]
    exact (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).mpr hC
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hμ).1
    M hMO hMC).2 b
  have hpsi : ∀ z y : A.K, A.psiK ψ (z * y) = ψ (Algebra.traceForm F A.K z y) := by
    intro z y
    simp [Et.psiK, Algebra.traceForm_apply]
  simp_rw [hpsi]
  rw [← hM]
  convert key using 2
  ext y
  simp only [Set.mem_setOf_eq, Algebra.traceForm_apply]
  constructor
  · intro h x hx
    exact h x (by simpa [hM] using (show x ∈ (M : Set A.K) from hx))
  · intro h z hz
    exact h z (show z ∈ (M : Set A.K) by rw [hM]; exact hz)

end GlobalTheory.JR
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  first | exact @GlobalTheory.UnitLemma.FibSum.fibsum | exact GlobalTheory.UnitLemma.FibSum.fibsum | (intros; apply GlobalTheory.UnitLemma.FibSum.fibsum <;> assumption)
end
