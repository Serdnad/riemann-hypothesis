module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle110
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

section General

open Formalism.UG Formalism.UG.P IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem exists_approx (c : 𝓞 F) (hc : c ≠ 0) (a : 𝒜) :
    ∃ x : E, ∃ w ∈ 𝒮, a = ι x + levelafC E c * w := by
  obtain ⟨d, hd, hda⟩ := levelaf_denom (E := E) a
  obtain ⟨b, t, ht, hbt⟩ := csGlob_approx csGlob_intAdApprox (d * c) (mul_ne_zero hd hc) _ hda
  refine ⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b, t, ht, ?_⟩
  have he : algebraMap (𝓞 F) E d ≠ 0 := adelstab_algebraMap_ne_zero d hd
  have hinv : ι ((algebraMap (𝓞 F) E d)⁻¹) * levelafC E d = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ he, map_one]
  have h2 : a = ι ((algebraMap (𝓞 F) E d)⁻¹) * (levelafC E d * a) := by
    rw [← mul_assoc, hinv, one_mul]
  rw [h2, hbt, levelafC_mul, map_mul]
  linear_combination (levelafC E c * t) * hinv

theorem mem_range_of_incl {e : E} (he : ι e ∈ 𝒮) : e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨e, csGlob_int (F := F) e he⟩, rfl⟩

variable (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
  (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)

include hdual

omit [NumberField F] [DecidableEq n] in
theorem integral_of_selfDual :
    ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (((1 : ℤ) : E) * hform (σ : E →+* E) J x y) := by
  intro x hx y hy
  obtain ⟨b, hb⟩ := (hdual y).1 hy x hx
  rw [Int.cast_one, one_mul, ← hb]
  exact NumberField.RingOfIntegers.isIntegral_coe b

theorem mem_latS_of_integral (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (z : n → 𝒜)
    (hz : ∀ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ,
      hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) w z ∈ 𝒮) :
    z ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
  obtain ⟨m, hm0, hm⟩ := csGlob_single Λ hspan
  have hc : ((m : 𝓞 F)) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have hC : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      (fun i => levelafC E (m : 𝓞 F) * v i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
    intro v hv
    have hk : ∀ k, (fun i => ι ((Pi.single k (m : E) : n → E) i)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      fun k => Submodule.subset_span ⟨_, hm k, rfl⟩
    have heq : (fun i => levelafC E (m : 𝓞 F) * v i) =
        ∑ k, (⟨v k, hv k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : n → E) i)) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.single_apply, Subring.smul_def, ← adelstab_incl_C, mul_comm]
      · intro k _ hki
        simp [Pi.single_apply, Ne.symm hki]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [heq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hk k)
  choose x w hw hxw using fun i => exists_approx (E := E) (m : 𝓞 F) hc (z i)
  have hint := integral_of_selfDual σ J Λ hdual
  have hzc := hC w hw
  have hz' : z = (fun i => ι (x i)) + (fun i => levelafC E (m : 𝓞 F) * w i) := funext hxw
  have hx : x ∈ Λ := by
    refine (hdual x).2 fun y hy => ?_
    have hyS : (fun i => ι (y i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    have h1 := hz _ hyS
    have h2 := csScale_latS σ J Λ 1 hint hyS hzc
    rw [Int.cast_one, map_one, one_mul] at h2
    rw [hz', csScale_hform_add_right, csScale_hform_incl] at h1
    refine mem_range_of_incl (F := F) ?_
    have h3 := sub_mem h1 h2
    rwa [add_sub_cancel_right] at h3
  rw [hz']
  exact add_mem (Submodule.subset_span ⟨x, hx, rfl⟩) hzc

theorem globLat_selfDual (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (x : n → E) :
    x ∈ CS.globLat g Λ ↔
      ∀ y ∈ CS.globLat g Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range := by
  have hint := integral_of_selfDual σ J Λ hdual
  constructor
  · intro hx y hy
    have h := csScale_glob σ J Λ 1 hint g hg hy hx
    rw [Int.cast_one, one_mul] at h
    exact mem_range_of_incl (F := F) h
  · intro H
    rw [csGlob_eq, adelstab_mem_iff]
    refine mem_latS_of_integral σ J Λ hdual hspan _ fun w hw => ?_
    obtain ⟨u, hu⟩ : ∃ u : n → 𝒜, u = ((g : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w := ⟨_, rfl⟩
    have hw' : w = ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u := by
      rw [hu, mulVec_mulVec, Units.inv_mul, one_mulVec]
    have huS := csSpan_back csGlob_intAdApprox Λ hfin hspan g u (by rw [← hw']; exact hw)
    have h := csDual_span σ J (CS.globLat g Λ) x H u huS
    have hU : Formalism.UG.cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *
        J.map ι * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = J.map ι := inv_mem hg
    rw [hw', hform_mulVec, hU]
    exact h

end General

theorem lamX_eq_globLat (I : AutInst) (x : I.GA) :
    lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
  apply GlobalTheory.PointEquivariance.lamX_eq <;> assumption

theorem lamX_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  intro I x
  have hmem : ∀ (x' : I.GA) (y : Fin I.n → I.E),
      y ∈ Formalism.UG.CS.globLat (x'.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L ↔
        I.fmat x'.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
    have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
      show Submodule.span _ _ = Submodule.span _ _
      rw [Set.image_eq_range]
      rfl
    intro x' y
    rw [Formalism.UG.P.csGlob_eq, Formalism.UG.P.adelstab_mem_iff, hL]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hlat := Formalism.UG.P.csGlob_lattice (F := I.F) I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have hσ : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := rfl
  have hdual' : ∀ y, y ∈ I.L ↔ ∀ z ∈ I.L, Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E)
      I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range := by
    rw [hσ]
    exact I.L_dual
  refine ⟨fun y => ?_, ?_, ?_, fun y => ?_, fun k hk => ?_⟩
  · rw [lamX_eq_globLat]
    exact hmem x y
  · rw [lamX_eq_globLat]
    exact hlat.fg
  · rw [lamX_eq_globLat]
    exact hlat.span_eq_top
  · rw [lamX_eq_globLat, ← hσ]
    exact globLat_selfDual I.cm.sig I.J I.L hdual' hfin I.L_span _ x.2.2 y
  · rw [lamX_eq_globLat, lamX_eq_globLat]
    ext y
    rw [hmem, hmem]
    have hk2 : ((k.2⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf :=
      inv_mem (show ((k.2 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf from hk)
    have e1 : I.fmat (x * k).2⁻¹ = I.fmat k.2⁻¹ * I.fmat x.2⁻¹ := by
      rw [Prod.snd_mul, _root_.mul_inv_rev]
      rfl
    rw [e1, ← mulVec_mulVec]
    exact (hk2 _).symm

end GlobalTheory.PointLattice
end
end

section

namespace GlobalTheory

open Matrix

theorem det_updateRow_last_single {K : Type} [CommRing K] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det
      = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [← two_mul, pow_mul]

theorem det_fromBlocks_corner {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then a else 0)
      (Matrix.diagonal fun i => if i = Fin.last r then b else 0) W).det
      = Z.det * W.det - a * b * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  set l := Fin.last r with hl
  set D : K → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun c => Matrix.diagonal fun i => if i = l then c else 0 with hD
  have h1 : Matrix.fromBlocks Z (D a) (D b) W
      = (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l)
          (Matrix.fromBlocks Z 0 (D b) W (Sum.inl l) + a • Pi.single (Sum.inr l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h2 : (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l) (Pi.single (Sum.inr l) 1)
      = (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
          (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W (Sum.inr l)
            + b • Pi.single (Sum.inl l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h3 : (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1)
      = (Matrix.fromBlocks (Z.updateRow l (Pi.single l 1)) 0 0
          (W.updateRow l (Pi.single l 1))).submatrix (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm,
        Equiv.swap_apply_def] <;> grind
  have h0 : (Z.updateRow l 0).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  change (Matrix.fromBlocks Z (D a) (D b) W).det = _
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h2,
    Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h3,
    Matrix.det_permute, Equiv.Perm.sign_swap (by simp), Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h0, hl,
    det_updateRow_last_single, det_updateRow_last_single]
  simp
  ring

theorem det_gram_two_frames {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by
  apply GlobalTheory.SA.TransvG.det_fromBlocks_last <;> assumption

end GlobalTheory
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.PerpBaseChange

private theorem dual_span_sum_eq_zero {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    ∀ ψ ∈ Submodule.span E S, ∑ j, ι (ψ (Pi.single j 1)) * u j = 0 := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [LinearMap.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

theorem mem_span_of_forms {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' {y | ∀ φ ∈ S, φ y = 0}) := by
  classical

  set D : Submodule E (Module.Dual E (Fin n → E)) := Submodule.span E S with hD
  set K : Submodule E (Fin n → E) := D.dualCoannihilator with hK
  have hKset : ∀ y, y ∈ K ↔ ∀ φ ∈ S, φ y = 0 := by
    intro y
    rw [hK, Submodule.mem_dualCoannihilator]
    constructor
    · intro h φ hφ
      exact h φ (Submodule.subset_span hφ)
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set P : (Fin n → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ g with hP
  have hPK : ∀ y, P y ∈ K := fun y => (g y).2
  have hPid : ∀ k ∈ K, P k = k := by
    intro k hk
    have h1 := LinearMap.congr_fun hg ⟨k, hk⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h1
    simp [hP, h1]

  have hrow : ∀ i, (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈ D := by
    intro i
    have hmem : (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈
        K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      simp [hPid k hk]
    rwa [hK, Subspace.dualCoannihilator_dualAnnihilator_eq] at hmem
  have hcoord : ∀ i, u i = ∑ j, ι (P (Pi.single j 1) i) * u j := by
    intro i
    have h0 := dual_span_sum_eq_zero ι S u hu _ (hrow i)
    simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, map_sub, sub_mul,
      Finset.sum_sub_distrib, sub_eq_zero] at h0
    rw [← h0]
    simp [Pi.single_apply]
  have hu' : u = ∑ j, u j • (fun i => ι (P (Pi.single j 1) i)) := by
    funext i
    rw [hcoord i]
    simp [Finset.sum_apply, mul_comm]
  rw [hu']
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨P (Pi.single j 1), ?_, rfl⟩)
  exact (hKset _).1 (hPK _)

def formRight {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w : Fin n → E) : Module.Dual E (Fin n → E) where
  toFun y := Formalism.UG.hform σ J w y
  map_add' y z := by simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem formRight_apply {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w y : Fin n → E) : formRight σ J w y = Formalism.UG.hform σ J w y := rfl

private theorem hform_add_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hform_smul_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J x (c • y) = c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem hform_add_left_flag_measures' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x x' y : Fin n → A) :
    Formalism.UG.hform s J (x + x') y = Formalism.UG.hform s J x y + Formalism.UG.hform s J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

private theorem hform_smul_left_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J (c • x) y = s c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perpSet_baseChange : ∀ (E A : Type) [Field E] [CommRing A] (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (W : Submodule E (Fin n → E)), (∀ e, s (ι e) = ι (σ e)) → perpSet s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E)))) = (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' perpSet σ J W) : Set (Fin n → A)) := by
  intro E A _ _ σ s ι n J W hs
  classical

  have key : ∀ w z : Fin n → E, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) (fun i => ι (z i)) =
      ι (Formalism.UG.hform σ J w z) := by
    intro w z

    simp only [Formalism.UG.hform, Matrix.map_apply, hs, map_sum, map_mul]

  have pair : ∀ (w : Fin n → E) (y : Fin n → A), Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y =
      ∑ j, ι (formRight σ J w (Pi.single j 1)) * y j := by
    intro w y

    simp only [formRight_apply, Formalism.UG.hform, Matrix.map_apply, hs, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
    Finset.sum_mul]
    rw [Finset.sum_comm]
  have hset : {z : Fin n → E | ∀ φ ∈ formRight σ J '' (W : Set (Fin n → E)), φ z = 0} = perpSet σ J W := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, perpSet, formRight_apply, SetLike.mem_coe]
  ext y
  constructor
  · intro hy
    rw [SetLike.mem_coe, ← hset]
    apply mem_span_of_forms ι _ y
    rintro φ ⟨w, hw, rfl⟩
    rw [← pair]
    exact hy _ (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro hy
    rw [SetLike.mem_coe] at hy
    have hgen : ∀ w ∈ W, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y = 0 := by
      intro w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        rw [key, hz w hw, map_zero]
      | zero => simp [Formalism.UG.hform]
      | add x x' _ _ hx hx' => rw [hform_add_right_flag_measures, hx, hx', add_zero]
      | smul c x _ hx => rw [hform_smul_right_flag_measures, hx, mul_zero]
    simp only [perpSet, Set.mem_setOf_eq]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp [Formalism.UG.hform]
    | add x x' _ _ hx hx' => rw [hform_add_left_flag_measures', hx, hx', add_zero]
    | smul c x _ hx => rw [hform_smul_left_flag_measures, hx, mul_zero]

end GlobalTheory.PerpBaseChange
end

section

open Formalism.MainNotions.S NumberField GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.TensDer

theorem hasDerivAt_orbit_tens : ∀ (B : RowsAut) (E : gInf B) (u u' : ∀ v, B.H v), (∀ v, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v)) (u' v) 0) → (∀ v, B.σ v 1 = 1) → open Classical in HasDerivAt (orbit B E (B.tens u)) (∑ v, B.tens (Function.update u v (u' v))) 0 := by
  intro B E u u' hd h1
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hfun : orbit B E (B.tens u) =
      fun t => (m.restrictScalars ℝ) (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) := by
    funext t
    have := B.tens_spec.2.1
    rw [ContinuousMultilinearMap.coe_restrictScalars, hm]
    unfold orbit
    rw [this]
    congr 1
  have h0 : (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0) = u := by
    funext v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
  have hpi : HasDerivAt (fun t v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) u' 0 :=
    hasDerivAt_pi.2 hd
  have hF := (m.restrictScalars ℝ).hasFDerivAt (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0)
  have := hF.comp_hasDerivAt (0 : ℝ) hpi
  rw [hfun]
  rw [h0, ContinuousMultilinearMap.linearDeriv_apply] at this
  simp only [ContinuousMultilinearMap.coe_restrictScalars, Function.comp_def, hm] at this ⊢
  exact this

end GlobalTheory.TensDer
end
