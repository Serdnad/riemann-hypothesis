module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeStable

noncomputable def liftFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  LinearMap.rTensor D.host.E
    (show Af D.host.F →ₗ[D.host.F] AF D.host.F from LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F))

theorem liftFin_tmul (D : D7) (α : Af D.host.F) (m : D.host.E) :
    liftFin D (α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] m := rfl

theorem mul_pair_tmul (D : D7) (w : AE D) (α : Af D.host.F) (m : D.host.E) :
    w * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = liftFin D (finPart D w * (α ⊗ₜ[D.host.F] m)) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [zero_mul, RingHom.map_zero, zero_mul, LinearMap.map_zero]
  | tmul x e =>
    change _ = liftFin D ((sndA D.host.F x ⊗ₜ[D.host.F] e) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul]
    congr 1
    exact Prod.ext (mul_zero _) rfl
  | add x y hx hy => rw [add_mul, hx, hy, RingHom.map_add (f := _), add_mul, LinearMap.map_add (f := _)]

noncomputable def liftMul (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E →+ AE D :=
  (liftFin D).toAddMonoidHom.comp (AddMonoidHom.mulRight c)

theorem smul_mem_latO (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : AE D) (hw : finPart D w ∈ intAE D) :
    ∀ u ∈ latO S T LS LT P, w • u ∈ latO S T LS LT P := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => w • u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : latO S T LS LT P ≤ (latO S T LS LT P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun y => Matrix.of fun i j => liftMul D
        (α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j)) y)
      fun y y' => Matrix.ext fun i j => (liftMul D _).map_add y y'
    have hle : intAE D ≤ (latO S T LS LT P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, o • a,
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · ext i j
        change liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _ ⊗ₜ[D.host.F] _
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * HSpace.gram S k j) : WO S T) = Φ (finPart D w) :=
      Matrix.ext fun i j => mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

end GlobalTheory.LatticeStable
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CartanTrace

theorem star_trace_herm {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (x y : Matrix (Fin m) (Fin n) ℂ) :
    star (A * yᴴ * B * x).trace = (A * xᴴ * B * y).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

open scoped MatrixOrder in
theorem trace_pos {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < (A * xᴴ * B * x).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  obtain ⟨D, hD, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hB.isStrictlyPositive
  have e : (star C * C * xᴴ * (star D * D) * x).trace = ((D * x * Cᴴ)ᴴ * (D * x * Cᴴ)).trace := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine lt_of_le_of_ne (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg ?_
  intro h
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h.symm
  apply hx
  have hC' : IsUnit Cᴴ := hC.star
  have hD' := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hC'' := (Matrix.isUnit_iff_isUnit_det _).1 hC'
  have : x = D⁻¹ * (D * x * Cᴴ) * Cᴴ⁻¹ := by
    rw [Matrix.mul_assoc D, Matrix.nonsing_inv_mul_cancel_left _ _ hD',
      Matrix.mul_nonsing_inv_cancel_right _ _ hC'']
  rw [this, h0]; simp

variable {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}

theorem adj_mul (h : IsCartanInv G s) : sᴴ * G = G * s := by
  have := congrArg (· * s) h.2.1
  simpa only [Matrix.mul_assoc, h.1, Matrix.mul_one] using this

theorem adj_sq (h : IsCartanInv G s) : sᴴ * sᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, h.1, Matrix.conjTranspose_one]

theorem herm (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : sᴴ * Gᴴ = sᴴ * G := by
    rw [← Matrix.conjTranspose_mul, adj_mul h]; exact h.2.2.isHermitian
  have := congrArg (sᴴ * ·) h1
  simpa only [← Matrix.mul_assoc, adj_sq h, Matrix.one_mul] using this

theorem inv_mul_adj (h : IsCartanInv G s) : G⁻¹ * sᴴ = (G * s)⁻¹ := by
  rw [← adj_mul h, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (adj_sq h)]

theorem form_cplxO {m n : ℕ} {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ}
    {ξ : ℂ} (hξ : ξ.re = 0) (hS : IsCartanInv GS sS) (hT : IsCartanInv GT sT)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re =
      ξ.im * ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x).trace.re := by
  have e : GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x =
      (-Complex.I) • ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x) := by
    rw [← inv_mul_adj hS, ← adj_mul hT]
    simp only [cplxO, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Complex.star_def, Complex.conj_I]
  rw [e, Matrix.trace_smul]
  simp [hξ]

theorem cplxO_pos : ∀ (m n : ℕ) (GS sS : Matrix (Fin n) (Fin n) ℂ) (GT sT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ), ξ.re = 0 → 0 < ξ.im → IsCartanInv GS sS → IsCartanInv GT sT → (∀ x : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * xᴴ * GT * x).trace).re = 0) ∧ (∀ x : Matrix (Fin m) (Fin n) ℂ, cplxO sS sT (cplxO sS sT x) = -x) ∧ (∀ x y : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re = (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * y).trace).re) ∧ ∀ x : Matrix (Fin m) (Fin n) ℂ, x ≠ 0 → 0 < (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * x).trace).re := by
  intro m n GS sS GT sT ξ h0 h1 hS hT
  refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · have hi : GS⁻¹ᴴ = GS⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, herm hS]
    have := congrArg Complex.im (star_trace_herm hi (herm hT) x x)
    have h2 : (GS⁻¹ * xᴴ * GT * x).trace.im = 0 := by
      rw [Complex.star_def, Complex.conj_im] at this; linarith
    simp [h0, h2]
  · simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT.1, Matrix.one_mul, Matrix.mul_assoc, hS.1]
    simp
  · rw [form_cplxO h0 hS hT, form_cplxO h0 hS hT,
      ← star_trace_herm hS.2.2.inv.isHermitian hT.2.2.isHermitian x y]
    simp
  · rw [form_cplxO h0 hS hT]
    exact mul_pos h1 (Complex.pos_iff.1 (trace_pos hS.2.2.inv hT.2.2 x hx)).1

end GlobalTheory.CartanTrace
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_place_isSquare_and_not_isSquare :
    ∀ (F : Type) [Field F] [NumberField F] (δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → u ≠ 0 → ¬ IsSquare δ → ¬ IsSquare u → ¬ IsSquare (u * δ) → ∃ v, v ∉ S₀ ∧ IsSquare (algebraMap F (v.adicCompletion F) δ) ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ δ u S₀ hδ hu hδs hus huδs
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδs
  have hbasic := isQuad_basic F E δ θ σ hq
  have huE : ¬ IsSquare (algebraMap F E u) := fun h => (hbasic.2.2.2.2.2.1 u h).elim hus huδs
  have hu0E : algebraMap F E u ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hu
  obtain ⟨S, hS₀, hSunits⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu, Units.mk0 (u * δ) (mul_ne_zero hu hδ)} S₀
  have hgood : ∀ v, v ∉ S → ∀ x ∈ ({Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu,
      Units.mk0 (u * δ) (mul_ne_zero hu hδ)} : Finset Fˣ), v.valuation F (x : F) = 1 :=
    fun v hv x hx => (mem_sUnits F S x).mp (hSunits S subset_rfl x hx) v hv
  obtain ⟨hover, -, -⟩ := places_over F E
  obtain ⟨SE, hSE⟩ := hover S
  obtain ⟨w, hwS, hwu⟩ := GlobalTheory.T.exists_place_not_isSquare_adicCompletion E (algebraMap F E u) SE hu0E huE
  have hvS : w.under (𝓞 F) ∉ S := fun h => hwS ((hSE w).mpr h)
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hθ : algebraMap E (w.adicCompletion E) θ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).mpr hq.root_ne_zero
  have hnu : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) := by
    intro h
    apply hwu
    have h' := h.map φ
    rwa [hφ] at h'
  have hnuδ : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) := by
    intro h
    apply hwu
    have h' := h.map φ
    rw [hφ, map_mul, map_mul, ← hq.sq, map_pow] at h'
    obtain ⟨r, hr⟩ := h'
    refine ⟨r / algebraMap E (w.adicCompletion E) θ, ?_⟩
    rw [div_mul_div_comm, ← hr]
    field_simp
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
      (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (w.under (𝓞 F)) x
  have h2 : Valued.v (2 : (w.under (𝓞 F)).adicCompletion F) = 1 := by
    rw [show (2 : (w.under (𝓞 F)).adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm,
      hval]
    simpa using hgood _ hvS (Units.mk0 (2 : F) two_ne_zero) (Finset.mem_insert_self _ _)
  have hvu : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 u hu)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvuδ : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 (u * δ) (mul_ne_zero hu hδ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨s, hs⟩ := isSquare_mul_of_nonsquare_units F (w.under (𝓞 F)) h2 _ _ hvu hvuδ hnu hnuδ
  have ha : algebraMap F ((w.under (𝓞 F)).adicCompletion F) u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F _).injective).mpr hu
  refine ⟨w.under (𝓞 F), fun h => hvS (hS₀ h), ⟨s / algebraMap F _ u, ?_⟩, hnu⟩
  rw [div_mul_div_comm, ← hs, map_mul]
  field_simp

end GlobalTheory.QNorm
end
