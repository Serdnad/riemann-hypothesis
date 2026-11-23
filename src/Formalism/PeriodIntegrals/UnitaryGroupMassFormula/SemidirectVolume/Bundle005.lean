module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (z : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = algebraMap F R (Algebra.trace F E z) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r e
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_basis_holds : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _

theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J (c • x) y = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c := σ.commutes c
  rw [map_mul, hc]
  ring

theorem hE_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J x (c • y) = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def trForm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : LinearMap.BilinForm F (Fin M → E) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (hE σ J x y))
    (fun x x' y => by simp only [hE_add_left, map_add (f := _)])
    (fun c x y => by simp only [hE_smul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [hE_add_right, map_add (f := _)])
    (fun c x y => by simp only [hE_smul_right, ← Algebra.smul_def, map_smul])

theorem hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]

theorem trace_gram_nondegenerate : TraceGramND := by
  intro F E _ _ _ _ _ σ hCM M J hJ k b
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  have hG : (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))) =
      LinearMap.BilinForm.toMatrix b (trForm σ J) := by
    ext i j
    simp [trForm, LinearMap.BilinForm.toMatrix_apply]
  rw [hG, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro x hx
  have hrow : ∀ j, ∑ i, σ (x i) * J i j = 0 := by
    intro j
    apply (traceForm_nondegenerate F E).1
    intro c
    have h1 := hx (Pi.single j c)
    simp only [trForm, LinearMap.mk₂_apply] at h1
    rw [Algebra.traceForm_apply, ← hE_single]
    exact h1
  have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hrow j
  by_contra hx0
  have hne : (fun i => σ (x i)) ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simpa using this
  exact hJ.2 (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hv⟩)

end PI.VolSemiDirect.W.Cj
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem toMatrix'_lin (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  unfold Formalism.L2.SG.Sub.lin
  first
    | exact LinearMap.toMatrix'_mulVecLin _
    | exact LinearMap.toMatrix'_toLin' _
    | (ext i j; simp [LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct, Pi.single_apply])

theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  simp only [piMat, PG.Dat.Pi, map_add (f := _), LinearMap.toMatrix'_comp, toMatrix'_lin, Matrix.mul_assoc]

theorem mat_inv (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl

theorem continuous_piMat_inv [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  have hm : Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [piMat_eq, mat_inv]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

theorem continuous_piMat [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [piMat_eq]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)

theorem continuous_piG [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun s : S0 R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨(continuous_piMat (P := P) (T := T)).comp continuous_subtype_val,
    (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val⟩

end Cont

end PI.VolSemiDirect.W
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

theorem HA_ext {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g g' : HA R σ J}
    (h : ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) : g = g' :=
  Subtype.ext (Units.ext h)

theorem tupH_alt {E : Type} {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_last]

theorem tupH_e {E : Type} {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]

theorem tupH_f {E : Type} {M r : ℕ} (P : Frame E M r) (b : Fin r) :
    tupH P (Fin.natAdd (r + 1) b) = P.f b := by
  simp [tupH, Fin.append_right]

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_piG]
  have H := datR_hyp (R := R) hσσ hJ hP
  refine Fin.addCases (fun b0 => ?_) (fun b1 => ?_) b
  · refine Fin.lastCases ?_ (fun a => ?_) b0
    · rw [tupH_alt]; exact PG.Dat.unipotent_proj_fixes_normal H _
    · rw [tupH_e]; exact PG.Dat.Pi_e H _ a
  · rw [tupH_f]; exact PG.Dat.Pi_f H _ b1

theorem mat_mul (g g' : HA R σ J) : ((HA.mat R σ J (g * g') : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) * ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) := rfl

theorem piG_mat (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    ((HA.mat R σ J (piG hσσ hJ hP g hg) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = piMat (P := P) (T := T) g := rfl

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    piG hσσ hJ hP (g * g') ((S0 R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  apply HA_ext
  rw [mat_mul hσσ hJ hP, piG_mat, piG_mat, piG_mat, piMat, piMat, piMat, Pi_lin_mul hσσ hJ hP hg hg',
    LinearMap.toMatrix'_comp]

theorem spanR_eq {m : ℕ} (Y : Fin m → Fin M → E) :
    spanR (F := F) R Y Set.univ = Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  rw [spanR, Set.image_univ]

end R

end PI.VolSemiDirect.W
end
end
