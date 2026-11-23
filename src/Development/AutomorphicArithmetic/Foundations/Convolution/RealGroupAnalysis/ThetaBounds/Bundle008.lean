module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle006
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private noncomputable def euF {F : Type} [Field F] (z : TR.Rinf F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨fun w => Real.exp (t * z w), fun w => Real.exp (-(t * z w)),
    funext fun w => by simp [← Real.exp_add], funext fun w => by simp [← Real.exp_add]⟩

private noncomputable def euE {E : Type} [Field E] (s : Cinf E) (t : ℝ) : (Cinf E)ˣ :=
  ⟨fun w => Complex.exp (t * s w), fun w => Complex.exp (-(t * s w)),
    funext fun w => by simp [← Complex.exp_add], funext fun w => by simp [← Complex.exp_add]⟩

private theorem inf_scalarF {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F u) := by
  have h1 : TR.pInf F (TR.infId F u).val = u.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F u).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem inf_scalarE {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (u : (Cinf E)ˣ) :
    infGL E 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E u) := by
  have hd : infId E u =
      Matrix.GeneralLinearGroup.det (infGL E 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)) := by
    rw [det_infGL]
    congr 1
    exact Units.ext (by simp)
  have h1 : pInf E (infId E u : Ideles E) = u := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pInf_infGL]
    simp
  have h2 : pFin E (infId E u : Ideles E) = 1 := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pFin_infGL]
    simp
  refine ga_ext ?_ ?_
  · rw [pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem ex_zE {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : Cinf E) (t : ℝ) :
    ex (zE s) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (euE s t) := by
  apply Units.ext
  have e : t • Matrix.of (zE s) = Matrix.diagonal (fun _ : Fin 2 => t • s) := by
    ext i j w
    by_cases h : i = j <;> simp [zE, Matrix.diagonal_apply, h]
  change NormedSpace.exp (t • Matrix.of (zE s)) = _
  rw [e, Matrix.exp_diagonal]
  ext i j w
  by_cases h : i = j
  · subst h
    simp [euE, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  · simp [Matrix.diagonal_apply, h]

private theorem norm_euE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (s : Cinf E) (t : ℝ) (v : InfinitePlace F) :
    (∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      (euF (trI F s) t).val v := by
  have h : ∀ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      Real.exp (t * if w.comap (algebraMap F E) = v then 2 * (s w).re else 0) := by
    intro w
    split_ifs
    · change ‖Complex.exp (t * s w)‖ ^ 2 = _
      rw [Complex.norm_exp, ← Real.exp_nat_mul]
      simp
      ring_nf
    · simp
  simp only [h]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.cenExp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), CenExp F E := by
  intro F E _ _ _ _ _ _ _ D s
  refine ⟨fun t => infId E (euE s t), fun t => Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) t),
    ⟨fun a b => ?_, ?_⟩, fun t => ⟨?_, ?_⟩⟩
  · have h : euF (trI F s) (a + b) = euF (trI F s) a * euF (trI F s) b := by
      refine Units.ext (funext fun w => ?_)
      change Real.exp ((a + b) * _) = Real.exp (a * _) * Real.exp (b * _)
      rw [add_mul, Real.exp_add]
    change Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) (a + b)) = _
    rw [h, map_mul]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    by_cases e : i = j
    · subst e
      have h : HasDerivAt (fun t : ℝ => Real.exp (t * trI F s v)) (trI F s v) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (trI F s v)).exp
      simpa [zF, euF, Matrix.diagonal_apply] using h
    · simpa [zF, Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · rw [ex_zE, inf_scalarE]
  · obtain ⟨u, hu, hn⟩ := normInf F E D (euE s t)
    have e : u = euF (trI F s) t := Units.ext (funext fun v => by rw [hu, norm_euE])
    rw [hn, e, inf_scalarF]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Iwa F := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  refine ⟨hKc, fun C hC => ?_⟩
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hS : IsCompact ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)) :=
    (hC.prod hKc).image continuous_mul
  refine ⟨Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹'
    ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)))),
    ((hemb.isCompact_preimage hS).image e.symm.continuous).image continuous_fst, fun g hg => ?_⟩
  obtain ⟨b, a, k, hk, rfl⟩ := M.iwa F g
  refine ⟨b, a, ?_, k, hk, rfl⟩
  refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
  change ((e (a, b) : M.Bor F) : G1 F) ∈ (fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)
  rw [he]
  refine ⟨(nU b * mD a * k, k⁻¹), ⟨hg, ?_⟩, by simp⟩
  change k⁻¹ ∈ KK F
  rw [hK] at hk ⊢
  exact (M.Ks F).inv_mem hk
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Level W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  obtain ⟨κ, hκc, hκ⟩ := finTr F E D
  have hfo : IsOpen {k | TR.finRep F 2 k f = f} := (π.cusp f hf).1.level
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), TR.finRep F 2 (κ k) f = f := by
    have hm : {k | TR.finRep F 2 k f = f} ∈ 𝓝 (κ 1) := hfo.mem_nhds (by simp)
    exact hκc.continuousAt.eventually hm
  let S : Subgroup (GL (Fin 2) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E 2 (k * l) Φ = Φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E 2 k⁻¹ Φ = Φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E 2 k Φ = Φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_of_mem_nhds (H := S) (g := 1) ?_
  filter_upwards [lLevel F E D W φ, h1] with k hL hk
  refine Subtype.ext (funext fun g => ?_)
  change Φ.1 (g * finGL E 2 k) = Φ.1 g
  rw [hΦ, transl F E D W M, hL, hκ k]
  exact congrFun (congrArg (fun u => lift W M u φ) (congrArg Subtype.val hk)) g
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical ContDiff

namespace UpperTheory.ConvolutionTheory.R2.Ff

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private noncomputable def invL (x : Lie E 2) : Lie E 2 := toL ((Matrix.of x)⁻¹)

private theorem invL_val (u : GL (Fin 2) (Cinf E)) : invL (toL u.val) = toL (u⁻¹).val := by
  simp [invL, Matrix.coe_units_inv]

private theorem contDiffOn_invL : ContDiffOn ℝ ∞ (invL (E := E)) (invSet E 2) := by
  have hdet : ContDiffOn ℝ ∞ (fun x : Lie E 2 => Ring.inverse (Matrix.of x).det) (invSet E 2) := by
    intro x hx
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (Matrix.of x).det :=
      hu ▸ contDiffAt_ringInverse ℝ u
    exact (h1.comp x contDiff_det.contDiffAt).contDiffWithinAt
  have hent : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => x i j := fun i j =>
    (contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)
  have hadj : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => (Matrix.adjugate (Matrix.of x)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
    · exact hent 1 1
    · exact (hent 0 1).neg
    · exact (hent 1 0).neg
    · exact hent 0 0
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hdet.mul (hadj i j).contDiffOn).congr fun x _ => ?_
  simp [invL, Matrix.inv_def]

private theorem chart_eq (Φ : GL (Fin 2) (A E) → ℂ) (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    chart Φ g = chart Φ (g * infGL E 2 u) ∘ lmul (toL (u⁻¹).val) := by
  rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem fd {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    DifferentiableAt ℝ (chart Φ g) (toL u.val) ∧
      ∀ Z, fderiv ℝ (chart Φ g) (toL u.val) Z = T (lmul (toL (u⁻¹).val) Z) (g * infGL E 2 u) := by
  have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E 2 := u.inv_mul
  have hd : DifferentiableAt ℝ (chart Φ (g * infGL E 2 u)) (lmul (toL (u⁻¹).val) (toL u.val)) := by
    rw [e1]; exact (h _).1
  have hc := hd.comp (toL u.val) (lmul (toL (u⁻¹).val)).differentiableAt
  rw [← chart_eq] at hc
  refine ⟨hc, fun Z => ?_⟩
  rw [chart_eq Φ g u, fderiv_comp _ hd (lmul (toL (u⁻¹).val)).differentiableAt, e1,
    ContinuousLinearMap.fderiv]
  exact (h _).2 _

private theorem diffOn {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) : DifferentiableOn ℝ (chart Φ g) (invSet E 2) := by
  intro x hx
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  exact (fd h g u).1.differentiableWithinAt

private theorem T_apply (T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)) (b : Module.Basis (Fin (Module.finrank ℝ (Lie E 2))) ℝ (Lie E 2))
    (Y : Lie E 2) (h : GL (Fin 2) (A E)) : T Y h = ∑ j, (b.repr Y j) • T (b j) h := by
  conv_lhs => rw [← b.sum_repr Y]

  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]

private theorem smN (S : Submodule ℂ (GL (Fin 2) (A E) → ℂ))
    (hS : ∀ Φ ∈ S, ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ), (∀ X, T X ∈ S) ∧
      ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (n : ℕ) : ∀ Φ ∈ S, ∀ g, ContDiffOn ℝ n (chart Φ g) (invSet E 2) := by
  induction n with
  | zero =>
    intro Φ hΦ g
    obtain ⟨T, -, h⟩ := hS Φ hΦ
    rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (diffOn h g).continuousOn
  | succ n ih =>
    intro Φ hΦ g
    obtain ⟨T, hT, h⟩ := hS Φ hΦ
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet).2 ⟨diffOn h g, by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun Z => ?_
    let b := Module.finBasis ℝ (Lie E 2)
    have hinv : ContDiffOn ℝ n (invL (E := E)) (invSet E 2) :=
      contDiffOn_invL.of_le (by exact_mod_cast le_top)
    have key : ContDiffOn ℝ n (fun x => ∑ j, (b.repr (rmul Z (invL x)) j) • chart (T (b j)) g x) (invSet E 2) :=
      ContDiffOn.sum fun j _ => ContDiffOn.smul
        ((LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn hinv)) (ih _ (hT _) g)
    refine key.congr fun x hx => ?_
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [(fd h g u).2 Z, T_apply T b, invL_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chart_val]
    rfl

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.smCrit :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], SmCrit E := by
  intro E _ _ _ S hc hd Φ hΦ g
  refine contDiffOn_infty.2 fun n => smN S (fun Φ hΦ => ?_) n Φ hΦ g
  obtain ⟨T, hT, h⟩ := hd Φ hΦ
  exact ⟨T, hT, smFre E Φ T (fun X g => hc _ (hT X) g) h⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.oneOf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OneOf F E := by
  intro F E _ _ _ _ _ _ _ D y hy
  obtain ⟨u, hu, hn⟩ := normInf F E D (Matrix.GeneralLinearGroup.det y)
  have hu1 : u = 1 := by
    refine Units.ext (funext fun v => ?_)
    rw [hu v]
    have h1 : ∀ w : InfinitePlace E, ‖(Matrix.GeneralLinearGroup.det y).val w‖ = 1 := hy
    change _ = (1 : ℝ)
    refine Finset.prod_eq_one fun w _ => ?_
    split_ifs
    · rw [h1 w, one_pow]
    · rfl
  change ideleNorm F E (Matrix.GeneralLinearGroup.det (infGL E 2 y)) = 1
  rw [det_infGL, hn, hu1, map_one]
end
