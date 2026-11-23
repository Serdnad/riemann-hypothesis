module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem nC_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : nC (0 : Cinf E) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem nC_add' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : Cinf E) :
    nC (a + b) = nC a * nC b := by
  apply Units.ext
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem nC_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) (z : Cinf E) :
    (nC (t • z)).val = 1 + t • (!![0, z; 0, 0] : Matrix (Fin 2) (Fin 2) (Cinf E)) := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem cv_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E)
    (k : GL (Fin 2) (A E)) (t : ℝ) : (cv D k t).val = 1 + t • XB D k := by
  have h : ((kInf k)⁻¹).val * (kInf k).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cv, XB, Units.val_mul, nC_val', mul_add, add_mul, mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

theorem UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)),
        cv D k 0 = 1 ∧ (∀ s t, cv D k (s + t) = cv D k s * cv D k t) ∧ HasDerivAt (fun t => toL (cv D k t).val) (toL (XB D k)) 0 ∧
        Continuous fun k : GL (Fin 2) (A E) => toL (XB D k) := by
  intro E _ _ _ D k
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cv, nC_zero']
  · intro s t
    simp only [cv, add_smul, nC_add']
    group
  · have h : (fun t : ℝ => toL (cv D k t).val) =
        fun t : ℝ => toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) + t • toL (XB D k) := by
      funext t
      rw [cv_val']
      rfl
    rw [h]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (XB D k))).const_add
      (toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)))
  · have hK : Continuous fun k : GL (Fin 2) (A E) => kInf k := ContAut.continuous_map_pInf E 2
    have h1 : Continuous fun k : GL (Fin 2) (A E) => (kInf k).val := Units.continuous_val.comp hK
    have h2 : Continuous fun k : GL (Fin 2) (A E) => ((kInf k)⁻¹).val :=
      Units.continuous_val.comp hK.inv
    exact (h2.matrix_mul continuous_const).matrix_mul h1
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem inf_const (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (c : ℝ) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) (TR.infEq ℚ fun _ => c) =
      infEq E fun _ => (c : ℂ) := by
  funext w
  let f : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E)).comp
      ((TR.infEq ℚ).toRingHom.comp (Pi.constRingHom (InfinitePlace ℚ) ℝ)))
  let g : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((infEq E).toRingHom.comp ((Pi.constRingHom (InfinitePlace E) ℂ).comp Complex.ofRealHom))
  have hf : Continuous f := (continuous_apply w).comp
    (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.comp
      ((TR.continuous_infEq ℚ).comp (continuous_pi fun _ => continuous_id)))
  have hg : Continuous g := (continuous_apply w).comp
    ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal))
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact congrFun h c

private theorem re_const (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext v
  rw [Subsingleton.elim v Rat.infinitePlace]
  rfl

private theorem pInf_adeleMap (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : A ℚ) :
    pInf E (AdeleBaseChange.adeleMap ℚ E x) = fun _ => (re x : ℂ) := by
  have h : x.1 = TR.infEq ℚ fun _ => re x := by
    rw [← re_const]
    exact ((TR.infEq ℚ).apply_symm_apply x.1).symm
  change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1) = _
  rw [h, inf_const, RingEquiv.symm_apply_apply]

private theorem pInf_s {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Cinf E) :
    pInf E (GlobalTheory.CuspRep.sInf E x) = x := (infEq E).symm_apply_apply x

private theorem pFin_s {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Cinf E) :
    pFin E (GlobalTheory.CuspRep.sInf E x) = 0 := rfl

private theorem re_s (c : ℝ) : re (TR.sInf ℚ fun _ => c) = c :=
  congrFun ((TR.infEq ℚ).symm_apply_apply fun _ => c) Rat.infinitePlace

private theorem map_n {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R) (z : R)
    (hg : g.val = !![1, z; 0, 1]) (h : Matrix.GeneralLinearGroup (Fin 2) S) (hh : h.val = !![1, f z; 0, 1]) :
    Matrix.GeneralLinearGroup.map f g = h := by
  refine Units.ext ?_
  rw [hh]
  ext i j
  change f (g.val i j) = _
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp

private theorem step1 {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)) (t : ℝ) :
    k * infGL E 2 (cv D k t) = gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D))) * k := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_infGL]
    have h : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = nC (t • thInf D) :=
      map_n _ _ _ rfl _ (by rw [pInf_s]; rfl)
    rw [h]
    change kInf k * cv D k t = nC (t • thInf D) * kInf k
    simp only [cv, mul_assoc, mul_inv_cancel_left]
  · rw [map_mul, map_mul, pFin_infGL, mul_one]
    have h : Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = 1 := by
      refine map_n _ _ _ rfl _ ?_
      rw [pFin_s]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h, one_mul]

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) :
    em E (aE y) = aE (Units.map (AdeleBaseChange.adeleMap ℚ E : A ℚ →* A E) y) := by
  refine Units.ext ?_
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((aE y).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

private theorem step3 {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (t : ℝ) :
    AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D) =
      D.mkE 0 (TR.sInf ℚ fun _ => t * re (y : A ℚ)) := by
  refine ad_ext ?_ ?_
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pInf_s, pInf_adeleMap, pInf_adeleMap, re_s]
    change _ = _ * thInf D
    funext w
    simp [Pi.mul_apply, Pi.smul_apply]
    ring
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pFin_s, mul_zero]
    have : pFin E (AdeleBaseChange.adeleMap ℚ E (TR.sInf ℚ fun _ => t * re (y : A ℚ))) = 0 :=
      map_zero (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, zero_mul]

theorem UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)) (t : ℝ),
        em E (aE y) * k * infGL E 2 (cv D k t) = nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] * (em E (aE y) * k) := by
  intro E _ _ _ D y k t
  have h3 := step3 D y t
  have hn : nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] =
      gl (nU (AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D))) := by
    rw [h3]
    rfl
  rw [mul_assoc, step1, hn, ← mul_assoc, ← mul_assoc, em_aE, Pp.a_n]
  rfl
end
