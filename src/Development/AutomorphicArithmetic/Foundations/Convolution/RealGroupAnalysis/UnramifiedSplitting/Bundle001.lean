module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle008
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.H

variable {K : Type} [Field K] [NumberField K]

private theorem sg_fst (v : P K) (x : Kv v) : (sg v x).1 = 0 := rfl

private theorem sg_snd_self (v : P K) (x : Kv v) : (sg v x).2 v = x := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x v = x
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_same]

private theorem sg_snd_ne (v : P K) (x : Kv v) {w : P K} (h : w ≠ v) : (sg v x).2 w = 0 := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x w = 0
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_of_ne h]

private theorem ext_a {a b : A K} (h1 : a.1 = b.1) (h2 : ∀ w : P K, a.2 w = b.2 w) : a = b :=
  Prod.ext h1 (FiniteAdeleRing.ext K h2)

private theorem sg_add (v : P K) (x y : Kv v) : sg v (x + y) = sg v x + sg v y := by
  refine ext_a (by change 0 = (sg v x).1 + (sg v y).1; simp [sg_fst]) fun w => ?_
  by_cases h : w = v
  · subst h
    change _ = (sg w x).2 w + (sg w y).2 w
    simp only [sg_snd_self]
  · change _ = (sg v x).2 w + (sg v y).2 w
    simp only [sg_snd_ne _ _ h, add_zero]

private theorem sg_mul (v : P K) (a : A K) (x : Kv v) : a * sg v x = sg v (cp v a * x) := by
  refine ext_a (by change a.1 * (sg v x).1 = _; simp [sg_fst]) fun w => ?_
  change a.2 w * (sg v x).2 w = _
  by_cases h : w = v
  · subst h
    simp only [sg_snd_self]; rfl
  · simp only [sg_snd_ne _ _ h, mul_zero]

private theorem cp_sg (v : P K) (x : Kv v) : cp v (sg v x) = x := sg_snd_self v x

private theorem idl_eq (v : P K) (x : (Kv v)ˣ) :
    ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1) := by
  refine ext_a ?_ fun w => ?_
  · change (1 : InfiniteAdeleRing K) = 1 + (sg v _).1
    rw [sg_fst, add_zero]
  · change (idl v x : (A K)ˣ).val.2 w = 1 + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [sg_snd_self]
      have : (localIdele K w x).val.2 w = x := by
        classical
        exact Pi.mulSingle_eq_same w _
      change (localIdele K w x).val.2 w = _
      rw [this]; ring
    · rw [sg_snd_ne _ _ h, add_zero]
      have : (localIdele K v x).val.2 w = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne h _
      exact this

private theorem cont_sg (v : P K) : Continuous (sg v) :=
  continuous_const.prodMk (GroundTheory.Global.continuous_finiteAdeleSingleAdd (K := K) v)

private theorem lc_fst (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  have h : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K)) (lc v g) = 1 := by
    change Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K))
      (finGL K 2 (locGL K 2 v g)) = 1
    rw [← Fb.finEmb_eq]
    exact congrArg Prod.fst
      (GroundTheory.Automorphic.AutomorphicForm.prodEquiv_finEmb (locGL K 2 v g))
  exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing K) => x.val i j) h

private theorem lc_snd (v w : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).2 w =
      (Matrix.GeneralLinearGroup.map (pLoc K w) (locGL K 2 v g)).val i j := by
  have h := pFin_finGL (E := K) (a := 2) (locGL K 2 v g)
  have e : ((lc v g).val i j).2 = (locGL K 2 v g).val i j :=
    congrArg (fun x : GL (Fin 2) (Af K) => x.val i j) h
  rw [e]
  rfl

private theorem one_fst (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem one_snd (w : P K) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w = (1 : Matrix (Fin 2) (Fin 2) (Kv w)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem lc_entry (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j +
      sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j) := by
  refine ext_a ?_ fun w => ?_
  · change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 + (sg v _).1
    rw [lc_fst, sg_fst, add_zero, one_fst]
  · rw [lc_snd]
    change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, sg_snd_self, one_snd]
      ring
    · rw [pLoc_locGL_of_ne h, sg_snd_ne _ _ h, add_zero, one_snd]
      rfl

private theorem ab_idl (v : P K) (x : (Kv v)ˣ) : ab (idl v x) = ‖(x : Kv v)‖ := by
  have e : idl v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : P K) (x : Kv v) (n : ℤ) (h : Valued.v x = WithZero.exp n) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  rfl

private theorem ab_unif (v : P K) (ϖ : (Kv v)ˣ) (h : IsU ϖ) :
    ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [ab_idl, norm_of_val v _ (-1) h, _root_.zpow_neg_one]

private theorem ab_unit (v : P K) (x : (Kv v)ˣ) (h : Valued.v (x : Kv v) = 1) : ab (idl v x) = 1 := by
  rw [ab_idl, norm_of_val v _ 0 (by simpa using h), zpow_zero]

private theorem cont_val_lc (v : P K) :
    Continuous fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K)) := by
  refine continuous_matrix fun i j => ?_
  simp only [lc_entry]
  refine continuous_const.add ((cont_sg v).comp (Continuous.sub ?_ continuous_const))
  exact Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Kv v))) i j

private theorem cont_lc (v : P K) : Continuous (lc v) := by
  refine Units.continuous_iff.2 ⟨cont_val_lc v, ?_⟩
  have e : (fun g : GL (Fin 2) (Kv v) => (((lc v g)⁻¹ : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) =
      (fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) ∘
        fun g => g⁻¹ := by
    funext g
    simp only [Function.comp, map_inv]
  exact e ▸ (cont_val_lc v).comp continuous_inv

end UpperTheory.ConvolutionTheory.R2.H

theorem UpperTheory.ConvolutionTheory.R2.H.sgLaws :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∀ x y, sg v (x + y) = sg v x + sg v y) ∧ (∀ (a : A K) x, a * sg v x = sg v (cp v a * x)) ∧ (∀ x, cp v (sg v x) = x) ∧
      (∀ x, ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1)) ∧
      (∀ (g : GL (Fin 2) (Kv v)) i j, (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j + sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j)) ∧
      (∀ ϖ, IsU ϖ → ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) ∧ (∀ x : (Kv v)ˣ, Valued.v (x : Kv v) = 1 → ab (idl v x) = 1) ∧
      (∀ x, (sg v x).1 = 0 ∧ ∀ v' ≠ v, (sg v x).2 v' = 0) ∧ Continuous (lc v) ∧ Continuous (sg v) := by
  intro K _ _ v
  exact ⟨sg_add v, sg_mul v, cp_sg v, idl_eq v, lc_entry v, ab_unif v, ab_unit v,
    fun x => ⟨sg_fst v x, fun _ h => sg_snd_ne v x h⟩, cont_lc v, cont_sg v⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem aeInt {K : Type} [Field K] [NumberField K] (x : A K) :
    ∀ᶠ v : P K in cofinite, cp v x ∈ v.adicCompletionIntegers K :=
  x.2.2

private theorem aeKAt {K : Type} [Field K] [NumberField K] (g : GL (Fin 2) (A K)) :
    ∀ᶠ v in cofinite, KAt v g := by
  have h1 : ∀ᶠ v : P K in cofinite, ∀ i j, cp v (g.val i j) ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => aeInt _
  have h2 : ∀ᶠ v : P K in cofinite, ∀ i j, cp v ((g⁻¹).val i j) ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => aeInt _
  filter_upwards [h1, h2] with v a b
  rw [KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  refine ⟨a, fun i j => ?_⟩
  rw [← map_inv]
  exact b i j

private theorem aeFix {K : Type} [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ)
    (hf : IsOpen {k : GL (Fin 2) (Af K) | ∀ g, f (g * finGL K 2 k) = f g}) :
    ∀ᶠ v in cofinite, Fix v f := by
  obtain ⟨S, hU⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1)
    (hf.mem_nhds (show (1 : GL (Fin 2) (Af K)) ∈ _ from fun g => by simp))
  filter_upwards [S.eventually_cofinite_notMem] with w hw g k hk
  have h0 : ((1 : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  exact hU (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev 2 w h0 hk, fun x hx =>
    pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _⟩) g

theorem UpperTheory.ConvolutionTheory.R2.H.aeK :
    ∀ (K : Type) [Field K] [NumberField K], (∀ g : GL (Fin 2) (A K), ∀ᶠ v in cofinite, KAt v g) ∧ (∀ a : (A K)ˣ, ∀ᶠ v in cofinite, KAt v (dM a)) ∧
      ∀ f : GL (Fin 2) (A K) → ℂ, IsOpen {k : GL (Fin 2) (Af K) | ∀ g, f (g * finGL K 2 k) = f g} → ∀ᶠ v in cofinite, Fix v f := by
  intro K _ _
  exact ⟨aeKAt, fun a => aeKAt _, aeFix⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem psi_sg {K : Type} [Field K] [NumberField K] (v : P K) (x : Kv v) :
    ψ (sg v x) = UpperTheory.V.Af.Smo.psiL v x := rfl

private theorem val_ae {K : Type} [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    ∀ᶠ v : P K in cofinite, Valued.v (algebraMap K (Kv v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) a⁻¹
  filter_upwards [h1.compl_mem_cofinite, h2.compl_mem_cofinite] with v hv1 hv2
  have e : Valued.v (algebraMap K (Kv v) a) = v.valuation K a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  have n1 : v.valuation K a ≤ 1 := not_lt.1 hv1
  have n2 : (v.valuation K a)⁻¹ ≤ 1 := by
    have : v.valuation K a⁻¹ ≤ 1 := not_lt.1 hv2
    rwa [map_inv₀] at this
  have h0 : v.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  exact le_antisymm n1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 n2)

private theorem good_of_goodAt {K : Type} [Field K] [NumberField K] (v : P K)
    (h : UpperTheory.V.Af.Smo.GoodAt v (UpperTheory.V.Af.Smo.psiL v)) :
    Good fun x : Kv v => ψ (sg v x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [psi_sg]
    exact AddChar.map_add_eq_mul _ x y
  · exact (psi_sg v x).trans (h1 x hx)
  · by_contra hni
    have hlt : 1 < Valued.v x := not_le.1 hni
    obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
    obtain ⟨y, hy, hy1⟩ := h2 ϖ hϖ
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hlt
      exact not_lt_zero' hlt
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hxe : WithZero.exp (1 : ℤ) ≤ Valued.v x := by
      rw [← WithZero.exp_log hv0]
      rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega
    have hyv : Valued.v (ϖ * y) ≤ 1 := hy
    rw [map_mul, hϖ] at hyv
    have hye : Valued.v y ≤ WithZero.exp (1 : ℤ) := by
      have := mul_le_mul_right hyv (WithZero.exp (1 : ℤ))
      rwa [← mul_assoc, ← WithZero.exp_add, show (1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero,
        one_mul, mul_one] at this
    have hc : IsInt (y * x⁻¹) := by
      change Valued.v (y * x⁻¹) ≤ 1
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ (hye.trans hxe) zero_le'
    have := hx _ hc
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    exact hy1 ((psi_sg v y).symm.trans this)

theorem UpperTheory.ConvolutionTheory.R2.H.gdAe :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K), δ ≠ 0 → ∀ᶠ v in cofinite, Gd δ v := by
  intro K _ _ δ hδ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  filter_upwards [(UpperTheory.V.Af.Smo.psiLoc K).2, val_ae (2 : K) h2, val_ae δ hδ] with v hg ht hd
  rw [map_ofNat] at ht
  exact ⟨good_of_goodAt v hg, ht, hd⟩
end
