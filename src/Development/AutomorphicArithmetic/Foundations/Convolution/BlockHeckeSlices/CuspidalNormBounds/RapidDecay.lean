module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelCount
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.ConvolutionTheory.BW

section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

private structure Good (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  sm : φ ∈ archSmooth K n
  cont : Continuous φ
  left : IsLeftInvariant φ
  lev : ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n), ∀ g, ∀ u ∈ U, φ (g * finEmb K n u) = φ g
  gr : ∃ N : ℕ, ∀ u : UEnv K n, HasGrowth (uAction u ⟨φ, sm⟩ : AdelicGLn.AdelicGL K n → ℂ) N
  cusp : IsCuspidal φ

private theorem Good.mod {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Good φ) : ∃ N, HasGrowth φ N := by
  obtain ⟨N, hN⟩ := hφ.gr
  have := hN 1
  rw [map_one] at this
  exact ⟨N, this⟩

private theorem siegel_le {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : Good φ) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) (N' : ℕ) :
    ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n, x ∈ Reduction.normOneGL (K := K) (n := n) →
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ‖φ x‖ ≤ C * (height x ^ N')⁻¹ := by
  obtain ⟨N₀, C₀, hC₀⟩ := hφ.mod
  obtain ⟨N, hN⟩ := hφ.gr
  have hdiff := exists_norm_diffSum_le_of_growth hφ.sm N hN
  exact exists_norm_le_height_pow_neg_siegel_of_root_bounds ⟨C₀, N₀, hC₀⟩ hω hωB ht
    (fun _ => exists_norm_le_siegel_root_of_diffSum hφ.cont hφ.left hφ.cusp hφ.lev hdiff hω hωB ht) N'

end

open GlobalTheory.CuspRep UpperTheory.V.Cm in
private theorem good_of {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {φ : Sm E n} (h : Umg φ)
    (hc : Cusp φ.1) : Good φ.1 := by
  let S : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E n k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E n (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E n k⁻¹ φ = φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E n k φ = φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine ⟨(smEq E n φ).2, GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n φ h.level, h.left, ⟨⟨S, h.level⟩, fun g u hu => ?_⟩, ?_, hc⟩
  · rw [UpperTheory.V.Fb.finEmb_eq]
    exact congrFun (congrArg Subtype.val (show GlobalTheory.CuspRep.finRep E n u φ = φ from hu)) g
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun u => ?_⟩
    have := hN (1 ⊗ₜ u)
    rw [uC_tmul, one_smul] at this
    exact this

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.rapidDecay :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.RapidDecay E := by
  intro E _ _ _ n φ hU hc N
  have h0 := good_of hU hc
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) n
  obtain ⟨C, hC⟩ := siegel_le h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγ1 : AdelicGLn.diagonal E n γ ∈ Reduction.normOneGL (K := E) (n := n) := Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩
  have h := hC b hb ρ hρ hs kk hkk _ (mul_mem hγ1 g.2) hxe
  rw [h0.left γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E n γ * g.1)
  have hq : PositivityTheory.Rg.Tf.Core.qht g ≤ height (AdelicGLn.diagonal E n γ * g.1) :=
    ciInf_le (f := fun γ : PositivityTheory.Rg.Tf.Core.Gam E n => height (((γ : Reduction.normOneGL (K := E) (n := n)) * g : Reduction.normOneGL (K := E) (n := n)) : AdelicGLn.AdelicGL E n))
      ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ ⟨⟨_, hγ1⟩, ⟨γ, rfl⟩⟩
  have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht g := le_ciInf fun _ => (height_pos _).le
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq N) (norm_nonneg _)).trans h
