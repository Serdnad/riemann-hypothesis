module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle028
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle026

@[expose] public section

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem siegelOrb : SiegelOrb := by
  intro n Z hZ
  obtain ⟨S, hSS, hSu⟩ := exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef
  have hX : Xᴴ = X := conj_half_smul Z
  have hSu' : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSu.star
  refine ⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩
  · rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]
    simp [nU, mM]
  · unfold actZ
    rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
    simp only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    rw [Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu',
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]
    have hc : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
      norm_num
    rw [hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
    norm_num

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacF

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem cpos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (hl0 : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 hl0; positivity

theorem tabs {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem rot_DG (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, 0 < Real.cos (φ j)) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : 0 < cLoc l τ := cpos hl0
  have hta : |tLoc l τ| = cLoc l τ := tabs
  have ht2 : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← hta, sq_abs]
  have hσ : ∀ a, (VacC.sigR ε a) ^ 2 = 1 := by intro a; unfold VacC.sigR; split_ifs <;> norm_num
  have hX1 : (dR fun j => Real.tan (φ j))ᴴ = dR fun j => Real.tan (φ j) := dR_conjTranspose _
  have hX2 : (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))ᴴ = dR fun j => -(Real.sin (φ j) * Real.cos (φ j)) :=
    dR_conjTranspose _
  have hDd : IsUnit (dR fun j => (Real.cos (φ j))⁻¹).det := by
    rw [isUnit_iff_ne_zero, dR, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      have := (hφ j).ne'; exact_mod_cast inv_ne_zero this
  set g1 := mkG (nU (dR fun j => Real.tan (φ j))) (inG_nU _ hX1) with hg1
  set g2 := mkG (nbar (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) (inG_nbar _ hX2) with hg2
  set g3 := mkG (mM (dR fun j => (Real.cos (φ j))⁻¹)) (inG_mM _ hDd) with hg3
  have hk : mkG (kth φ) (inK_kth φ).1 = g1 * g2 * g3 := by
    apply Subtype.ext; apply Units.ext
    exact kth_decomp φ (fun j => (hφ j).ne')
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) := isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc hta K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL (g1 * g2) g3 _ hf0,
    hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 g2 _ (hL.1 g3 _ hf0)]
  have h3 : L g3 (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (n := n) (K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank)
        (fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2)) := by
    rw [hlev g3 _ hDd rfl _ hf0]
    exact levF_diag e (fun j => (Real.cos (φ j))⁻¹) (fun j => inv_pos.2 (hφ j)) K _
  have hf3 := hL.1 g3 _ hf0
  rw [h3] at hf3 ⊢
  set K1 : ℂ := K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank with hK1
  set γ1 : Fin V.rank → Fin n → ℂ := fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2) with hγ1
  have hre1 : ∀ a j, 0 < (γ1 a j).re := by
    intro a j
    rw [hγ1]; simp only
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have := inv_pos.2 (hφ j); positivity
  set γ2 : Fin V.rank → Fin n → ℂ := fun a j => ((-tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ1 a j -
    Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.sin (φ j) * Real.cos (φ j) : ℝ) : ℂ) with hγ2
  have hX2' : -(dR fun j => -(Real.sin (φ j) * Real.cos (φ j))) = dR fun j => Real.sin (φ j) * Real.cos (φ j) := by
    rw [dR_neg]; congr 1; funext j; ring
  have hin : (fun v => chN ε (tLoc l τ) (-(dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) v *
      ftLoc ε (-tLoc l τ) (DG K1 γ1) v) = DG (K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j)) γ2 := by
    funext v
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre1, hX2']
    exact chN_DG ε (tLoc l τ) (fun j => Real.sin (φ j) * Real.cos (φ j)) _ _ v
  have hre2 : ∀ a j, 0 < (γ2 a j).re := by
    intro a j
    have e : γ2 a j = ((((-tLoc l τ) ^ 2 * (VacC.sigR ε a) ^ 2 / (cLoc l τ * ((Real.cos (φ j))⁻¹) ^ 2)) : ℝ) : ℂ) -
        Complex.I * (((tLoc l τ * VacC.sigR ε a * (Real.sin (φ j) * Real.cos (φ j))) : ℝ) : ℂ) := by
      rw [hγ2, hγ1]; push_cast; ring
    rw [e, Complex.sub_re, Complex.ofReal_re, Complex.re_mul_ofReal, Complex.I_re, zero_mul, sub_zero, hσ a, mul_one, neg_sq]
    have htne : tLoc l τ ≠ 0 := by intro h0; rw [h0, abs_zero] at hta; linarith
    have := inv_pos.2 (hφ j)
    positivity
  set K2 : ℂ := K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j) with hK2
  set γ3 : Fin V.rank → Fin n → ℂ := fun a j => ((tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ2 a j with hγ3
  set C0 : ℂ := ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) with hC0
  have h2 : (fun u => C0 * ftLoc ε (tLoc l τ) (DG K2 γ2) u) = DG (C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j))) γ3 := by
    funext u
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre2]
    unfold DG
    ring
  have hf2 := hL.1 g2 _ hf3
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2] at hf2
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2]
  rw [hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 _ hX1 rfl _ hf2]
  funext u
  refine (chN_DG ε (tLoc l τ) (fun j => Real.tan (φ j)) _ _ u).trans ?_
  have hγ4 : (fun a j => γ3 a j - Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.tan (φ j) : ℝ) : ℂ)) =
      fun _ _ => ((cLoc l τ : ℝ) : ℂ) := by
    funext a j
    rw [hγ3, hγ2, hγ1]
    simp only
    rw [Real.tan_eq_sin_div_cos]
    exact coord_gamma (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
      (Real.sin_sq_add_cos_sq _)
  have hK : C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j)) =
      K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)) := by
    have p1 : (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank = ∏ _a : Fin V.rank, ∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have p2 : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) =
        ∏ _a : Fin V.rank, ∏ _j : Fin n, (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) := by
      rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin,
        ← pow_mul, ← pow_mul]
      ring_nf
    have hc1 : ∀ a j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / γ1 a j) * ((Real.pi : ℂ) / γ2 a j) *
        (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) =
        (Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ) := by
      intro a j
      rw [hγ2, hγ1]
      simp only
      rw [coord_const (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
        (Real.sin_sq_add_cos_sq _), rhoT_eq (tLoc l τ) (cLoc l τ) hta hc ε a]
      push_cast
      ring
    rw [hC0, hK2, hK1, p1, p2, ← Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun j _ => hc1 a j))]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hγ4, hK]

end PositivityTheory.Rg.Sw.Glob.VacF
end
end

section

noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def DBoundPQ : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X)) ∧
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p' ∈ N, p'.2 ∈ stripS X → ∀ u, ‖famPQ ε t c e p q p'.1 X p'.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

namespace DBoundBH

open DBoundH DBoundAH

variable {n : ℕ}

theorem isOpen_stripS (X : Fin n → ℝ) : IsOpen (stripS X) := by
  have : stripS X = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by ext z; simp [stripS]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_abs.comp (Complex.continuous_im.mul continuous_const))) continuous_const

private theorem entC_mR_mul_aC_univ_prod_stripS (X : Fin n → ℝ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => mR p.1 * aC X p.2) := by
  apply entC_mul
  · intro i j
    exact (Continuous.matrix_elem (mR_cont.comp continuous_fst) i j).continuousOn
  · intro i j
    apply Continuous.continuousOn
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases h : i = j <;> simp [aC, Matrix.diagonal_apply, h] <;> fun_prop

theorem ptZ_entC (X : Fin n → ℝ) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => ptZ p.1 X p.2 s) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h11 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₁) :=
    fun i j => hM (Sum.inl i) (Sum.inl j)
  have h12 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₂) :=
    fun i j => hM (Sum.inl i) (Sum.inr j)
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  have hden : ∀ p ∈ Set.univ ×ˢ stripS X,
      ((mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂).det ≠ 0 := by
    intro p hp
    rcases hs with rfl | rfl
    · exact (dSieg n p.1 X p.2 hp.2).2.2.1
    · exact (dSieg n p.1 X p.2 hp.2).2.2.2
  exact entC_mul (entC_add (entC_mul h11 (entC_const _ _)) h12)
    (entC_inv (entC_add (entC_mul h21 (entC_const _ _)) h22) hden)

private theorem entC_toBlocks_smul_add_univ_prod_stripS (X : Fin n → ℝ) (s : ℂ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ =>
      (mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  exact entC_add (entC_mul h21 (entC_const _ _)) h22

theorem jC_contOn (X : Fin n → ℝ) (e : ℤ) (p q : ℕ) :
    ContinuousOn (fun p' : GR n × ℂ => jC e p q p'.1 X p'.2) (Set.univ ×ˢ stripS X) := by
  have h0 : ContinuousOn (fun x : GR n × ℂ => (mR x.1 * aC X x.2).det ^ e) (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_mR_mul_aC_univ_prod_stripS X)).zpow₀ _ fun x _ => Or.inl (det_bigM_ne x.1 X x.2)
  have h1 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(p : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X Complex.I)).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.1
  have h2 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * -Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(q : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X (-Complex.I))).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.2
  exact (h0.mul h1).mul h2

private theorem re_I_mul_ofReal_mul_eq_neg_mul_im (c : ℝ) (w : ℂ) : (Complex.I * c * w).re = -(c * w.im) := by
  simp [Complex.mul_re, Complex.mul_im]

private theorem sum_norm_sq_rowC_eq_sum_norm_sq {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) :
    ∑ j, ‖rowC u a j‖ ^ 2 = ∑ j, ‖u a j‖ ^ 2 := by
  simp [rowC, norm_star]

theorem re_bound {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (Z Z' : Matrix (Fin n) (Fin n) ℂ)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : ∀ w : Fin n → ℂ, δ₁ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re)
    (h2 : ∀ w : Fin n → ℂ, δ₂ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z'ᴴ - Z')) *ᵥ w)).re)
    (u : Fin m → Fin n → ℂ) :
    (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace).re ≤
      -(c * min δ₁ δ₂ * ∑ a, ∑ j, ‖u a j‖ ^ 2) := by
  set S : Fin m → ℝ := fun a => ∑ j, ‖u a j‖ ^ 2 with hSdef
  have hS : ∀ a, 0 ≤ S a := fun a => by positivity
  have hT : ∀ a, c * min δ₁ δ₂ * S a ≤
      c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im := by
    intro a
    have e1 := h1 (rowC u a)
    rw [sum_norm_sq_rowC_eq_sum_norm_sq, ← im_eq_re] at e1
    have hm : min δ₁ δ₂ * S a ≤ δ₁ * S a := mul_le_mul_of_nonneg_right (min_le_left _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e1 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hF : ∀ a, c * min δ₁ δ₂ * S a ≤
      -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) := by
    intro a
    have e2 := h2 (rowC u a)
    have hflip : (star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z'ᴴ - Z')) *ᵥ rowC u a)
        = -(star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z' - Z'ᴴ)) *ᵥ rowC u a) := by
      rw [← neg_sub Z' Z'ᴴ, smul_neg, Matrix.neg_mulVec, dotProduct_neg]
    rw [hflip, Complex.neg_re, ← im_eq_re, sum_norm_sq_rowC_eq_sum_norm_sq] at e2
    have hm : min δ₁ δ₂ * S a ≤ δ₂ * S a := mul_le_mul_of_nonneg_right (min_le_right _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e2 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hsplit : ∑ a, S a = ∑ a with epsT t ε a = true, S a + ∑ a with epsT t ε a = false, S a := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => epsT t ε a = true) S]
    simp only [Bool.not_eq_true]
  rw [trace_gramB, trace_gramB, Finset.mul_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum,
    Complex.re_sum]
  simp only [re_I_mul_ofReal_mul_eq_neg_mul_im]
  have A : ∑ a with epsT t ε a = true, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = true, c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im :=
    Finset.sum_le_sum fun a _ => hT a
  have B : ∑ a with epsT t ε a = false, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = false, -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) :=
    Finset.sum_le_sum fun a _ => hF a
  rw [← Finset.mul_sum] at A B
  rw [Finset.sum_neg_distrib] at B ⊢
  rw [Finset.sum_neg_distrib]
  have hall : ∑ a, ∑ j, ‖u a j‖ ^ 2 = ∑ a, S a := rfl
  rw [hall, hsplit]
  nlinarith

end DBoundBH

open DBoundH DBoundAH DBoundBH in
theorem dBoundPQ : DBoundPQ := by
  intro m n ε t c e p q X hc _
  refine ⟨fun y u => famPQ_holo ε t c e p q X y u, famPQ_cont ε t c e p q X, ?_⟩
  intro y₀ z₀ hz₀
  have hopen : IsOpen (Set.univ ×ˢ stripS X : Set (GR n × ℂ)) := isOpen_univ.prod (isOpen_stripS X)
  have hmem : Set.univ ×ˢ stripS X ∈ 𝓝 ((y₀, z₀) : GR n × ℂ) := hopen.mem_nhds ⟨trivial, hz₀⟩
  have cZ : ∀ s : ℂ, (s = Complex.I ∨ s = -Complex.I) → ∀ i j,
      ContinuousAt (fun x : GR n × ℂ => ptZ x.1 X x.2 s i j) (y₀, z₀) :=
    fun s hs i j => (ptZ_entC X s hs i j).continuousAt hmem
  obtain ⟨δ₁, hδ₁, ev1⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • (ptZ x.1 X x.2 Complex.I - (ptZ x.1 X x.2 Complex.I)ᴴ))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inl rfl) i j).sub (cZ _ (Or.inl rfl) j i).star))
    (dSieg n y₀ X z₀ hz₀).1
  have hpd2 : ((-(Complex.I / 2)) • ((ptZ y₀ X z₀ (-Complex.I))ᴴ - ptZ y₀ X z₀ (-Complex.I))).PosDef := by
    have h := (dSieg n y₀ X z₀ hz₀).2.1
    unfold IsSiegel at h
    rwa [Matrix.conjTranspose_conjTranspose] at h
  obtain ⟨δ₂, hδ₂, ev2⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • ((ptZ x.1 X x.2 (-Complex.I))ᴴ - ptZ x.1 X x.2 (-Complex.I)))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inr rfl) j i).star.sub (cZ _ (Or.inr rfl) i j)))
    hpd2
  have evJ : ∀ᶠ x in 𝓝 ((y₀, z₀) : GR n × ℂ),
      ‖jC e p q x.1 X x.2‖ < ‖jC e p q y₀ X z₀‖ + 1 :=
    ((jC_contOn X e p q).continuousAt hmem).norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨N, hN, hNp⟩ := (ev1.and (ev2.and evJ)).exists_mem
  refine ⟨N, c * min δ₁ δ₂, ‖jC e p q y₀ X z₀‖ + 1, hN, by positivity, ?_⟩
  intro x hx _ u
  obtain ⟨b1, b2, bJ⟩ := hNp x hx
  have hr := re_bound ε t c hc (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) δ₁ δ₂ hδ₁ hδ₂ b1 b2 u
  show ‖jC e p q x.1 X x.2 * gC ε t c (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) u‖ ≤ _
  rw [norm_mul, gC, Complex.norm_exp]
  exact mul_le_mul bJ.le (Real.exp_le_exp.2 hr) (Real.exp_pos _).le (by positivity)

theorem dBound : DBound := by
  intro m n ε t c e X hc ht
  exact dBoundPQ m n ε t c e (cnt (epsT t ε) true) (cnt (epsT t ε) false) X hc ht

end PositivityTheory.Rg.Sw.Glob
end
end
