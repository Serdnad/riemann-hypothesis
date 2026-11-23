module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacA
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {m n : ℕ}

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem gramX_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX ε x j i = ∑ a, (sR ε a : ℂ) * (star (x a j) * x a i) := by

  simp only [gramX, Qp, Qb, evX, sR, map_sub, map_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
  have h1 : (b * gramX ε x).trace = ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h1]
  calc ∑ i, ∑ j, ∑ a, (sR ε a : ℂ) * (b i j * star (x a j) * x a i)
      = ∑ i, ∑ a, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (sR ε a : ℂ) * (b i j * star (x a j) * x a i) := Finset.sum_comm
    _ = ∑ a, (sR ε a : ℂ) * ∑ i, ∑ j, b i j * star (x a j) * x a i := by
        simp only [Finset.mul_sum]

theorem secN_one (ε : Fin m → Bool) (c t : ℝ) (hc : 0 < c) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b =
      ∏ a : Fin m, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det := by
  have hpt : ∀ x : Fin m → Fin n → ℂ,
      evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
        = ∏ a, rowF c (t * sR ε a) b (x a) := by
    intro x
    simp only [evX, map_one, one_mul, gs, rowF, trace_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    · congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · congr 1
      rw [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  unfold secN
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a v => rowF c (t * sR ε a) b v)]
  exact Finset.prod_congr rfl fun a _ => row_int c _ hc b hb

theorem detpm (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b = (c : ℂ) • (1 - (Complex.I * (s : ℂ)) • b) := by
  rw [smul_sub, smul_smul]; push_cast; congr 2; ring

theorem fac_eq (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((c * s : ℝ) : ℂ)) • b).det =
      ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) * ((1 - (Complex.I * (s : ℂ)) • b).det)⁻¹ := by
  rw [detpm, det_smul, Fintype.card_fin, div_mul_eq_div_div, div_eq_mul_inv]

theorem one_sub_neg (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((-1 : ℝ) : ℂ)) • b) = 1 + Complex.I • b := by
  push_cast; rw [mul_neg_one, neg_smul, sub_neg_eq_add]

theorem one_sub_pos (b : Matrix (Fin n) (Fin n) ℂ) : (1 - (Complex.I * ((1 : ℝ) : ℂ)) • b) = 1 - Complex.I • b := by
  push_cast; rw [mul_one]

private theorem prod_bool_fun_eq_pow_cnt_mul_pow_cnt (ε : Fin m → Bool) (F : Bool → ℂ) :
    ∏ a, F (ε a) = F true ^ cnt ε true * F false ^ cnt ε false := by
  have h : ∀ a, F (ε a) = if ε a = true then F true else F false := by
    intro a
    cases ε a <;> simp
  rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp [cnt]

theorem secN_eval (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (hc : 0 < c)
    (hsign : (t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true))
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    secN ε c t (1 : PX m n) b = ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) *
      (1 - Complex.I • b).det ^ (-(p : ℤ)) * (1 + Complex.I • b).det ^ (-(q : ℤ)) := by
  rw [secN_one ε c t hc b hb]
  rcases hsign with ⟨ht, hp, hq⟩ | ⟨ht, hp, hq⟩
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then 1 else -1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      rw [ht, fac_eq]
      rfl
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring
  · subst hp hq
    let F : Bool → ℂ := fun β => ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) *
      ((1 - (Complex.I * ((if β = true then -1 else 1 : ℝ) : ℂ)) • b).det)⁻¹
    have hf : ∀ a, (Real.pi : ℂ) ^ n / ((c : ℂ) • 1 - (Complex.I * ((t * sR ε a : ℝ) : ℂ)) • b).det
        = F (ε a) := by
      intro a
      have hs : t * sR ε a = c * (if ε a = true then -1 else 1) := by
        rw [ht]
        unfold sR
        split_ifs <;> ring
      rw [hs, fac_eq]
    rw [Finset.prod_congr rfl fun a _ => hf a, prod_bool_fun_eq_pow_cnt_mul_pow_cnt ε F]
    simp only [F, ↓reduceIte, Bool.false_eq_true, one_sub_pos, one_sub_neg]
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, _root_.mul_pow, _root_.mul_pow,
      _root_.inv_pow, _root_.inv_pow, pow_add]
    ring

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.EmbP

open Formalism.IndefR.Eqv (glueA splitInv psiT psiT_glueA finPart_glueA mat_ext psiT_sigR finPart_sigR psiT_inclR
  finPart_inclR continuous_glueA continuous_splitInv thetaC eq_thetaC)

variable (D : D7) {N : ℕ}

open Classical

def atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then g i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j)
    ((1 : Matrix (Fin N) (Fin N) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_atMN (τ τ' : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) :
    (atMN D τ g).map (psiT D τ') = if τ' = τ then g else 1 := by
  classical
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, psiT_glueA]
  split_ifs <;> rfl

theorem fin_atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : (atMN D τ g).map (finPart D) = 1 := by
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, finPart_glueA]

theorem atMN_mul (τ : D.what₂.Tau) (g g' : Matrix (Fin N) (Fin N) ℂ) :
    atMN D τ (g * g') = atMN D τ g * atMN D τ g' := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, psi_atMN, psi_atMN, psi_atMN]
    split_ifs <;> simp
  · rw [Matrix.map_mul, fin_atMN, fin_atMN, fin_atMN, Matrix.one_mul]

theorem atMN_one (τ : D.what₂.Tau) : atMN D τ (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  apply mat_ext D
  · intro τ'
    rw [psi_atMN, Matrix.map_one _ (map_zero _) (map_one _)]
    split_ifs <;> rfl
  · rw [fin_atMN, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_map_psiT (τ : D.what₂.Tau) (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (psiT D τ) = (M.map (psiT D τ))ᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, psiT_sigR]

theorem cT_map_fin (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (finPart D) =
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (M.map (finPart D)) := by
  ext i j; simp [Formalism.UG.cT, finPart_sigR]

theorem JR_map_psiT (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (psiT D τ) = J.map (tauE D τ) := by
  ext i j; simp [JR, psiT_inclR]

theorem JR_map_fin (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (finPart D) = JR (Af D.host.F) J := by
  ext i j; simp [JR, finPart_inclR]

theorem atMN_unitary (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : gᴴ * J.map (tauE D τ) * g = J.map (tauE D τ)) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (atMN D τ g) * JR (AF D.host.F) J * atMN D τ g = JR (AF D.host.F) J := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_atMN]
    split_ifs with h
    · subst h; exact hg
    · simp
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_atMN, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem continuous_atMN (τ : D.what₂.Tau) : Continuous (atMN D (N := N) τ) := by
  classical
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact (continuous_apply j).comp (continuous_apply i)
  · simp only [h, if_false]; exact continuous_const

end PositivityTheory.Rg.Sw.Glob.EmbP
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add (f := _), psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add (f := _), finPart_insT, finPart_insT, finPart_insT, add_zero]

theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]



def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl


theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
end
end
