module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

open PosProof

private theorem gip_monomial_self_eq_prod_jr {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (m : Sg ι A B →₀ ℕ) :
    gip (monomial m (1 : ℂ)) (monomial m (1 : ℂ)) = ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
  rw [← integral_mon_self m]
  unfold gip
  congr 1
  funext z
  rw [mon_prod]
  have h1 : (eval z) (monomial m (1 : ℂ)) = ∏ s : Sg ι A B, z s ^ m s := by
    rw [eval_monomial, one_mul, Finsupp.prod_fintype]
    intro i
    simp
  rw [h1, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hk_diag, star_pow, ← mul_pow]
  have h2 : z s * star (z s) = ((‖z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2]
  push_cast
  ring_nf

private theorem pos_lemma {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    sub 1 (Matrix.diagonal fun i => (d i : ℂ)) (monomial m (1 : ℂ)) =
      C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ) := by
  apply MvPolynomial.funext
  intro z
  rw [PosProof.eval_sub, Phi_diag, eval_mul, eval_C, eval_monomial, eval_monomial, one_mul, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  push_cast
  simp only [mul_pow, Finset.prod_mul_distrib]

private theorem lam_eq_prod_kap_pow {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    lam d m = ∏ s : Sg ι A B, kap d s ^ m s := by
  classical
  have hP : (0 : ℝ) < ∏ s : Sg ι A B, jr (m s) := Finset.prod_pos fun s _ => jr_pos _
  have h := gip_diag (A := A) (B := B) d (monomial m (1 : ℂ))
  rw [pos_lemma, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl,
    Complex.normSq_one, one_mul] at h
  have h3 : gip (C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ)) (monomial m (1 : ℂ)) =
      ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
    rw [← gip_monomial_self_eq_prod_jr]
    unfold gip
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [eval_mul, eval_C]
    ring
  rw [h3] at h
  have h4 : (∏ s : Sg ι A B, kap d s ^ m s) * (∏ s : Sg ι A B, jr (m s)) =
      lam d m * ∏ s : Sg ι A B, jr (m s) := by
    exact_mod_cast h
  exact (mul_right_cancel₀ hP.ne' h4).symm

private theorem gip_sub_eq_of_unitary_conj_diag {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (M U D : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (hMU : M * U = U * D)
    (f : PV ι A B) :
    gip (sub 1 M f) f = gip (sub 1 D (sub 1 U f)) (sub 1 U f) := by
  have hcont : Continuous fun z : Sg ι A B → ℂ =>
      (eval z) (sub 1 M f) * star ((eval z) f) * Complex.exp (-↑(∑ s : Sg ι A B, ‖z s‖ ^ 2)) :=
    ((continuous_eval _).mul (continuous_star.comp (continuous_eval _))).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun s _ => (continuous_norm.comp (continuous_apply s)).pow 2)).neg)
  unfold gip
  rw [integral_Phi U hU1 hU2 _ hcont]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [PosProof.eval_sub]
  rw [← Phi_mul, ← Phi_mul, hMU, norm_Phi U hU1]

theorem pos : Pos := by
  intro ι A B _ _ _ _ M hM f
  have hH := hM.isHermitian
  have hMe : M = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU1 : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa [Unitary.coe_star] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hMU : M * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have h := congrArg (· * (hH.eigenvectorUnitary : Matrix ι ι ℂ)) hMe
    rw [h, Matrix.mul_assoc (_ * _), hU1, Matrix.mul_one]
  have hkap : ∀ s : Sg ι A B, 0 ≤ kap hH.eigenvalues s := by
    intro s
    rcases s with s | s
    · simp [kap]
    · simp only [kap, Sum.elim_inr]
      exact hM.eigenvalues_nonneg _
  rw [gip_sub_eq_of_unitary_conj_diag M _ _ hU1 hU2 hMU f, gip_diag]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, trivial, ?_⟩
  · refine Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) ?_)
      (Finset.prod_nonneg fun s _ => (jr_pos _).le)
    rw [lam_eq_prod_kap_pow]
    exact Finset.prod_nonneg fun s _ => pow_nonneg (hkap s) _
  · intro hPD hf
    have hkap' : ∀ s : Sg ι A B, 0 < kap hH.eigenvalues s := by
      intro s
      rcases s with s | s
      · simp [kap]
      · simp only [kap, Sum.elim_inr]
        exact hPD.eigenvalues_pos _
    have hinv : sub 1 (star (hH.eigenvectorUnitary : Matrix ι ι ℂ))
        (sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f) = f := by
      apply MvPolynomial.funext
      intro z
      rw [PosProof.eval_sub, PosProof.eval_sub, ← Phi_mul, hU2, Phi_one]
    have hg : sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f ≠ 0 := by
      intro hg
      apply hf
      rw [← hinv, hg, map_zero]
    refine Finset.sum_pos (fun m hm => mul_pos (mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_)
      (Finset.prod_pos fun s _ => jr_pos _)) ?_
    · rw [lam_eq_prod_kap_pow]
      exact Finset.prod_pos fun s _ => pow_pos (hkap' s) _
    · exact Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section

noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder Matrix

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT

open AsmA

attribute [local irreducible] Tf

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]


variable (ι A B) in
def invSub : Submodule ℂ (PV ι A B) where
  carrier := {q | IsInv q}
  add_mem' := fun {a b} ha hb u hu => by rw [map_add (f := _), ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c q hq u hu => by rw [map_smul, hq u hu]


variable (ι A B) in
def Vd (d : ℕ) : Submodule ℂ (PV ι A B) := restrictTotalDegree ((ι × A) ⊕ (ι × B)) ℂ d ⊓ invSub ι A B

instance (d : ℕ) : FiniteDimensional ℂ (Vd ι A B d) := Submodule.finiteDimensional_of_le inf_le_left

theorem integrable_eval_act_blk_toMK (hA : Avg) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q)
      (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrable_eval_act hA _ _ continuous_blk (continuous_blk.matrix_map continuous_star) z q

theorem Tf_add (hA : Avg) (q1 q2 : PV ι A B) : Tf hA (q1 + q2) = Tf hA q1 + Tf hA q2 :=
  MvPolynomial.funext fun z => by
    rw [map_add (f := _), eval_Tf, eval_Tf, eval_Tf, ← integral_add (integrable_eval_act_blk_toMK hA z q1) (integrable_eval_act_blk_toMK hA z q2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_add (f := _)]

theorem Tf_smul (hA : Avg) (c : ℂ) (q : PV ι A B) : Tf hA (c • q) = c • Tf hA q :=
  MvPolynomial.funext fun z => by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_Tf, eval_Tf,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_mul, eval_C]

theorem Tf_memVd (hS : Stable) (hA : Avg) {d : ℕ} {q : PV ι A B} (hq : q ∈ Vd ι A B d) :
    Tf hA q ∈ Vd ι A B d := by
  rw [Vd, Submodule.mem_inf] at hq ⊢
  refine ⟨(mem_restrictTotalDegree _ _ _).mpr ((Tf_deg hA q).trans ((mem_restrictTotalDegree _ _ _).mp hq.1)), ?_⟩
  show IsInv (Tf hA q)
  exact pair_inv (Tf_mem hS hA q)

def Tlin (hS : Stable) (hA : Avg) (d : ℕ) : Vd ι A B d →ₗ[ℂ] Vd ι A B d where
  toFun q := ⟨Tf hA q, Tf_memVd hS hA q.2⟩
  map_add' q1 q2 := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact Tf_add hA (q1 : PV ι A B) (q2 : PV ι A B)
  map_smul' c q := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact Tf_smul hA c (q : PV ι A B)

def Mk (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : Matrix ι ι ℂ :=
  (blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).transpose * (blk (Formalism.REAL.toMK k)).map star

theorem continuous_Mk : Continuous (Mk (ι := ι) (A := A) (B := B)) :=
  continuous_blk.matrix_transpose.matrix_mul (continuous_blk.matrix_map continuous_star)

theorem Mk_psd (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : (Mk (ι := ι) (A := A) (B := B) k).PosSemidef := by
  have e : Mk (ι := ι) (A := A) (B := B) k =
      ((blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).map star)ᴴ * (blk (Formalism.REAL.toMK k)).map star := by
    ext i j
    simp [Mk, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem Mk_one : Mk (ι := ι) (A := A) (B := B) 1 = 1 := by
  have hb : blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK (1 : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true))) = 1 := by
    have h1 : Formalism.REAL.toM (1 : Formalism.REAL.UJ (fun _ : Fin (NN ι A B) => true)) = 1 := Units.val_one
    ext i j
    simp only [blk, Formalism.REAL.toMK, OneMemClass.coe_one, h1, Matrix.one_apply, emb_injective.eq_iff]
  simp [Mk, hb]

theorem eval_Tf_inv (hE : Ext) (hA : Avg) {q : PV ι A B} (hq : IsInv q) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k, eval (act 1 (Mk (ι := ι) (A := A) (B := B) k) z) q ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  rw [eval_Tf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact ext_all hE hq _ z

theorem Tlin_injective (hS : Stable) (hE : Ext) (hA : Avg) (hP : Pos) (d : ℕ) :
    Function.Injective (Tlin (ι := ι) (A := A) (B := B) hS hA d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq0
  by_contra hne
  have hq : (q : PV ι A B) ≠ 0 := fun h => hne (Subtype.ext h)
  have hqI : IsInv (q : PV ι A B) := (Submodule.mem_inf.mp q.2).2
  have hqd : (q : PV ι A B).totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).mp (Submodule.mem_inf.mp q.2).1
  set W := restrictTotalDegree ((ι × A) ⊕ (ι × B)) ℂ d
  obtain ⟨c, hc⟩ := exists_points W ((gipL hP (q : PV ι A B)).comp W.subtype)
  have hsubW : ∀ k, sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B) ∈ W := fun k =>
    (mem_restrictTotalDegree _ _ _).mpr ((totalDegree_sub_le _ _ _).trans hqd)
  have hΨ : ∀ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) =
      ∑ z ∈ c.support, c z * eval (act 1 (Mk (ι := ι) (A := A) (B := B) k) z) (q : PV ι A B) := by
    intro k
    have h := hc ⟨_, hsubW k⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.sum] at h
    change gip (sub 1 (Mk k) (q : PV ι A B)) (q : PV ι A B) = _ at h
    rw [h]
    simp only [AsmA.eval_sub]
  have hΨc : Continuous fun k => gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) := by
    simp_rw [hΨ]
    exact continuous_finsetSum _ fun z _ => continuous_const.mul (continuous_act_eval continuous_const continuous_Mk z _)
  have hint : Integrable (fun k => gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B))
      (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
    integrableOn_univ.mp (hΨc.continuousOn.integrableOn_compact isCompact_univ)
  have hTW : Tf hA (q : PV ι A B) ∈ W := (mem_restrictTotalDegree _ _ _).mpr ((Tf_deg hA _).trans hqd)
  have hT0 : Tf hA (q : PV ι A B) = 0 := congrArg Subtype.val hq0
  have hgipT : gip (Tf hA (q : PV ι A B)) (q : PV ι A B) =
      ∫ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    have h := hc ⟨_, hTW⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.sum] at h
    change gip (Tf hA (q : PV ι A B)) (q : PV ι A B) = _ at h
    rw [h]
    simp_rw [hΨ]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [eval_Tf_inv hE hA hqI z, integral_const_mul]
    · intro z _
      exact (integrable_eval_act hA (fun _ => 1) (Mk (ι := ι) (A := A) (B := B)) continuous_const continuous_Mk z _).const_mul _
  have hgip0 : gip (Tf hA (q : PV ι A B)) (q : PV ι A B) = 0 := by
    rw [hT0]; simp [gip]
  have hre : 0 < ∫ k, (gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)).re
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    refine (Complex.continuous_re.comp hΨc).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
      (fun k => (hP ι A B (Mk (ι := ι) (A := A) (B := B) k) (Mk_psd k) _).1) (x := 1) ?_
    have h1 := (hP ι A B (Mk (ι := ι) (A := A) (B := B) 1) (Mk_psd 1) (q : PV ι A B)).2.2 (by rw [Mk_one]; exact Matrix.PosDef.one) hq
    exact h1.ne'
  have hcomm : (∫ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true))).re =
      ∫ k, (gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)).re
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    have := Complex.reCLM.integral_comp_comm hint
    simpa using this.symm
  rw [← hgipT, hgip0] at hcomm
  simp at hcomm
  linarith

end PositivityTheory.Rg.Sw.FFTSteps.AsmT

namespace PositivityTheory.Rg.Sw.FFTSteps

open AsmT

theorem assembly : Assembly := by
  intro hS hE hA hP ι A B _ _ _ _ p hp
  have hpI : IsInv p := fun u hu => hp u hu
  have hsurj := LinearMap.injective_iff_surjective.mp (Tlin_injective (ι := ι) (A := A) (B := B) hS hE hA hP p.totalDegree)
  obtain ⟨q, hq⟩ := hsurj ⟨p, Submodule.mem_inf.mpr ⟨(mem_restrictTotalDegree _ _ _).mpr le_rfl, hpI⟩⟩
  have h : Tf hA (q : PV ι A B) = p := congrArg Subtype.val hq
  rw [← h]
  exact Tf_mem hS hA _

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem coeff_inv (v : Matrix (Rw ε true) (Rw ε true) ℂ) (Q : PX m n) (hQ : act (blk ε true v) Q = Q)
    (μ : VV (Rw ε false) n →₀ ℕ) : sub v (v.map star) ((Th ε Q).coeff μ) = (Th ε Q).coeff μ := by
  classical
  have h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support,
      emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1) := by
    conv_lhs => rw [decomp (ε := ε) Q]

    rw [map_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [map_mul]
    congr 1
    · exact DFunLike.congr_fun (act_emb_same true v) _
    · exact DFunLike.congr_fun (act_emb_other true false (by decide) v) _
  rw [hQ] at h1
  have h2 := congrArg (fun P => AddMonoidAlgebra.coeff (Th ε P) μ) h1

  simp only [map_sum, th_prod, coeff_sum_monomial] at h2
  by_cases hμ : μ ∈ (Th ε Q).support
  · rw [if_pos hμ] at h2
    exact h2.symm
  · have : AddMonoidAlgebra.coeff (Th ε Q) μ = 0 := notMem_support_iff.1 hμ
    rw [this, map_zero]

end PositivityTheory.Rg.Sw.FFTSteps.CycF

namespace PositivityTheory.Rg.Sw.FFTSteps

open CycF

theorem cycFFT : CycFFT := by
  classical
  intro hF m n ε Q hQ
  have hact : ∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      act (n := n) u Q = Q := hQ
  have hc : ∀ μ, (Th ε Q).coeff μ ∈ pairAlg (Rw ε true) (Fin n) (Fin n) := fun μ =>
    hF _ _ _ ((Th ε Q).coeff μ) (fun u hu => coeff_inv u Q (hact _ (blk_unitary true u hu) (blk_block true u)) μ)
  obtain ⟨bs, hbs, hspan, hli⟩ := exists_linearIndependent ℂ
    ((fun μ => (Th ε Q).coeff μ) '' ((Th ε Q).support : Set _))
  have hfin : bs.Finite := (((Th ε Q).support.finite_toSet).image _).subset hbs
  letI : Fintype bs := hfin.fintype
  have hmem : ∀ μ ∈ (Th ε Q).support, (Th ε Q).coeff μ ∈
      Submodule.span ℂ (Set.range (fun j : bs => (j : PV (Rw ε true) (Fin n) (Fin n)))) := by
    intro μ hμ
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hrep : ∀ μ : (Th ε Q).support, ∃ a : bs → ℂ,
      ∑ j, a j • (j : PV (Rw ε true) (Fin n) (Fin n)) = (Th ε Q).coeff μ.1 := fun μ =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem μ.1 μ.2)
  choose a ha using hrep
  let r : bs → PV (Rw ε false) (Fin n) (Fin n) := fun j => ∑ μ : (Th ε Q).support, a μ j • monomial μ.1 1
  have hQ' : Q = ∑ j : bs, emb ε true (j : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r j) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [← Finset.sum_coe_sort (Th ε Q).support]
    simp_rw [← ha]

    simp only [r, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  have hr : ∀ j, r j ∈ pairAlg (Rw ε false) (Fin n) (Fin n) := by
    intro j
    refine hF _ _ _ (r j) (fun u hu => ?_)
    have h1 := hact _ (blk_unitary false u hu) (blk_block false u)

    rw [hQ', map_sum] at h1
    have h2 : ∀ i : bs, act (blk ε false u) (emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r i)) =
        emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i)) := by
      intro i
      rw [map_mul]
      congr 1
      · exact DFunLike.congr_fun (act_emb_other false true (by decide) u) _
      · exact DFunLike.congr_fun (act_emb_same false u) _
    simp_rw [h2] at h1
    have h3 : ∑ i : bs, emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) *
        emb ε false (sub u (u.map star) (r i) - r i) = 0 := by
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
      rw [h1, sub_self]
    have := indep (fun i : bs => (i : PV (Rw ε true) (Fin n) (Fin n))) hli _ h3 j
    exact sub_eq_zero.1 this
  rw [hQ']
  refine Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ ?_ ?_)
  · obtain ⟨μ, hμ, hj⟩ := hbs j.2
    apply emb_pairAlg true
    rw [← hj]
    exact hc μ
  · exact emb_pairAlg false (hr j)

end PositivityTheory.Rg.Sw.FFTSteps
end
end
