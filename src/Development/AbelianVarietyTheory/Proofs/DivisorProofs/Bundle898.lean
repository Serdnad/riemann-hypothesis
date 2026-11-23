module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

namespace NablaStr

theorem coeff_der_diag_row {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (Formalism.CohomologicalDescent.LR.der r n a a f) m = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * AddMonoidAlgebra.coeff f m := by
  rw [← Formalism.CohomologicalDescent.LR.rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

theorem der_diag_eq_weight_smul_of_isWeightedHomogeneous {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ → ∀ a, Formalism.CohomologicalDescent.LR.der r n a a f = (μ a : ℚ) • f := by
  intro h a
  ext m
  rw [coeff_der_diag_row, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : AddMonoidAlgebra.coeff f m = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [h hm]

theorem eV_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  unfold eV
  rw [dif_pos ⟨ha, hb⟩]
  rfl

theorem eV_pow_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (k : ℕ) (x : dualWeyl ℚ N N ν) :
    (((eV N ν a b ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      ((Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) ^ k)
        (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, eV_val ν a b ha hb, pow_succ, Module.End.mul_apply]
    rfl

theorem weight_rowW_eq {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem glRel_eV (N : ℕ) (ν : Fin N → ℕ) : GlRel N (eV N ν) := by
  intro a b c d ha hb hc hd
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := Formalism.CohomologicalDescent.LR.der_comm (n := N) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (x : MvPolynomial (Fin N × Fin N) ℚ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [eV_val ν a b ha hb, eV_val ν c d hc hd, eV_val ν c d hc hd, eV_val ν a b ha hb, h]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp only [if_true, LinearMap.sub_apply, Submodule.coe_sub, eV_val ν d d ha hd, eV_val ν b b hc hb]
  · subst hbc
    have : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp only [if_true, this, if_false, hda, sub_zero, eV_val ν a d ha hd]
    simp
  · subst hda
    have : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    simp only [if_true, this, if_false, hbc, zero_sub, LinearMap.neg_apply, Submodule.coe_neg, eV_val ν c b hc hb]
    simp
  · have h1 : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    have h2 : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp [h1, h2, hbc, hda]

theorem wtSpan_eV (N : ℕ) (ν : Fin N → ℕ) : WtSpan N (eV N ν) := by
  classical
  rw [WtSpan, eq_top_iff]
  rintro x -
  set f : MvPolynomial (Fin N × Fin N) ℚ := (x : MvPolynomial (Fin N × Fin N) ℚ) with hf
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum : f = ∑ μ ∈ hfin.toFinset, weightedHomogeneousComponent (rowW N N) μ f := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (rowW N N) f]
    exact finsum_eq_sum_of_support_subset _ (fun μ hμ => (Set.Finite.mem_toFinset hfin).mpr hμ)
  have hmem : ∀ μ, weightedHomogeneousComponent (rowW N N) μ f ∈ dualWeyl ℚ N N ν :=
    fun μ => dualWeylRowGraded ℚ N N ν μ f x.2
  have hx : x = ∑ μ ∈ hfin.toFinset, (⟨_, hmem μ⟩ : dualWeyl ℚ N N ν) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hsum
  rw [hx]
  refine Submodule.sum_mem _ fun μ _ => Submodule.subset_span ?_
  refine ⟨fun c => if h : c < N then (μ ⟨c, h⟩ : ℤ) else 0, fun c hc => ?_⟩
  apply Subtype.ext
  rw [eV_val ν c c hc hc]
  simp only [dif_pos hc]
  have h := der_diag_eq_weight_smul_of_isWeightedHomogeneous _ μ
    (weightedHomogeneousComponent_isWeightedHomogeneous μ f) ⟨c, hc⟩
  rw [Submodule.coe_smul]
  simpa using h

theorem sum_range_dite (N k : ℕ) (hk : k ≤ N) (F : Fin N → ℕ) :
    ∑ c ∈ Finset.range k, (if h : c < N then (F ⟨c, h⟩ : ℤ) else 0) =
      ((∑ a : Fin N with a.val < k, F a : ℕ) : ℤ) := by
  push_cast
  rw [Finset.sum_filter]
  have e : ∀ a : Fin N, (if a.val < k then (F a : ℤ) else 0) =
      (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) a.val := by
    intro a
    simp [a.isLt]
  rw [Finset.sum_congr rfl (fun a _ => e a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) N,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem dom_eV (N : ℕ) (ν : Fin N → ℕ) : Dom N (eV N ν) (wtZ ν) := by
  classical
  intro μ x hx hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hx0'
  have hμ : ∀ c (hc : c < N), μ c = (rowDeg m ⟨c, hc⟩ : ℤ) := by
    intro c hc
    have h1 := congrArg (fun y : dualWeyl ℚ N N ν => AddMonoidAlgebra.coeff (y : MvPolynomial (Fin N × Fin N) ℚ) m) (hx c hc)
    simp only [eV_val ν c c hc hc, coeff_der_diag_row, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul,
      weight_rowW_eq] at h1
    have h2 := mul_right_cancel₀ hm h1
    exact_mod_cast h2.symm
  have hdom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν (x : MvPolynomial (Fin N × Fin N) ℚ) x.2 m
    (mem_support_iff.mpr hm)
  have hsμ : ∀ k ≤ N, ∑ c ∈ Finset.range k, μ c = ((∑ a : Fin N with a.val < k, rowDeg m a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcN : c < N := lt_of_lt_of_le (Finset.mem_range.mp hc) hk
    rw [dif_pos hcN, hμ c hcN]
  have hsν : ∀ k ≤ N, ∑ c ∈ Finset.range k, wtZ ν c = ((∑ a : Fin N with a.val < k, ν a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    exact Finset.sum_congr rfl fun c _ => rfl
  have hall : ∀ F : Fin N → ℕ, (∑ a : Fin N with a.val < N, F a) = ∑ a : Fin N, F a := by
    intro F
    rw [Finset.filter_true_of_mem (fun a _ => a.isLt)]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hsμ k hk, hsν k hk]
    exact_mod_cast hdom.1 k
  · rw [hsμ N le_rfl, hsν N le_rfl, hall, hall]
    exact_mod_cast hdom.2

theorem divStable_eV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ))
    (hM : ∀ (a b : Fin N) (k : ℕ), ∀ f ∈ M, rowDiv ℤ a b k f ∈ M) : DivStable N (eV N ν) (latV N ν M) := by
  intro i hi j hj hij k x hx
  simp only [latV, Submodule.mem_comap, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : map (Int.castRingHom ℚ) y = (x : MvPolynomial (Fin N × Fin N) ℚ) := hyx
  refine ⟨rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y, hM _ _ k y hy, ?_⟩
  have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
  change map (Int.castRingHom ℚ) (rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y) =
    (((k.factorial : ℚ)⁻¹ • (eV N ν i j ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ)
  rw [Submodule.coe_smul, eV_pow_val ν i j hi hj, ← Formalism.CohomologicalDescent.LR.der_pow _ _ hne, ← lclosedeq_rowDiv_map, hyx']

end NablaStr

open NablaStr

theorem nablaGl : NablaGl := by
  intro N ν _
  refine ⟨glRel_eV N ν, wtSpan_eV N ν, dom_eV N ν, divStable_eV N ν _ ?_, divStable_eV N ν _ ?_⟩
  · intro a b k f hf
    exact rowDivStable ℤ N N ν a b k f hf
  · intro a b k f hf
    exact weylRowDivStable ℤ N N le_rfl ν a b k f hf

end GlobalTheory.LeviCut
end
end

section

open Classical MvPolynomial

noncomputable section

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem eval_rsub_frameMat {a d : ℕ} (x₀ : Var ι d a → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (rsub (frameMat x₀) P) = eval x₀ (colSub g P) := by
  have h : (eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2)).comp
        (rsub (frameMat x₀) : Pol ι d a →ₐ[ℂ] _).toRingHom
      = (eval x₀).comp (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      obtain ⟨τ, r, j⟩ := v

      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rsub_X, colSub, aeval_X,
      map_sum, map_mul, eval_C, eval_X]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single j]
        · simp [frameMat, mul_comm]
        · intro b _ hb; simp [frameMat, hb]
        · simp
      · intro b _ hb; simp [frameMat, hb]
      · simp
  exact congrArg (fun φ : Pol ι d a →+* ℂ => φ P) h

theorem rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply GlobalTheory.T.unitaryGroup_family_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring

theorem inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  intro ι _ a d n P hP
  set c := Formalism.L2.DIV.fockS (detG (ι := ι) a n) (detG a n) with hc
  have hc0 : c ≠ 0 := fun h => by
    have := fockS_self_re_pos (detG_ne_zero (ι := ι) a n)
    rw [← hc, h] at this
    simp at this
  have key : c • P = ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    apply MvPolynomial.funext
    intro x₀
    have h1 := GlobalTheory.T.fockPairing_linearSubstitution_adjoint (frameMat x₀).conjTranspose (detG a n) P
    rw [Matrix.conjTranspose_conjTranspose, rsub_frameMat_of_mem_inv x₀ hP, GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum] at h1

    rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, map_sum, map_smul, LinearMap.sum_apply] at h1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, smul_eq_mul,
      starRingEnd_apply, star_star] at h1

    rw [smul_eval, map_sum]
    simp only [smul_eval]
    rw [mul_comm, ← h1]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hP' : P = c⁻¹ • ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    rw [← key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hP']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

end GlobalTheory.MinorFrame
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
open scoped BigOperators

namespace GlobalTheory.BaseVacuum.ProductTheta

variable (L : PeriodPair) {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

theorem stdH_prod (x y : ι × m → ℂ) :
    stdH L (ι × m) x y = ∑ k, stdH L m (fun v => x (k, v)) (fun v => y (k, v)) := by
  rw [(stdHBasic L (ι × m)).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(stdHBasic L m).1]

theorem alphaQ_prod (c : ℝ) (y : ι × m → ℂ) :
    alphaQ c (stdH L (ι × m)) y = ∏ k, alphaQ c (stdH L m) (fun v => y (k, v)) := by
  unfold alphaQ qOf
  rw [← Complex.exp_sum]
  congr 1
  rw [stdH_prod, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem altE_prod (x y : ι × m → ℂ) :
    altE (stdH L (ι × m)) x y = ∑ k, altE (stdH L m) (fun v => x (k, v)) (fun v => y (k, v)) := by
  unfold altE
  rw [stdH_prod, Complex.im_sum]

theorem mem_stdLat_prod (x : ι × m → ℂ) :
    x ∈ stdLat L (ι × m) ↔ ∀ k, (fun v => x (k, v)) ∈ stdLat L m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Prod.forall]

theorem heisenbergOperator_gaussianVacuum_prod_blocks (ω₀ : ℂ) (x z : ι × m → ℂ) :
    opU (stdH L (ι × m)) x (F0 L ω₀ (ι × m)) z
      = ∏ k, opU (stdH L m) (fun v => x (k, v)) (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold F0
  rw [opUStd L (ι × m), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [opUStd L m]

theorem gaussianVacuum_prod_blocks (ω₀ : ℂ) (z : ι × m → ℂ) : F0 L ω₀ (ι × m) z = ∏ k, F0 L ω₀ m (fun v => z (k, v)) := by
  unfold F0 prodFn
  rw [Fintype.prod_prod_type]

theorem semiChar_prod (c : ℝ) (Λ : AddSubgroup (m → ℂ)) (h : IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m))) :
    IsSemiChar (stdH L (ι × m)) (blkLat (ι := ι) Λ) (alphaQ c (stdH L (ι × m))) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [alphaQ_prod]
    exact Finset.prod_induction _ (fun a : ℂ => a = 1 ∨ a = -1)
      (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
      (Or.inl rfl) (fun k _ => h.1 _ (hx k))
  · rw [alphaQ_prod, alphaQ_prod, alphaQ_prod, altE_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact h.2 _ (hx k) _ (hy k)

theorem fixed_prod (ω₀ : ℂ) (c' : ℝ)
    (hF : F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c' (stdH L m)) (stdLat L m)) :
    F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c' (stdH L (ι × m))) (stdLat L (ι × m)) := by
  change ∀ x ∈ stdLat L (ι × m), ∀ z, _ = _
  intro x hx z
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib, gaussianVacuum_prod_blocks]
  have hx' := (mem_stdLat_prod L x).1 hx
  exact Finset.prod_congr rfl fun k _ => hF _ (hx' k) _

def prodReps (S : Finset (m → ℂ)) : Finset (ι × m → ℂ) :=
  (Fintype.piFinset fun _ : ι => S).map (Equiv.curry ι m ℂ).symm.toEmbedding

theorem card_prodReps (S : Finset (m → ℂ)) : (prodReps (ι := ι) S).card = S.card ^ Fintype.card ι := by
  rw [prodReps, Finset.card_map, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

theorem prodReps_isReps {Λ : AddSubgroup (m → ℂ)} {S : Finset (m → ℂ)} (hS : IsReps (stdLat L m) Λ S) :
    IsReps (stdLat L (ι × m)) (blkLat (ι := ι) Λ) (prodReps S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf
    intro k
    exact hS.1 _ (hf k)
  · intro x hx y hy hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf hg
    have hd' := (mem_stdLat_prod L _).1 hd
    have : f = g := funext fun k => hS.2.1 _ (hf k) _ (hg k) (hd' k)
    rw [this]
  · intro y hy
    have : ∀ k, ∃ x ∈ S, (fun v => y (k, v)) - x ∈ stdLat L m := fun k => hS.2.2 _ (hy k)
    choose f hf hfy using this
    refine ⟨(Equiv.curry ι m ℂ).symm f, Finset.mem_map_of_mem _ (Fintype.mem_piFinset.2 hf), ?_⟩
    rw [mem_stdLat_prod]
    intro k
    exact hfy k

theorem relIdx_eq_card {V : Type} [AddCommGroup V] [Module ℂ V] {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V}
    (hS : IsReps Λ₁ Λ₂ S) : relIdx Λ₁ Λ₂ = S.card := by
  have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  rw [h1]
  rfl

theorem sumU_prod (c : ℝ) (ω₀ : ℂ) (S : Finset (m → ℂ)) (z : ι × m → ℂ) :
    sumU (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (prodReps S) (F0 L ω₀ (ι × m)) z
      = ∏ k, sumU (stdH L m) (alphaQ c (stdH L m)) S (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold sumU prodReps
  rw [Finset.sum_map, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib]
  rfl

theorem sqrt_pow' (r : ℝ) (hr : 0 ≤ r) (n : ℕ) : Real.sqrt (r ^ n) = Real.sqrt r ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg r) n), pow_right_comm, Real.sq_sqrt hr]

end GlobalTheory.BaseVacuum.ProductTheta

namespace GlobalTheory.BaseVacuum


open ProductTheta in
theorem prod_blk_inter : ∀ (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)), IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m)) → F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) → relIdx (stdLat L m) Λ ≠ 0 → IsSemiChar (stdH L (ι × m)) (blkLat Λ) (alphaQ c (stdH L (ι × m))) ∧ F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) ∧ relIdx (stdLat L (ι × m)) (blkLat Λ) ≠ 0 ∧ ∀ w, inter (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) (blkLat Λ) (F0 L ω₀ (ι × m)) w = ∏ k, inter (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) Λ (F0 L ω₀ m) (fun v => w (k, v)) := by
  intro L ω₀ c ι m _ _ _ _ Λ hα hF hn
  have hα' := semiChar_prod L (ι := ι) c Λ hα
  have hF' := fixed_prod L (ι := ι) ω₀ c hF
  obtain ⟨⟨S, hS⟩, hcard⟩ := repsExist _ (stdLat L m) Λ hn
  have hS' := prodReps_isReps L (ι := ι) hS
  have hr : relIdx (stdLat L (ι × m)) (blkLat (ι := ι) Λ) = relIdx (stdLat L m) Λ ^ Fintype.card ι := by
    rw [relIdx_eq_card hS', card_prodReps, hcard S hS]
  refine ⟨hα', hF', by rw [hr]; exact pow_ne_zero _ hn, fun w => ?_⟩
  rw [interReps _ _ (stdHBasic L _).2.1 _ _ _ hα' _ hF' _ hS' w, sumU_prod]
  rw [Finset.prod_congr rfl fun k _ => interReps _ _ (stdHBasic L m).2.1 _ _ _ hα _ hF _ hS (fun v => w (k, v))]
  rw [hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.cast_pow,
    sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]

end GlobalTheory.BaseVacuum
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.analyticOnNhd_om_expt_and_iteratedDeriv_zero_eq : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  first | exact @GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | exact GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | (intros; apply GlobalTheory.FockAlg.analyticOnNhd_orbit_pol <;> assumption)
end
