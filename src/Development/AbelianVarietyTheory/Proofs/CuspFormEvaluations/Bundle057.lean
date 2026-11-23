module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.Shares.WtDic

variable {D : D7}

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun x => by simp [conjEmb]

theorem tauEmb_ne_conj (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_tau {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj, this]
  · simp

theorem wtA_conj {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [(tauEmb_ne_conj _ _).symm]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h => ht' (tauEmb_inj (by
      have := congrArg conjEmb h
      rwa [conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm
    simp [(tauEmb_ne_conj _ _).symm, this]
  · simp

theorem matrixExtendByZero_mul {p : ℕ} (c : ℕ) (f : Fin p → ℕ) (i : ℕ) : ext0 (fun k => c * f k) i = c * ext0 f i := by
  unfold ext0; split_ifs <;> rfl

theorem wtA_wsmul {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (wsmul c w) x = c * wtA w x := by
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2 := matrixExtendByZero_mul _ _ _
  have h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2 := matrixExtendByZero_mul _ _ _
  rw [h1, h2]
  split_ifs <;> ring

theorem wtA_wscalar (j n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp only [wtA]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  rw [h1, h2]
  simp

theorem laR_wadd (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (u u' : WeightFamilies.Wt D j) :
    laR T j (wadd u u') k = laR T j u k + laR T j u' k := by
  funext τ a
  have hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2 := by
    have h1 := u.n_even
    have h2 := u'.n_even
    rw [n_wadd]
    rw [Nat.even_iff] at h1 h2
    omega
  simp only [laR, laU, Pi.add_apply, wtA_wadd, hn]
  split_ifs <;> push_cast <;> ring

theorem laR_wsmul (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (m : ℕ) (u : WeightFamilies.Wt D j) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  funext τ a
  have hn : (wsmul m u).n / 2 = m * (u.n / 2) := by
    obtain ⟨s, hs⟩ := u.n_even
    show m * u.n / 2 = _
    rw [hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  simp only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem card_lower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem choose_split (p q : ℕ) : (p + q) * (p + q - 1) / 2 = p * q + p * (p - 1) / 2 + q * (q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem weights_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  intro D T h j hj k
  obtain ⟨hr, hk, -⟩ := h.unf j hj T.σ₀ T.good_σ₀
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  have hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f := by
    have h1 := GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D] at h1
    omega
  refine ⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩
  · rw [addL, laR_wadd, laR_wsmul]
  · funext τ a
    have hn : (etWt D j i).n / 2 = i * (g0 D / 2) := by
      show g0 D * i / 2 = _
      unfold g0
      rw [mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]
    have hw : ∀ x, wtA (etWt D j i) x = 0 := wtA_wscalar _ _ _
    simp only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]
    split_ifs <;> simp
  · rw [nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]
  · rw [← hc, Fintype.card_coe]
  · let f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ := fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩
      obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)
      exact ⟨t, Subtype.ext ht.symm⟩
    have hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ := fun τ =>
      Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ
    refine ⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩
    obtain ⟨t, rfl⟩ := (Equiv.ofBijective f hf).surjective τ
    rw [Equiv.symm_apply_apply]
    have e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t := rfl
    simp only [laR, laU, hinv, e, wtA_tau, wtA_conj]

end GlobalTheory.Shares.WtDic
end
end

section

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThFr

section Deriv

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ}

theorem differentiable_polyDeriv (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) :
    Differentiable ℂ fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F y := by
  simp only [polyDeriv_eq_of_subset P u F _ subset_rfl, pdTerm_eq_itD]
  exact Differentiable.fun_sum fun m _ => (itD_differentiable hF _).const_mul _

theorem polyDeriv_mul_X (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) (l : σ)
    (x : W) : _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (P * X l) u F x = fderiv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F y) x (u l) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have h (m : σ →₀ ℕ) : (monomial m c : MvPolynomial σ ℂ) = c • monomial m 1 := by
      simp [smul_monomial]
    rw [X, monomial_mul, mul_one, h, h]
    simp only [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD]
    rw [fderiv_const_mul (itD_differentiable hF _ x), ContinuousLinearMap.smul_apply, smul_eq_mul,
      ← itD_cons hF, ← List.map_cons]
    refine congrArg _ (congrFun (ct_itD_perm hF (List.Perm.map u ?_)) x)
    rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
  | add P Q hP hQ =>
    simp only [add_mul, polyDeriv_add, hP, hQ]
    rw [fderiv_fun_add (differentiable_polyDeriv hF P u x) (differentiable_polyDeriv hF Q u x),
      ContinuousLinearMap.add_apply]

theorem polyDeriv_algHom (hF : ContDiff ℂ (⊤ : ℕ∞) F) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (s : σ → ℂ) (j : σ → σ) (hΦ : ∀ l, Φ (X l) = X l + C (s l) * X (j l)) (u : σ → W)
    (P : MvPolynomial σ ℂ) (x : W) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (Φ P) u F x = _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => u l + s l • u (j l)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (C a : MvPolynomial σ ℂ) = a • monomial 0 1 := by simp [smul_eq_C_mul]
    rw [algHom_C, algebraMap_eq, h]
    simp [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD, -smul_monomial, -monomial_zero']
  | add P Q hP hQ => simp only [map_add (f := _), polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, hΦ, mul_add, mul_left_comm, C_mul', polyDeriv_add, polyDeriv_smul,
      polyDeriv_mul_X hF, polyDeriv_mul_X hF, polyDeriv_mul_X hF, funext hP]
    simp

end Deriv

section Triangular

variable {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module ℂ V]

theorem eigen_of_triangular (f : (J → V) → ℂ) (lt : J → J → Prop) (rk : J → ℕ)
    (hrk : ∀ i j, lt i j → rk i < rk j) (d : J → ℕ)
    (hadd : ∀ i j, lt i j → ∀ (s : ℂ) u, f (Function.update u j (u j + s • u i)) = f u)
    (hsc : ∀ j (s : ℂ) u, f (Function.update u j (s • u j)) = s ^ d j * f u)
    (N : J → J → ℂ) (hN : ∀ i j, i ≠ j → ¬ lt i j → N i j = 0) (u : J → V) :
    f (fun j => ∑ i, N i j • u i) = (∏ j, N j j ^ d j) * f u := by
  have hne : ∀ i j, lt i j → i ≠ j := fun i j h e => (hrk i j h).ne (congrArg rk e)
  have one (y : J → V) (j : J) (T : Finset J) (hT : j ∉ T) :
      f (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)) = N j j ^ d j * f y := by
    induction T using Finset.induction_on with
    | empty => simpa using hsc j _ y
    | insert i T hi ih =>
      have hij : i ≠ j := fun e => hT (e ▸ Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hi, ← ih fun h => hT (Finset.mem_insert_of_mem h)]
      by_cases h : lt i j
      · rw [← hadd i j h (N i j) (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)),
          Function.update_idem,
          Function.update_self, Function.update_of_ne hij]
        congr 2
        abel
      · rw [hN i j hij h, zero_smul, zero_add]
  have key (S : Finset J) : f (fun j => if j ∈ S then ∑ i, N i j • u i else u j) =
      (∏ j ∈ S, N j j ^ d j) * f u := by
    induction S using Finset.induction_on_min_value rk with
    | empty => simp
    | insert a S ha hmin ih =>
      rw [Finset.prod_insert ha, mul_assoc, ← ih, ← one _ a (Finset.univ.erase a) (by simp)]
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj
        rw [Function.update_self, if_pos (Finset.mem_insert_self _ _), if_neg ha,
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        by_cases h : lt i j
        · rw [if_neg fun hS => (hmin i hS).not_gt (hrk i j h)]
        · rw [hN i j (Finset.ne_of_mem_erase hi) h, zero_smul, zero_smul]
      · simp [Function.update_of_ne hj, hj]
  simpa using key Finset.univ

end Triangular


open Harm in
theorem polyDeriv_triangular {T κ W : Type*} [Fintype T] [Fintype κ] {p q : ℕ}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F)
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {P : Poly ℂ T p q κ} (hP : P ∈ rowHighest ℂ c c')
    (N : T × (Fin p ⊕ Fin q) → T × (Fin p ⊕ Fin q) → ℂ)
    (hN : ∀ i j, i ≠ j → ¬ (i.1 = j.1 ∧ RowLT i.2 j.2) → N i j = 0) (u : Var T p q κ → W) (x : W) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => ∑ i, N i (l.1, l.2.1) • u (i.1, i.2, l.2.2)) F x =
      (∏ j, N j j ^ Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) * _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x := by
  classical
  obtain ⟨-, hdeg, hinv⟩ := mem_rowHighest_iff_rowAdd.1 hP
  have h := eigen_of_triangular
    (fun w : T × (Fin p ⊕ Fin q) → κ → W => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => w (l.1, l.2.1) l.2.2) F x)
    (fun i j => i.1 = j.1 ∧ RowLT i.2 j.2) (fun i => Sum.elim Fin.val Fin.val i.2) ?_
    (fun j => Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) ?_ ?_ N hN
    fun i k => u (i.1, i.2, k)
  · simpa only [Finset.sum_apply, Pi.smul_apply] using h
  · rintro ⟨t, a | a⟩ ⟨t', b | b⟩ ⟨-, h⟩ <;> first | exact h | exact h.elim
  · rintro ⟨t, r⟩ ⟨t', r'⟩ ⟨rfl, h⟩ s w
    conv_rhs => rw [← rowAdd_eq_self_of_forall_int (hinv t r r' h) s]
    rw [polyDeriv_algHom hF _ (fun l => if l.1 = t ∧ l.2.1 = r' then s else 0)
      (fun l => (t, r, l.2.2)) (fun ⟨t', r'', k⟩ => by rw [rowAdd_X]; split_ifs <;> simp)]
    congr 1
    funext ⟨t', r'', k⟩
    by_cases e : t' = t ∧ r'' = r'
    · obtain ⟨rfl, rfl⟩ := e
      simp
    · rw [Function.update_of_ne (by simpa using e), if_neg e]
      simp
  · rintro ⟨t, r⟩ s w
    rw [← polyDeriv_smul_letter P (fun l => if l.1 = t ∧ l.2.1 = r then s else 1) _ fun m hm => ?_]
    · congr 1
      funext ⟨t', r'', k⟩
      by_cases e : t' = t ∧ r'' = r
      · obtain ⟨rfl, rfl⟩ := e
        simp
      · rw [Function.update_of_ne (by simpa using e), if_neg e]
        simp
    · rw [← hdeg t r (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.sum,
        ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [rowInd_apply]
      split_ifs with h <;> simp [h]

end GlobalTheory.ThFr
end
