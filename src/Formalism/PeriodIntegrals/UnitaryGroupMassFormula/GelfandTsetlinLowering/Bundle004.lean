module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliShift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoExistsOfCap
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoPolDiagHw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.EvalInitMinorNormLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params

@[expose] public section

section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem io_fixed_up {n : ℕ} (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hU : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) f = f)
    (a b : Fin n) (hab : a < b) : pol ℂ a.castSucc b.castSucc f = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc b.castSucc f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, PI.WHw.eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det ≠ 0 := by
      rw [det_one_add_single, if_neg hne]; exact one_ne_zero
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (m : ℂ) := rfl
    have hup : ∀ i j, j < i → g i j = 0 := by
      intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      show (1 + Matrix.single a b (m : ℂ)) i j = 0
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg hij, zero_add]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hab hji) (lt_irrefl _)
    have hdiag : ∀ i, g i i = 1 := by
      intro i
      show (1 + Matrix.single a b (m : ℂ)) i i = 1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_true]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩; exact hne h.symm
    have h1 := hU g hup hdiag
    have hT := embGL_transvec g a b (m : ℂ) hgv
    have hdet1 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = 1 := by
      unfold detPow
      have hd : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hT, det_one_add_single,
          if_neg (fun h => hne (Fin.castSucc_injective _ h).symm)]
        rfl)
      rw [hd, one_zpow, Units.val_one]
    unfold sqAct at h1
    rw [hdet1, one_smul, hT] at h1
    exact h1
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at this
  rw [pol_eq_rowDiv]
  exact this

theorem io_torus_diag {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hT : ∀ t : Fin n → ℂˣ, sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) f =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • f)
    (a : Fin n) (hd : lam.detShift ≤ sg.w a) :
    pol ℂ a.castSucc a.castSucc f = ((sg.w a - lam.detShift : ℤ) : ℂ) • f := by
  set d : ℕ := (sg.w a - lam.detShift).toNat with hd'
  have hdz : ((d : ℕ) : ℤ) = sg.w a - lam.detShift := Int.toNat_of_nonneg (by omega)
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc a.castSucc f - Polynomial.C f * (1 + Polynomial.X) ^ d).eval
      (C (m : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    have hm0 : (m : ℂ) + 1 ≠ 0 := by norm_cast
    let t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 ((m : ℂ) + 1) hm0 else 1
    have h1 := hT t
    have hgv : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a a (m : ℂ) := by
      ext i j
      simp only [diagGL, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, t]
      by_cases hij : i = j <;> by_cases hia : i = a <;> simp_all [add_comm] <;> intro h <;> exact absurd h.symm hia
    have hTr := embGL_transvec (diagGL ℂ n t) a a (m : ℂ) hgv
    have hdet : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) lam.detShift =
        ((m : ℂ) + 1) ^ lam.detShift := by
      unfold detPow
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hTr,
        det_one_add_single, if_pos rfl]
    have hprod : ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) = ((m : ℂ) + 1) ^ sg.w a := by
      rw [Finset.prod_eq_single a (fun j _ hj => by simp [t, hj]) (by simp), Units.val_zpow_eq_zpow_val]
      simp [t]
    unfold sqAct at h1
    rw [hdet, hTr, hprod] at h1
    have hz : ((m : ℂ) + 1) ^ sg.w a = ((m : ℂ) + 1) ^ lam.detShift * ((m : ℂ) + 1) ^ d := by
      rw [← zpow_natCast, hdz, ← zpow_add₀ hm0]
      congr 1
      ring
    rw [hz, ← smul_smul] at h1
    have h2 := smul_right_injective _ (zpow_ne_zero _ hm0) h1
    rw [Submodule.mem_bot, Polynomial.eval_sub, PI.WHw.eval_rowGen, sub_eq_zero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    rw [show (1 + C (m : ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ^ d = C (((m : ℂ) + 1) ^ d) by
      rw [map_pow, map_add (f := _), map_one, add_comm (C (m : ℂ)) 1], mul_comm, ← smul_eq_C_mul]
    exact h2
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, sub_eq_zero] at this
  rw [pol_eq_rowDiv]
  unfold rowDiv
  rw [this, ← hdz, Int.cast_natCast, smul_eq_C_mul, mul_comm, map_natCast]

theorem capXi (hx : XiFacts) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) (u : ℂ) :
    Formalism.REAL.qdet (capE h lam) u (xi ℂ h lam sg) = capP sg u • xi ℂ h lam sg := by
  subst h
  obtain ⟨-, -, hU, hT, -, -⟩ := hx n (n + 1) rfl lam sg hI
  have hHW : Formalism.REAL.IsHW (capE rfl lam) (fun k => ((sg.w k : ℤ) : ℂ)) (xi ℂ rfl lam sg) := by
    refine ⟨fun a' => ?_, fun a' b' hab => ?_⟩
    · have hd : lam.detShift ≤ sg.w a' := by
        have ha := a'.isLt
        have h1 := (hI a').2
        have h2 : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨a'.1 + 1, by omega⟩ := lam.anti (by
          rw [Fin.le_iff_val_le_val]
          show a'.1 + 1 ≤ n
          omega)
        have h3 : lam.detShift = lam.w ⟨n, by omega⟩ := by
          unfold DomWeight.detShift
          rw [dite_eq_left (by omega)] <;> congr 1
        linarith
      have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) a')
          (xi ℂ rfl lam sg) = ((sg.w a' - lam.detShift : ℤ) : ℂ) • xi ℂ rfl lam sg :=
        io_torus_diag lam sg (xi ℂ rfl lam sg) hT a' hd
      rw [capE_apply, if_pos rfl, e, ← add_smul]
      congr 1
      push_cast
      ring
    · have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) b')
          (xi ℂ rfl lam sg) = 0 :=
        io_fixed_up lam (xi ℂ rfl lam sg) hU a' b' hab
      rw [capE_apply, if_neg (ne_of_lt hab), e, add_zero]
  rw [Formalism.REAL.quantumDetHighestWeight_holds _ n (capE rfl lam) _ _ (capE_glRel rfl lam) hHW u]
  rfl

theorem capFacts_of (h3 : PI.HwIrred) (hx : XiFacts) : CapFacts := by
  intro n N h lam sg hI
  refine ⟨fun u => Formalism.REAL.qdet (capE h lam) u, ?_, ?_⟩
  · intro mu _ φ hφ s hs u
    exact capScalar h3 h lam mu φ hφ s hs u
  · intro u
    exact capXi hx h lam sg hI u

theorem ioExists_of' (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of_cap h3 h4 hx (capFacts_of h3 hx)

end PI.WGL
end
end

section

noncomputable section

namespace PI.WGL.LTC

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM

theorem eRow_inj {n N : ℕ} (h : n + 1 = N) : Function.Injective (eRow h) := by
  intro a b hab
  have h1 := congrArg Fin.val hab
  simp only [eRow] at h1
  exact Fin.ext (by simpa using h1)

theorem eRow_ne_last {n N : ℕ} (h : n + 1 = N) (b : Fin n) : eRow h b ≠ ⟨N - 1, by omega⟩ := by
  intro hb
  have h1 := congrArg Fin.val hb
  have h2 := b.2
  simp [eRow] at h1
  omega

theorem exp_bidet {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K) :
    Exp (id : Fin n → Fin n) (fun ρ : Fin (sz k) → Fin n => initMinor ℤ (n := n) ρ (hsz k)) := exp_gmin id Function.injective_id (Fin.castLE (hsz k))

theorem exp_M {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) :
    Exp (eRow h) (fun ρ : Fin (sz k) → Fin n =>
      if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega)) := by
  intro a b ρ
  by_cases hk : k ∈ L
  · simp only [hk, if_true, ite_true]
    exact exp_lift (eRow h) (eRow_inj h) ⟨N - 1, by omega⟩ (eRow_ne_last h)
      (Fin.castLE (by have := hsz k; omega)) a b ρ
  · simp only [hk, if_false, ite_false]
    exact exp_gmin (eRow h) (eRow_inj h) (Fin.castLE (by have := hsz k; omega)) a b ρ

theorem rowGen_gmin_inv {r c m : ℕ} (a b : Fin r) (hab : a ≠ b) (ρ : Fin m → Fin r) (κ : Fin m → Fin c)
    (hρ : (∃ pa, ρ pa = a) ∨ ∀ p, ρ p ≠ b) :
    rowGen ℤ a b (gmin ρ κ) = Polynomial.C (gmin ρ κ) := by
  classical
  rw [rowGen_gmin, Finset.sum_eq_single ∅]
  · have hu : upd ρ ∅ a = ρ := by
      funext p
      simp [upd]
    simp [hu]
  · intro S _ hS
    split_ifs with hc
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rcases hρ with ⟨pa, hpa⟩ | hρ
      · have hne : pa ≠ p0 := by
          intro h
          apply hab
          rw [← hpa, h]
          exact hc p0 hp0
        have hpaS : pa ∉ S := fun h => hab (hpa.symm.trans (hc pa h))
        have hz : gmin (upd ρ S a) κ = 0 := by
          unfold gmin
          apply Matrix.det_zero_of_row_eq hne
          funext q
          simp [upd, hpaS, hp0, hpa]
        simp [hz]
      · exact absurd (hc p0 hp0) (hρ p0)
    · rfl
  · simp

theorem polarization_of_constant {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (a b : Fin n) (hab : a ≠ b) :
    rowGen ℤ (eRow h a) (eRow h b) (C0 h lam sg) = Polynomial.C (C0 h lam sg) := by
  have hab' : eRow h a ≠ eRow h b := fun h' => hab (eRow_inj h h')
  have hlp : ∀ i : Fin n, i.1 + 1 = n → ∀ (hr : i.1 + 1 ≤ N) (hc : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (lpMinor ℤ (i.1 + 1) hr hc) = Polynomial.C (lpMinor ℤ (i.1 + 1) hr hc) := by
    intro i hi hr hc
    have ha := a.2
    exact rowGen_gmin_inv _ _ hab' (Fin.castLE hr) (Fin.castLE hc)
      (Or.inl ⟨⟨a.1, by omega⟩, Fin.ext (by simp [eRow])⟩)
  have hrz : ∀ i : Fin n, i.1 = 0 → ∀ (hs : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (initMinor ℤ (rowsZ h i) hs) = Polynomial.C (initMinor ℤ (rowsZ h i) hs) := by
    intro i hi hs
    refine rowGen_gmin_inv _ _ hab' (rowsZ h i) (Fin.castLE hs) (Or.inr fun p hp => ?_)
    have hp0 : p.1 = i.1 := by have := p.2; omega
    apply eRow_ne_last h b
    rw [← hp]
    simp [rowsZ, hp0]
  unfold C0
  simp only [map_prod, map_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  · split_ifs with hi
    · rw [map_pow, map_pow, hlp i hi]
    · simp
  · split_ifs with hi
    · rw [map_pow, map_pow, hrz i hi]
    · simp

theorem word_clause {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) :
    ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
      applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
      applyWord ℤ (liftWord h w) (Mlift h lam sg sz hsz L I) =
        d.sum (fun J c => c • Mlift h lam sg sz hsz L J) := by
  classical
  refine ⟨twd sz w (Finsupp.single I 1), ?_, ?_⟩
  · have hmap : w.map (fun x => (id x.1, id x.2.1, x.2.2)) = w := by
      induction w with
      | nil => rfl
      | cons x w ih => simp
    have h1 := applyWord_comb id sz (fun k ρ => initMinor ℤ (n := n) ρ (hsz k)) (exp_bidet sz hsz) 1
      (fun a b _ => by simp) w hw (Finsupp.single I 1)
    rw [hmap, Finsupp.linearCombination_single, one_smul] at h1
    simp only [one_mul, Finsupp.linearCombination_apply] at h1
    unfold bideterminant
    exact h1
  · have h2 := applyWord_comb (eRow h) sz
      (fun k ρ => if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (exp_M h sz hsz L) (C0 h lam sg) (fun a b hab => polarization_of_constant h lam sg a b hab) w hw (Finsupp.single I 1)
    rw [Finsupp.linearCombination_single, one_smul] at h2
    simp only [Finsupp.linearCombination_apply] at h2
    unfold Mlift
    exact h2

end PI.WGL.LTC
end
end

section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem xi_coefficient_facts : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx

end PI.WGL
end
end
