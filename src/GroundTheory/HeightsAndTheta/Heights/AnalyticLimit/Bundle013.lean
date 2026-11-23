module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd isPshRsmul maMeasureMono maMeasure_thm mIntegrableCont
  mIntSymm mIntRsmul st_mInt_congr_phi)

theorem isPsh_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P Q : LocPot X} (hP : IsPsh A P) (hU : ∀ x, Q.U x ⊆ P.U x) (hφ : Q.φ = P.φ) : IsPsh A Q := by
  intro x j y hy w
  rw [hφ]
  exact hP x j y ⟨hy.1, hU x hy.2⟩ w

theorem mInt_update_rsmul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin e) (g : X → ℝ) :
    mInt A (Function.update Φ j ((Φ j).rsmul c)) g = c * mInt A Φ g := by
  obtain _ | n := e
  · exact j.elim0
  set q := Φ ∘ Equiv.swap 0 j with hq
  have h1 : Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j =
      Fin.cons ((q 0).rsmul c) (Fin.tail q) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hq]
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, Fin.tail, hq, Function.update_of_ne hne]
  calc mInt A (Function.update Φ j ((Φ j).rsmul c)) g
      = mInt A (Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j) g := (mIntSymm A _ _ g).symm
    _ = mInt A (Fin.cons ((q 0).rsmul c) (Fin.tail q)) g := by rw [h1]
    _ = c * mInt A (Fin.cons (q 0) (Fin.tail q)) g :=
        mIntRsmul A c _ _ (hΦ _) (fun i => hΦ _) g
    _ = c * mInt A Φ g := by rw [Fin.cons_self_tail, hq, mIntSymm]

theorem mInt_rsmul_all {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) :
    mInt A (fun i => (Φ i).rsmul c) g = c ^ e * mInt A Φ g := by
  have key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then (Φ i).rsmul c else Φ i) g =
      c ^ k * mInt A Φ g := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      set Ψ : Fin e → LocPot X := fun i => if (i : ℕ) < k then (Φ i).rsmul c else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := fun i => by
        simp only [hΨ]; split_ifs
        · exact isPotentialRsmul A c _ (hΦ i)
        · exact hΦ i
      have h : (fun i : Fin e => if (i : ℕ) < k + 1 then (Φ i).rsmul c else Φ i) =
          Function.update Ψ ⟨k, hk⟩ ((Ψ ⟨k, hk⟩).rsmul c) := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp [hΨ]
        · have hi' : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi, hΨ]
          simp only [Nat.lt_succ_iff_lt_or_eq, hi', or_false]
      rw [h, mInt_update_rsmul A c Ψ hΨp, ih (Nat.le_of_succ_le hk), pow_succ]
      ring
  simpa using key e le_rfl

theorem LemmaEScale.proof : LemmaEScale.Statement := by
  intro D X _ _ _ A Om M v hM hv hpsh
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hM0 : M ≠ 0 := by positivity
  have hP : ∀ i, IsPotential A (potForm Om.pot (v i)) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hv i))
  have hW : ∀ i, IsPotential A (potForm Om.pot fun x => v i x / M) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ fun j => (hv i j).div_const M)
  have hQ := isPotentialRsmul A (M - 1) _ Om.isPot
  have hQpsh := isPshRsmul A (M - 1) _ (by linarith) Om.isPot Om.isPsh
  refine ⟨fun i => ?_, fun g hg hg0 => ?_⟩
  · have h1 := isPshRsmul A M⁻¹ _ (by positivity) (hP i) (hpsh i)
    have h2 := isPshRsmul A (1 - M⁻¹) _ (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hM)
      Om.isPot Om.isPsh
    refine isPsh_of_φ_eq (isPshAdd A _ _ (isPotentialRsmul A _ _ (hP i))
      (isPotentialRsmul A _ _ Om.isPot) h1 h2) (fun x y hy => ⟨hy, hy.1⟩) ?_
    funext x y
    show Om.pot.φ x y + v i y / M = M⁻¹ * (Om.pot.φ x y + v i y) + (1 - M⁻¹) * Om.pot.φ x y
    field_simp
    ring
  have hmono := maMeasureMono A _ (fun _ => Om.pot.rsmul (M - 1)) hP hpsh (fun _ => hQ)
    (fun _ => hQpsh)
  have hS : ∀ i, IsPotential A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPotentialAdd A _ _ (hP i) hQ
  have hSpsh : ∀ i, IsPsh A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPshAdd A _ _ (hP i) hQ (hpsh i) hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A _ hP hpsh
  obtain ⟨_, hS'⟩ := maMeasure_thm A _ hS hSpsh
  have hgm := hg.measurable
  have e1 := (hT' g hgm).2 (mIntegrableCont A _ hP g hg)
  have e2 := (hS' g hgm).2 (mIntegrableCont A _ hS g hg)
  have hint := (hS' g hgm).1.1 (mIntegrableCont A _ hS g hg)
  have hle : mInt A (fun i => potForm Om.pot (v i)) g ≤
      mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g := by
    rw [e1, e2]
    exact integral_mono_measure hmono (Filter.Eventually.of_forall hg0) hint
  have e3 : mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g =
      mInt A (fun i => (potForm Om.pot fun x => v i x / M).rsmul M) g := by
    refine st_mInt_congr_phi A (fun i => ?_) g
    funext x y
    show Om.pot.φ x y + v i y + (M - 1) * Om.pot.φ x y = M * (Om.pot.φ x y + v i y / M)
    field_simp
    ring
  rw [e3, mInt_rsmul_all A M _ hW] at hle
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem lemmaEEnergy_step {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (u : Fin (n + 1) → X → ℝ) (w : X → ℝ)
    (hu : ∀ i, A.Smooth (u i)) (hpsh : ∀ i, IsPsh A (potForm Om.pot (u i))) (j : Fin (n + 1))
    (hj : ∀ x, -1 ≤ u j x ∧ u j x ≤ 0) (hw : A.Smooth w) (hwp : IsPsh A (potForm Om.pot w)) :
    mInt A (fun i => potForm Om.pot (u i)) (fun x => -w x) ≤
      mInt A (fun i => potForm Om.pot (Function.update u j 0 i)) (fun x => -w x) + Om.vol := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσdef
  have hσ : ∀ i : Fin n, σ i.succ ≠ j := by
    intro i h
    have h' : σ (σ i.succ) = σ j := congrArg σ h
    rw [Equiv.swap_apply_self, hσdef, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'
  let d : EnergyStep.Data A Om :=
    { w := w, v := u j, f := fun i => u (σ i.succ), M := 1, w_smooth := hw, w_psh := hwp,
      v_smooth := hu j, v_nonpos := fun x => (hj x).2, le_v := fun x => (hj x).1,
      f_smooth := fun _ => hu _, f_psh := fun _ => hpsh _ }
  have h := EnergyStep.proof A Om d
  rw [← mIntSymm A _ σ, ← mIntSymm A (fun i => potForm Om.pot (Function.update u j 0 i)) σ]
  have e1 : mInt A ((fun i => potForm Om.pot (u i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [σ, d, potForm]
    · simp [d, EnergyStep.Data.T, potForm]
  have e2 : mInt A ((fun i => potForm Om.pot (Function.update u j 0 i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons Om.pot d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      simp [σ, potForm, locPot_add_φ, LocPot.ofFun]
    · simp [d, EnergyStep.Data.T, potForm, Function.update_of_ne (hσ i)]
  rw [e1, e2]
  simpa [d] using h

theorem LemmaEEnergy.proof : LemmaEEnergy.Statement := by
  intro D X _ _ _ A Om v w hv hpsh hb hw hwp
  cases D with
  | zero =>
    have e : (fun i : Fin 0 => potForm Om.pot (v i)) = fun _ => Om.pot := funext fun i => i.elim0
    simp [e]
  | succ n =>
    let u : ℕ → Fin (n + 1) → X → ℝ := fun k i => if (i : ℕ) < k then v i else 0
    have hu : ∀ k i, A.Smooth (u k i) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hv i, st_smooth_const A 0]
    have hup : ∀ k i, IsPsh A (potForm Om.pot (u k i)) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hpsh i, isPsh_add_const Om.isPsh 0]
    have key : ∀ k ≤ n + 1, mInt A (fun i => potForm Om.pot (u k i)) (fun x => -w x) ≤
        mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) + k * Om.vol := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hupd : Function.update (u (k + 1)) ⟨k, hk⟩ 0 = u k := by
          funext i
          by_cases h : i = ⟨k, hk⟩
          · subst h; simp [u]
          · rw [Function.update_of_ne h]
            have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
            by_cases hlt : (i : ℕ) < k
            · simp [u, hlt, Nat.lt_succ_of_lt hlt]
            · have : ¬ (i : ℕ) < k + 1 := by omega
              simp [u, hlt, this]
        have step := lemmaEEnergy_step A Om (u (k + 1)) w (hu _) (hup _) ⟨k, hk⟩
          (fun x => by simpa [u] using hb ⟨k, hk⟩ x) hw hwp
        rw [hupd] at step
        have := ih (by omega)
        push_cast
        linarith
    have h1 := key (n + 1) le_rfl
    have e1 : (fun i => potForm Om.pot (u (n + 1) i)) = fun i => potForm Om.pot (v i) :=
      funext fun i => by simp [u, i.isLt]
    have e0 : mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) =
        mInt A (fun _ => Om.pot) (fun x => -w x) := by
      apply st_mInt_congr_phi
      intro i
      funext x y
      simp [u, potForm, locPot_add_φ, LocPot.ofFun]
    rw [e1, e0] at h1
    simpa using h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_add_smul levi_zero continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh isPotential_ofFun)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

theorem two_le_top_gms : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W}

def formDiff (Om th : LocPot W) : LocPot W := Om + th.rsmul (-1)

theorem isPotential_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th) :
    IsPotential A (formDiff Om th) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ hO (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ _ hth)

theorem isPsh_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th)
    (hle : LeviLe A Set.univ 1 th 1 Om) : IsPsh A (formDiff Om th) := by
  intro x j y hy w
  have h1 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A Om hO x j
    ⟨hy.1, hy.2.1⟩).of_le two_le_top_gms
  have h2 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A th hth x j
    ⟨hy.1, hy.2.2⟩).of_le two_le_top_gms
  have hl := levi_add_smul (-1) h1 h2 w
  have hle' := hle x j y ⟨hy.1, ⟨Set.mem_univ _, hy.2.2⟩, hy.2.1⟩ w
  have heq : (formDiff Om th).φ x ∘ (A.chart j).symm =
      fun z => (Om.φ x ∘ (A.chart j).symm) z + (-1) * (th.φ x ∘ (A.chart j).symm) z := rfl
  rw [heq, hl]
  linarith

theorem add_formDiff_φ (Om th : LocPot W) (x y : W) : (th + formDiff Om th).φ x y = Om.φ x y := by
  show th.φ x y + (Om.φ x y + -1 * th.φ x y) = Om.φ x y
  ring

theorem isPsh_of_formNonneg_dense {P : LocPot W} {Yo : Set W} (hP : IsPotential A P)
    (hd : Dense Yo) (hn : FormNonneg A Yo P) : IsPsh A P := by
  intro x j y hy w
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  obtain ⟨F, hF⟩ : ∃ F, F = P.φ x ∘ (A.chart j).symm := ⟨_, rfl⟩
  have hFs : ContDiffOn ℝ 2 F ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
    rw [hF]
    exact (hP.1 x j).of_le two_le_top_gms
  rw [← hF]
  have hpair : ContinuousAt (fun p : (Fin e → ℂ) × (Fin e → ℂ) => levi F p.1 p.2) (y, w) :=
    (continuousOn_levi hOo hFs).continuousAt (prod_mem_nhds (hOo.mem_nhds hy) Filter.univ_mem)
  have hc : ContinuousAt (fun z => levi F z w) y :=
    hpair.comp (f := fun z => (z, w)) (continuousAt_id.prodMk continuousAt_const)
  by_contra hneg
  rw [not_le] at hneg
  have hN : {z | levi F z w < 0} ∩
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) ∈ 𝓝 y :=
    Filter.inter_mem (hc.preimage_mem_nhds (Iio_mem_nhds hneg)) (hOo.mem_nhds hy)
  obtain ⟨V, hVN, hVo, hyV⟩ := mem_nhds_iff.1 hN
  have hVt : V ⊆ (A.chart j).target := fun z hz => (hVN hz).2.1
  have himg : IsOpen ((A.chart j).symm '' V) := by
    have := (A.chart j).symm.isOpen_image_source_inter hVo
    rwa [OpenPartialHomeomorph.symm_source, Set.inter_eq_right.2 hVt] at this
  obtain ⟨p, ⟨z, hzV, rfl⟩, hpY⟩ := hd.inter_open_nonempty _ himg ⟨_, y, hyV, rfl⟩
  have h0 := hn x j z ⟨(hVN hzV).2.1, hpY, (hVN hzV).2.2⟩ w
  rw [← hF] at h0
  exact absurd (hVN hzV).1 (not_lt.2 h0)

theorem forall_cons_of {n : ℕ} {p : LocPot W → Prop} {P : LocPot W} {Φ : Fin n → LocPot W}
    (h0 : p P) (h : ∀ i, p (Φ i)) : ∀ i, p ((Fin.cons P Φ : Fin (n + 1) → LocPot W) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0
  · simpa using h j

namespace UIData

variable {D : ℕ} (S : UIData D W)

theorem T_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPotential S.A (S.T t b) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form b t ht hℓ).1.th_pot
    (isPotential_ofFun S.A _ (S.form b t ht hℓ).2)

theorem dense_Yo : Dense S.Yo := by
  have h := interior_eq_empty_iff_dense_compl.1 S.bd_interior
  rwa [compl_compl] at h

theorem T_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPsh S.A (S.T t b) :=
  isPsh_of_formNonneg_dense (S.T_isPotential ht hℓ b) S.dense_Yo (S.form b t ht hℓ).1.nonneg

theorem rest_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPotential S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPotential ht hℓ _
  · exact S.Om.isPot

theorem rest_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPsh S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPsh ht hℓ _
  · exact S.Om.isPsh

end UIData

theorem mixedForms_cycle {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (a : ℕ)
    (ha : a < D + 1) (b : ℕ) (hb : b = a ∨ b = a + 1) :
    mixedForms Om T b ∘ (Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1))).symm =
      Fin.cons (mixedForms Om T b ⟨a, ha⟩) (restForms Om T a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.cycleRange_symm_zero]
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.cycleRange_symm_succ]
    by_cases hj : (j : ℕ) < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hj)]
      simp only [mixedForms, restForms, Fin.val_castSucc, hj, if_true]
      rw [if_pos (by omega)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
      simp only [mixedForms, restForms, Fin.val_succ, hj, if_false]
      rw [if_neg (by omega)]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
