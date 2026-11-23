module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

def cI (p : Fin (2 * r + k + 1)) : Fin (mdim k r 0) := ⟨p.val, by have := p.isLt; simp [mdim]; omega⟩

theorem posL_cI (p : Fin (2 * r + k + 1)) : posL k r 0 (cI p) = p := Fin.ext (by simp [posL, cI])

theorem cI_inj : Function.Injective (cI (k := k) (r := r)) := fun p q h => Fin.ext (by
  have := congrArg Fin.val h; simpa [cI] using this)


variable (E) in
abbrev SA (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r 0) × Fin (mdim k r 0) => Eh (E := E) (i := 0) hD p.1 p.2)

def EA (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SA E hD :=
  ⟨Eh hD (cI p) (cI q), Algebra.subset_adjoin ⟨(cI p, cI q), rfl⟩⟩

theorem EA_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : (EA (E := E) hD p q : Module.End ℂ (VS k r 0 D E)) =
    Eh hD (cI p) (cI q) := rfl

theorem EA_gl (hD : IsOpen D) : GlRel (EA (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := Eh_gl (E := E) (i := 0) hD (cI a) (cI b) (cI c) (cI d)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EA_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos (congrArg cI hbc), if_pos hbc]; rfl
    · rw [if_neg (fun e => hbc (cI_inj e)), if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos (congrArg cI hda), if_pos hda]; rfl
    · rw [if_neg (fun e => hda (cI_inj e)), if_neg hda]; rfl

def La (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) : SA E hD →ₗ[ℂ] E where
  toFun x := ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g
  map_add' x y := by simp
  map_smul' c x := by simp

theorem La_apply (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) (x : SA E hD) :
    La hD v g x = ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g := rfl

theorem leftEq_SA (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : SA E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) → LeftEq k r z 0 D (x v : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    intro v hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩
    rw [ev_E hD p.1 p.2 v hng, ev_E hD p.1 p.2 v hg]
    exact ((generator_action_preserved E k r z 0 D p.1 p.2 (v : Mx k r → E) (v : Mx k r → E) 1 hD v.2.1 v.2.1).2.1 hN hv) g hg n hn
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y₁ y₂ _ _ h₁ h₂ =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h₁ v hv g hg n hn, h₂ v hv g hg n hn, smul_add]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro v hv
    exact h₁ _ (h₂ v hv)

abbrev Tor (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, j ≤ l.val ∧ x = EA hD (eI k r l) (eI k r l)}

theorem comm_Tor (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, j ≤ l.val → p ≠ eI k r l) (hq : ∀ l : Fin r, j ≤ l.val → q ≠ eI k r l) (P : SA E hD)
    (hP : P ∈ Tor hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (eI k r l) (eI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem Tor_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : Tor (E := E) hD j' ≤ Tor hD j :=
  Algebra.adjoin_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem EA_mem_Tor (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : j ≤ l.val) :
    EA (E := E) hD (eI k r l) (eI k r l) ∈ Tor hD j :=
  Algebra.subset_adjoin ⟨l, h, rfl⟩

end alg

section qm

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor E a b u) = qminor (fun p q => φ (E p q)) a b u := by
  unfold qminor

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  congr 1
  funext k
  simp only [Function.comp_apply, Tm, map_add]
  split_ifs <;> simp

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (E : Fin n' → Fin n' → A) (ι : Fin n → Fin n')
    (hι : Function.Injective ι) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun p q => E (ι p) (ι q)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  congr 1
  funext l
  simp only [Tm, Function.comp_apply]
  by_cases h : a (σ l) = b l
  · rw [if_pos h, if_pos (congrArg ι h)]
  · rw [if_neg h, if_neg (fun e => h (hι e))]

end qm

section main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem gauge_last (c : Fin r → ℂ) :
    (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) =
      ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) :=
  Finset.prod_congr rfl fun a _ => if_pos a.isLt

theorem resG_last (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    Q.resG k r (Fin.last r) J c g = ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • J (wCell k r (Fin.last r) c * g) := by
  unfold Q.resG
  rw [gauge_last]

theorem root_vector_action_cutoff (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleE) {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : a.val < b.val) :
    ((EA hD (eI k r a) (eI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (eI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (eI k r b) (cut k r 0 D f) g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

end main

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section
variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem inverse_mul_regular_element {y : ℂ} (hy : RegY P y) : xInvM P y * xA P (DQ P) y = 1 := by
  unfold xInvM xA
  rw [← map_mul]
  have : ((fun π => (M.xC P π y)⁻¹) * fun π => M.xC P π y) = (1 : M.Ty P → ℂ) := by
    funext π; simp only [Pi.mul_apply, Pi.one_apply]; exact inv_mul_cancel₀ (hy π)
  rw [this, map_one]

theorem jdr_kap_DG (g : M.Ty P → ℂ) {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P) :
    kap P (DQ P) g * z = z * kap P (DQ P) g := Formalism.FourierDecayAlt.P.MAx3.H.kap_comm_DG P g hz

theorem jdr_SC_DG {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P) : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P := by
  obtain ⟨w, rfl⟩ := hz
  exact Formalism.FourierDecayAlt.P.MAx3.H.sc_memDG P w

end

theorem residue_splitting_holds : ResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, hDri, -⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hl0 : L.l0 y = l0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hgi, hn, -, -⟩ := hL
    simp only [LevelData.l0, l0A, hn, hzb, hgi]
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Drb = L.Drb * X := jdr_kap_DG _ (jdr_SC_DG hDrb)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDriDr : L.Dri * L.Dr = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDri L) (Formalism.FourierDecayAlt.P.MAx3.H.memDr L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Dr_Dri' L

  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * SSn P L l * kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y =
        X * L.Drb * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
    intro l _
    have c1 : SS P (DQ P) l * L.Dr = L.Dr * SS P (DQ P) l := Formalism.FourierDecayAlt.P.MAx3.H.SS_comm_SC P l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    unfold SSn LevelData.Ahat
    calc X * (L.Drb * L.Dri * SS P (DQ P) l) * kap P (DQ P) (fun π => M.xEx P {l} π y) * (L.Dr * L.Ar y)
        = X * L.Drb * L.Dri * (SS P (DQ P) l * (kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr)) * L.Ar y := by
          simp only [mul_assoc]
      _ = X * L.Drb * (L.Dri * L.Dr) * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
          rw [c2, ← mul_assoc (SS P (DQ P) l), c1]; simp only [mul_assoc]
      _ = _ := by rw [hDriDr, mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS21 : (∑ l ∈ Finset.Icc 1 (P.k - 1), SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) =
      weightedSumBis P (DQ P) y := rfl
  rw [hS21]

  have hR : X * RhM P L y = L.R0 y + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
    unfold RhM LevelData.R0 t21 t22
    rw [hl0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * l0A P (DQ P) y) = ggA P (DQ P) * l0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Drb * ((ggA P (DQ P) * x * l0A P (DQ P) y + weightedSumBis P (DQ P) y) * L.Ar y + ggA P (DQ P) * x * L.Br y))
        = L.Drb * ((X * (ggA P (DQ P) * x * l0A P (DQ P) y) + X * weightedSumBis P (DQ P) y) * L.Ar y +
            X * (ggA P (DQ P) * x) * L.Br y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Drb * ggA P (DQ P) * (l0A P (DQ P) y * L.Ar y + L.Br y) + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

theorem mirror_residue_splitting_holds : MirrorResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, -, hDrbi⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hm0 : L.m0 y = m0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hgi, -, hns, -⟩ := hL
    simp only [LevelData.m0, m0A, hns, hz, hgi]
  have sDrb : star L.Drb = L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.cb) = L.c := funext fun l => by
      obtain ⟨-, -, hc, -, hcb, -⟩ := hL
      show star (L.cb l) = L.c l
      rw [hcb, hc]
      simp only [cbA, cA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_c L l)
  have sDri : star L.Dri = L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.ci) = L.cbi := funext fun l => by
      obtain ⟨-, -, -, hci, -, hcbi, -⟩ := hL
      show star (L.ci l) = L.cbi l
      rw [hci, hcbi]
      simp only [ciA, cbiA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_cbi L l)
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Dr = L.Dr * X := jdr_kap_DG _ (jdr_SC_DG hDr)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDrbiDrb : L.Drbi * L.Drb = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDrbi L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Drb_Drbi' L
  have cDD : L.Dr * L.Drb = L.Drb * L.Dr :=
    Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDr L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)
  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y =
        X * L.Dr * (kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) * L.Avr y := by
    intro l _
    have c1 : star (SS P (DQ P) l) * L.Dr = L.Dr * star (SS P (DQ P) l) := Formalism.FourierDecayAlt.P.MAx3.H.SSs_comm_SC l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    have hs : star (SSn P L l) = star (SS P (DQ P) l) * L.Drbi * L.Dr := by
      unfold SSn; rw [star_mul, star_mul, sDri, sDrb, mul_assoc]
    rw [hs]
    unfold LevelData.Ahatv
    calc X * kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Drbi * L.Dr) * (L.Drb * L.Avr y)
        = X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l) * (L.Drbi * (L.Dr * L.Drb)) *
            L.Avr y := by simp only [mul_assoc]
      _ = X * (kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Dr)) * L.Avr y := by
          rw [cDD, ← mul_assoc L.Drbi, hDrbiDrb, one_mul]; simp only [mul_assoc]
      _ = _ := by rw [c1, ← mul_assoc (kap P (DQ P) _), c2]; simp only [mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS12 : (∑ l ∈ Finset.Icc 1 (P.k - 1), kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) =
      S12 P (DQ P) y := rfl
  rw [hS12]
  have hR : X * RhvM P L y = L.R0v y + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
    unfold RhvM LevelData.R0v t12 t22
    rw [hm0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * m0A P (DQ P) y) = ggA P (DQ P) * m0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Dr * ((ggA P (DQ P) * x * m0A P (DQ P) y + S12 P (DQ P) y) * L.Avr y + ggA P (DQ P) * x * L.Bvr y))
        = L.Dr * ((X * (ggA P (DQ P) * x * m0A P (DQ P) y) + X * S12 P (DQ P) y) * L.Avr y +
            X * (ggA P (DQ P) * x) * L.Bvr y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Dr * ggA P (DQ P) * (m0A P (DQ P) y * L.Avr y + L.Bvr y) + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

end

end Formalism.FourierDecayAlt.P.CutMP
end
