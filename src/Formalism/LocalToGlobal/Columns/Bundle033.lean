module

public import Formalism.LocalToGlobal.Columns.ChainTopLawB
public import Formalism.LocalToGlobal.Columns.ChainLawPhiA
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
public import Formalism.LocalToGlobal.Columns.ChainTwOk
import Formalism.LocalToGlobal.Columns.ChainOneOk
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Formalism.LocalToGlobal.Columns.Bundle014

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section ClPfT

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clPfUV_one {k : Type} [CommRing k] (χ : kˣ →* Kˣ) : clPfUV χ (1 : k) = 1 := by
  classical
  unfold clPfUV
  rw [dite_eq_left isUnit_one]
  have : (isUnit_one : IsUnit (1 : k)).unit = 1 := Units.ext rfl
  rw [this, map_one, Units.val_one]

private theorem fIdx_lt' {k₀ c n s : ℕ} (hk : k₀ ≤ n) (hs : s < n + c) : LocE.fIdx k₀ c n s < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

private theorem fIdx_injective {k₀ c n s s' : ℕ} (hk : k₀ ≤ n) (hs : s < n + c) (hs' : s' < n + c)
    (h : LocE.fIdx k₀ c n s = LocE.fIdx k₀ c n s') : s = s' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

private theorem clPfRed_one_eq_ite {k₀ n c : ℕ} (hk : k₀ ≤ n) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    clPfRed P q k₀ c n c n (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p' = if p = p' then 1 else 0 := by
  unfold clPfRed LocE.entB
  have hf := fIdx_lt' (k₀ := k₀) (c := c) hk hp
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_one, id]
  unfold Loc.atN Loc.eN
  rw [dite_eq_left hf]
  by_cases h : p = p'
  · subst h
    simp [redP_one]
  · have h2 : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h3 => h (fIdx_injective hk hp hp' h3)
    simp [h, h2, redP_zero]

theorem clPfT_lamGBS_one (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ r t J n c : ℕ} (hk : k₀ ≤ n) (hkr : k₀ < r) (hJ : r + J * t ≤ n + c) :
    LocE.lamGBS q ψ₀ χ k₀ r t J n c (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap = 1 := by
  have h1 : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) :=
    Subgroup.one_mem _
  rw [clPf_lamGBS hq0 ψ₀ χ hk hkr hJ h1]
  rw [clPf_lam_congr ψ₀ χ (A := n + c) (Y := fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0)
    hkr.le hJ (fun p p' hp hp' => clPfRed_one_eq_ite hk hp hp')]
  have hb : ∀ i, diagonalBlockMatrix r t i (fun p p' : ℕ => if p = p' then (1 : 𝓞 E ⧸ P.asIdeal) else 0) = 1 := by
    intro i
    ext s s'
    simp [diagonalBlockMatrix, Matrix.one_apply, Fin.ext_iff]
  unfold clPfLam
  simp only [hb, Matrix.det_one, clPfUV_one, Finset.prod_const_one, mul_one]
  simp [clPfS]

private theorem reduction_mul_of_integral' {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

theorem clPfT_lamGBS_symm (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t J n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS < r) (hJ : r + J * t ≤ n + c) (ht : 0 < t)
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ LocE.JGsym P q k₀ rS r t n c) :
    LocE.lamGBS q ψ₀ χ k₀ r t J n c γ.symm.toLinearMap = (LocE.lamGBS q ψ₀ χ k₀ r t J n c γ.toLinearMap)⁻¹ := by
  have hqn : q ≠ 0 := by
    rintro rfl
    exact hu (by simp)
  have hq0 : ((q : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hqn
  have hrN : r ≤ n + c := le_trans (Nat.le_add_right r (J * t)) hJ
  have hs : γ.symm ∈ LocE.JGsym P q k₀ rS r t n c := (LocE.JGsym P q k₀ rS r t n c).inv_mem hγ
  have hγL := (Subgroup.mem_inf.mp hγ).1
  have hsL := (Subgroup.mem_inf.mp hs).1
  have hkr : k₀ < r := by omega
  have hG := clPf_pat_JGsym hq hu hk hr hrN hs
  have hX := clPf_pat_JGsym hq hu hk hr hrN hγ
  apply eq_inv_of_mul_eq_one_left
  rw [clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hsL, clPf_lamGBS hq0 ψ₀ χ hk hkr hJ hγL]
  have hcomp : ∀ p p', p < n + c → p' < n + c →
      clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap) (clPfRed P q k₀ c n c n γ.toLinearMap) p p' =
      clPfRed P q k₀ c n c n (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p' := by
    intro p p' hp hp'
    have he : (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap = γ.symm.toLinearMap ∘ₗ γ.toLinearMap := by
      ext v
      simp
    rw [he]
    unfold clPfRed
    rw [clPf_entB_compL hq0 hk hk _ _ hp hp']
    rw [redP_sum _ _ (fun u hu' => IntAt.mul (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL)
      (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL))]
    unfold clPfMul
    refine Finset.sum_congr rfl (fun u hu' => ?_)
    exact (reduction_mul_of_integral' (frameEntry_integral_of_stabilizer hq0 hk hp (Finset.mem_range.mp hu') hsL)
      (frameEntry_integral_of_stabilizer hq0 hk (Finset.mem_range.mp hu') hp' hγL)).symm
  have hmul : clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.symm.toLinearMap) *
      clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.toLinearMap) =
      clPfLam ψ₀ χ k₀ r t J (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap)
        (clPfRed P q k₀ c n c n γ.toLinearMap)) := by
    unfold clPfLam
    rw [clPf_S_mulL hr hrN le_rfl hG hX, AddChar.map_add_eq_mul]
    have hblk : ∀ i ∈ Finset.range J,
        clPfUV (χ i) (diagonalBlockMatrix r t i (clPfMul (n + c) (clPfRed P q k₀ c n c n γ.symm.toLinearMap)
          (clPfRed P q k₀ c n c n γ.toLinearMap))).det =
        clPfUV (χ i) (diagonalBlockMatrix r t i (clPfRed P q k₀ c n c n γ.symm.toLinearMap)).det *
          clPfUV (χ i) (diagonalBlockMatrix r t i (clPfRed P q k₀ c n c n γ.toLinearMap)).det := by
      intro i hi
      have hi' : r + i * t + t ≤ n + c := by
        have h3 : (i + 1) * t ≤ J * t := Nat.mul_le_mul_right t (Finset.mem_range.mp hi)
        rw [Nat.add_mul, one_mul] at h3
        omega
      rw [clPf_blk_mulL hr ht le_rfl hG hX hi', Matrix.det_mul, clPfUV_mul]
    rw [Finset.prod_congr rfl hblk, Finset.prod_mul_distrib]
    ring
  rw [hmul, clPf_lam_congr ψ₀ χ hkr.le hJ hcomp, ← clPf_lamGBS hq0 ψ₀ χ hk hkr hJ (Subgroup.one_mem _)]
  exact clPfT_lamGBS_one hq0 ψ₀ χ hk hkr hJ

private theorem intAt_of_redP_ne_zero {F : Type} [Field F] {Q : HeightOneSpectrum (𝓞 F)} {a : F}
    (h : redP Q a ≠ 0) : IntAt Q a := by
  unfold redP at h
  split_ifs at h with hex
  · obtain ⟨c, r, s, hs, h1, -⟩ := hex
    exact ⟨r, s, hs, h1⟩
  · exact absurd rfl h

private theorem redP_mul_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

theorem clPfT_unitV_symm (hq0 : (q : E) ≠ 0) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n c : ℕ} (hk : k₀ ≤ n)
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) :
    (LocE.unitV χ ((LinearEquiv.det γ.symm : Eˣ) : E))⁻¹ = LocE.unitV χ ((LinearEquiv.det γ : Eˣ) : E) := by
  have hs : γ.symm ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) :=
    (stabL E (n + c) _).inv_mem hγ
  have hu1 := clPf_det_unit (k₀ := k₀) hq0 hk hγ
  have hu2 := clPf_det_unit (k₀ := k₀) hq0 hk hs
  rw [← clPf_det_red hq0 hk hγ] at hu1
  rw [← clPf_det_red hq0 hk hs] at hu2
  have i1 := intAt_of_redP_ne_zero hu1.ne_zero
  have i2 := intAt_of_redP_ne_zero hu2.ne_zero
  have hm : ((LinearEquiv.det γ.symm : Eˣ) : E) * ((LinearEquiv.det γ : Eˣ) : E) = 1 := by
    rw [← Units.val_mul, ← map_mul]
    have h1 : γ.symm * γ = 1 := by
      ext v
      simp
    rw [h1, map_one, Units.val_one]
  apply inv_eq_of_mul_eq_one_right
  rw [clPf_unitV, clPf_unitV, ← clPfUV_mul, ← redP_mul_of_intAt i2 i1, hm, redP_one, clPfUV_one]

theorem control_phi_law : CtlPhiLaw := by
  intro E K _ _ _ _ P q ψ₀ χ k₀ rS t j n' n hq hu hj ht hn' hn γ κ hγ hκ x
  have hH : PhiGSLawHyp P q k₀ rS (k₀ + 2 * rS + 1) t j 0 n' 0 n :=
    ⟨hq, hu, hj, by omega, by omega, by omega, ht, by omega, by omega⟩
  have h := clPf_phiGSLaw hH ψ₀ χ γ.symm (Subgroup.inv_mem _ hγ) κ hκ x
  rw [h, clPfT_lamGBS_symm hq hu ψ₀ χ (k₀ := k₀) (rS := rS) (r := k₀ + 2 * rS + 1) (J := j) (n := n) (c := 0) (by omega) (by omega) (by omega) ht hγ,
    clPfT_unitV_symm (ciQ_ne_zero hu) (χ (j - 1)) (k₀ := k₀) (n := n) (c := 0) (by omega) hγ.1]
  ring

end ClPfT

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwCstL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {G : ChGlob X R.m}

open Classical

theorem twCst_D_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).D P = 1 := if_pos hP
theorem twCst_D_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : (twCst Ch sel mu G).D P = 2 * R.m := if_neg hP
theorem twCst_psi_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).psi P = ciPsi Ch P := if_pos hP
theorem twCst_psi_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) :
    (twCst Ch sel mu G).psi P = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) := if_neg hP
theorem twCst_sq_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).sq P = ciSq Ch P.1 := if_pos hP
theorem twCst_sq_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : (twCst Ch sel mu G).sq P = twSqrt P.1 := if_neg hP

theorem twCst_ok (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (hK : TwCstQ (Pr := Pr) sel mu G) :
    (twCst Ch sel mu G).Ok := by
  have hc := ciCst_ok (Ch := Ch) hPr hCh (SB := Pr.vGs) (fun _ h => h) h4 (mq := fun _ _ => 1)
  have h2 := R.two_le_m
  exact
    { psi_add := fun P x y hx hy => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_D_g hP] at hx hy
          rw [twCst_psi_g hP]
          exact hc.psi_add ⟨P.1, hP⟩ x y hx hy
        · rw [twCst_D_Q hP] at hx hy
          rw [twCst_psi_Q hP]
          exact hK.psi_add P hP x y hx hy
      psi_int := fun P x hx => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_psi_g hP]
          exact hc.psi_int ⟨P.1, hP⟩ x hx
        · rw [twCst_psi_Q hP]
          exact hK.psi_int P hP x hx
      psi_ne := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_psi_g hP]
          exact hc.psi_ne ⟨P.1, hP⟩
        · rw [twCst_psi_Q hP]
          exact hK.psi_ne P hP
      D_pos := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_D_g hP]
        · rw [twCst_D_Q hP]; omega
      sq_sq := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_sq_g hP]
          exact hc.sq_sq ⟨P.1, hP⟩
        · rw [twCst_sq_Q hP]
          exact hK.sq_sq P hP
      M_pos := by show 1 ≤ R.m; omega
      M_le_A := by show R.m ≤ R.m + 1; omega
      M_le_B := by show R.m ≤ R.m + 1; omega
      B_pos := by show 1 ≤ R.m + 1; omega }

theorem localConstants_psi_depth_one (hPr : Pr.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (a : X.E) (ha : IntAt P.1 a) :
    (twCst Ch sel mu G).psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) := by
  rw [twCst_psi_g hP]
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr hP).ne_zero
  unfold ciPsi
  rw [mul_div_cancel₀ _ hq0, if_pos ha]

theorem twCst_weil (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : Ch.WeilTied G.σ₀ G.xi0) (hK : TwCstQ (Pr := Pr) sel mu G) :
    (twCst Ch sel mu G).WeilTied G.σ₀ G.xi0 := by
  intro P a b ha hab
  by_cases hP : P.1 ∈ Pr.vGs
  · have hw := ciCst_weil Ch hX hPr (SB := Pr.vGs) (fun _ h => h) (fun _ _ => 1) hW (fun P hP => (ookXiUnit hCh hW P hP).1)
    rw [twCst_D_g hP] at ha hab ⊢
    rw [twCst_psi_g hP]
    exact hw ⟨P.1, hP⟩ a b ha hab
  · rw [twCst_D_Q hP] at ha hab ⊢
    rw [twCst_psi_Q hP]
    exact hK.weil P hP a b ha hab

theorem twCst_base (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (hK : TwCstQ (Pr := Pr) sel mu G) {m2 : ℕ}
    (hm : R.m = m2 + 2) : OcbBase Ch sel mu (twCst Ch sel mu G) m2 := by
  exact
    { hX := hX
      hPr := hPr
      hCh := hCh
      hm := hm
      cst_ok := twCst_ok hPr hCh h4 hK
      sharp := rfl
      psi0 := fun P a hP ha => localConstants_psi_depth_one hPr P hP a ha
      depthG := fun _ hP => twCst_D_g hP }

end TwCstL

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Mat

variable {K : Type} [Field K]

theorem rf_inv_entries_mem (K0 : Subfield K) {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (hA : ∀ i j, A i j ∈ K0) (i j : Fin d) :
    A⁻¹ i j ∈ K0 := by
  let A0 : Matrix (Fin d) (Fin d) K0 := fun i j => ⟨A i j, hA i j⟩
  have e : A = A0.map K0.subtype := rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', e, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← RingHom.map_adjugate]
  exact mul_mem (inv_mem (A0.det).2) ((A0.adjugate i j).2)

end Mat

namespace CSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem pair_mem (R : S.Rat) (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (hy : ∀ i, S.bV.repr y i ∈ cmMax K) :
    S.pair x y ∈ cmMax K := by
  rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
  starRingEnd_apply]
  refine sum_mem fun j _ => mul_mem (hy j) (sum_mem fun i _ => ?_)
  exact mul_mem (Formalism.L2.DIV.star_mem_cmMax (hx i)) (R.pair_rat i j)

theorem csum_mem (R : S.Rat) (f g : S.Cl → S.V) (hf : S.IsRat f) (hg : S.IsRat g) : S.csum f g ∈ cmMax K := by
  unfold CSD.csum
  exact sum_mem fun c _ => mul_mem (inv_mem (natCast_mem _ _)) (pair_mem S R _ _ (hf c) (hg c))

theorem H_mem (R : S.Rat) (hb : S.HasRatBasis) (i j : Fin S.dim) : S.H i j ∈ cmMax K :=
  csum_mem S R _ _ (S.basis_rat hb i) (S.basis_rat hb j)

theorem csum_basis (i : Fin S.dim) (x : Fin S.dim → K) :
    S.csum (S.basis i : S.Cl → S.V) (S.I x) = (S.H *ᵥ x) i := by
  have h := S.csum_sum (Pi.single i 1) x
  have e : S.I (Pi.single i 1) = (S.basis i : S.Cl → S.V) := by
    rw [S.I_eq_sum, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e, Finset.sum_eq_single i] at h
  · rw [h]
    simp [Matrix.mulVec, dotProduct]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem repr_mem (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V))
    (i : Fin S.dim) : S.basis.repr f i ∈ cmMax K := by
  set x : Fin S.dim → K := S.basis.equivFun f with hx
  have hI : S.I x = (f : S.Cl → S.V) := by
    rw [S.I_apply, hx, LinearEquiv.symm_apply_apply]
  have h1 : S.H *ᵥ x = fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    funext i
    rw [← csum_basis, hI]
  have h2 : x = S.H⁻¹ *ᵥ fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  show x i ∈ cmMax K
  rw [h2]
  show ∑ j, S.H⁻¹ i j * S.csum (S.basis j : S.Cl → S.V) (f : S.Cl → S.V) ∈ cmMax K
  exact sum_mem fun j _ => mul_mem (rf_inv_entries_mem _ _ (H_mem S R hb) i j) (csum_mem S R _ _ (S.basis_rat hb j) hf)

theorem actRat_of (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms)
    (hr : ∀ (t : G) (f : S.Forms), S.IsRat (f : S.Cl → S.V) → S.IsRat (r t f : S.Cl → S.V)) : S.ActRat r := by
  intro t i j
  unfold CSD.actMat
  rw [LinearMap.toMatrix_apply]
  exact repr_mem S R hb hdet _ (hr t _ (S.basis_rat hb j)) i

end CSDRat

section GSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem GSD.rho_mem (R : S.Rat) (g : S.G) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    S.bV.repr (S.ρ g x) i ∈ cmMax K := by
  have e : S.ρ g x = S.ρ g (∑ j, S.bV.repr x j • S.bV j) := by rw [S.bV.sum_repr x]
  rw [e]

  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hx j) (R.act_rat g i j)

theorem GSD.det_H_ne_zero (R : S.Rat) (h : S.Ok) : (S.toCSD h).H.det ≠ 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hp := (R.posH h v).det_pos
  intro h0
  have e : ((S.toCSD h).H.map v.embedding).det = v.embedding (S.toCSD h).H.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hp' : 0 < ((S.toCSD h).H.map v.embedding).det := hp
  rw [e, h0, map_zero] at hp'
  exact lt_irrefl _ hp'

theorem GSD.repCSD_actRat (h : S.Ok) (R : S.Rat) {A : Type} [Group A] [Fintype A] (r : Representation K A S.EqFun)
    (hr : ∀ (a : A) (φ : S.EqFun) (d : S.D), ∃ d' : S.D, (r a φ : S.D → S.V) d = (φ : S.D → S.V) d') :
    (S.toCSD h).ActRat (S.repCSD h r) := by
  refine CSDRat.actRat_of _ (S.toCSDOf_rat h R _) (csd_hasRatBasis _ (S.toCSDOf_rat h R _)) (S.det_H_ne_zero R h) _ ?_
  intro t f hf c i
  obtain ⟨d', hd'⟩ := hr t ((S.res h).symm f) (S.outSec.rep c)
  show S.bV.repr ((r t ((S.res h).symm f) : S.D → S.V) (S.outSec.rep c)) i ∈ cmMax K
  rw [hd']
  show S.bV.repr (S.ρ (S.outSec.mv d') ((f.1 : S.Cl → S.V) (S.cls d'))) i ∈ cmMax K
  exact S.rho_mem R _ _ (hf _) i

end GSDRat

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem unipotentActionForms_rational (hX : X.Ok) (h : (mtildeKGSD W Ch sel mu).Ok) :
    (MtildeKCSD W Ch sel mu h).ActRat (g0Act W Ch sel mu h) :=
  GSD.repCSD_actRat _ h (mtildeK_rat W Ch sel mu hX) _ fun _ _ _ => ⟨_, rfl⟩

theorem unipotentActionClassSum_rational (hX : X.Ok) (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) :
    (MtKCSD W Ch sel mu j h).ActRat (unipotentRightActionOnForms W Ch sel mu j h) :=
  GSD.repCSD_actRat _ h (mtK_rat W Ch sel mu hX j) _ fun _ _ _ => ⟨_, rfl⟩

end Rows

end Formalism.L2.Col
end
end
