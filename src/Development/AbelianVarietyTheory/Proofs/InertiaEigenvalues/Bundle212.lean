module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import GroundTheory.PAdicHodge.Bundle002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValResultantEqDegreeMulUnramifiedExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem oc_eq_normInteger : (𝓞_ℂ_[l]).toSubring = normInteger ℂ_[l] := by
  ext x
  rw [mem_normInteger, ← GlobalTheory.RingBasics.mem_OC]
  rfl

noncomputable def ocEquiv : OC l ≃+* normInteger ℂ_[l] := RingEquiv.subringCongr (oc_eq_normInteger l)

theorem coe_ocEquiv (x : OC l) : ((ocEquiv l x : normInteger ℂ_[l]) : ℂ_[l]) = (x : ℂ_[l]) := rfl

theorem span_map_ocEquiv :
    Ideal.span {(l : normInteger ℂ_[l])} = (Ideal.span {(l : OC l)}).map ((ocEquiv l : OC l →+* normInteger ℂ_[l])) := by
  rw [Ideal.map_span, Set.image_singleton]; simp

noncomputable def modEquiv : ModP (OC l) l ≃+* ModP (normInteger ℂ_[l]) l :=
  Ideal.quotientEquiv _ _ (ocEquiv l) (span_map_ocEquiv l)

noncomputable def flTo : Fl l →+* PreTilt (normInteger ℂ_[l]) l :=
  Perfection.map l (modEquiv l : ModP (OC l) l →+* ModP (normInteger ℂ_[l]) l)

noncomputable def flFrom : PreTilt (normInteger ℂ_[l]) l →+* Fl l :=
  Perfection.map l ((modEquiv l).symm : ModP (normInteger ℂ_[l]) l →+* ModP (OC l) l)

theorem coeff_flTo (x : Fl l) (n : ℕ) :
    Perfection.coeff _ l n (flTo l x) = modEquiv l (Perfection.coeff _ l n x) := rfl

theorem coeff_flFrom (x : PreTilt (normInteger ℂ_[l]) l) (n : ℕ) :
    Perfection.coeff _ l n (flFrom l x) = (modEquiv l).symm (Perfection.coeff _ l n x) := rfl

noncomputable def flEquiv : Fl l ≃+* PreTilt (normInteger ℂ_[l]) l :=
  RingEquiv.ofRingHom (flTo l) (flFrom l)
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flTo l (flFrom l x)) = Perfection.coeff _ l n x
      rw [coeff_flTo, coeff_flFrom, RingEquiv.apply_symm_apply])
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flFrom l (flTo l x)) = Perfection.coeff _ l n x
      rw [coeff_flFrom, coeff_flTo, RingEquiv.symm_apply_apply])

theorem flEquiv_apply (x : Fl l) : flEquiv l x = flTo l x := rfl

theorem untilt_flTo (x : Fl l) : (flTo l x).untilt = ocEquiv l x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : normInteger ℂ_[l])}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ l n x)
  refine ⟨ocEquiv l y, ?_, ?_⟩
  · rw [coeff_flTo, ← hy]
    rfl
  · have := (Perfection.teichmuller_sModEq hy).symm
    rw [SModEq.sub_mem, GlobalTheory.RingBasics.mem_span_pow_OC] at this
    have hl : ((l : normInteger ℂ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [SModEq.sub_mem, mem_span_singleton_pow_iff, ← map_pow, ← map_sub, coe_ocEquiv, hl]
    exact this

theorem exists_flEquiv_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l,
    ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  intro l _
  refine ⟨flEquiv l, fun x => ?_⟩
  rw [flEquiv_apply, untilt_flTo, coe_ocEquiv]
  rfl

end GlobalTheory.PSer
end

section

noncomputable section

namespace GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}


omit [CompleteSpace K] in
theorem conn_mem_ext_Rpi (D : BKDat O K l e a ι η H) {y : Vec K a ι}
    (hy : y ∈ D.ext (Rpi O K l e)) : D.conn y ∈ D.ext (Rpi O K l e) := by
  have hf : ∀ i τ, (Matrix.mulVec (D.mxInv τ) (y τ)) i ∈ Rpi O K l e := fun i τ =>
    D.mem_extc_iff.1 (mem_tot.1 hy τ) i

  rw [D.eq_sum_phi_bas y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : D.phi (bas i) ∈ D.L := D.phi_mem_L (D.bas_mem_M i)
  have hM : D.phi (bas i) ∈ D.MM := D.ext_mono (A_le_S l e) hL
  rw [PhiMod.conn_smul_tot]
  refine Submodule.add_mem _ ?_ ?_
  · exact D.smul_tot_mem_ext (fun τ => N_mem (derivative_mem_R l (hf i τ)))
      (D.ext_mono (S_le_R l e) hM)
  · exact D.smul_tot_mem_ext (hf i) (D.ext_mono (S_le_R l e) (D.conn_mem_MM hM))

omit [CompleteSpace K] in
theorem EN_add_smul_mem_shiftE' (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι)
    (hx : x ∈ shiftE l e j (D.ext (Rpi O K l e))) :
    D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  rw [mem_shiftE] at hx ⊢
  set y := Ezpow K l e (-j) • x with hy
  have hxy : x = Ezpow K l e j • y := by
    rw [hy, smul_smul, mul_comm, Ezpow_neg_mul, one_smul]
  clear_value y
  clear hy
  have h1 : Ezpow K l e (j + 1) = Ezpow K l e j * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  have hc : ((j * e * l : ℤ) : K) • x = ((j * e * l : ℤ) : K⟦X⟧) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hN : E K l e * N K (Ezpow K l e j) + ((j * e * l : ℤ) : K⟦X⟧) * Ezpow K l e j =
      Ezpow K l e (j + 1) * ((j * e : ℤ) : K⟦X⟧) := by
    rw [E_mul_N_Ezpow, N_E, h1, E]
    push_cast
    ring
  have key : D.EN x + ((j * e * l : ℤ) : K) • x =
      Ezpow K l e (j + 1) • ((j * e : ℤ) • y + D.conn y) := by
    rw [hc, PhiMod.EN_apply, hxy, PhiMod.conn_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      ← Int.cast_smul_eq_zsmul K⟦X⟧ (j * e : ℤ), smul_smul, ← hN, add_smul, h1, mul_comm (E K l e) (Ezpow K l e j)]
    abel
  rw [key, smul_smul, Ezpow_neg_mul, one_smul]
  exact Submodule.add_mem _ (zsmul_mem hx _) (conn_mem_ext_Rpi D hx)

theorem EN_add_smul_mem_shiftE :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j x hx
  exact EN_add_smul_mem_shiftE' D j x hx

end GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded
end
end

section

open PowerSeries GlobalTheory.BK

noncomputable section

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

theorem PhiMod.eq_xi_red_of_conn_eq_zero (P : PhiMod O K l e a ι) {v : Vec K a ι}
    (h : P.conn v = 0) : v = P.xi (red v) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [PhiMod.conn_xiExt] at h
  have hN : ∀ τ i, N K (w τ i) = 0 := fun τ i => by
    have := congrFun (congrFun (P.xiExt.injective (h.trans (map_zero _).symm)) τ) i
    simpa using this
  have hw : w = cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | n
    · simp
    · have := congrArg (coeff (n + 1)) (hN τ i)
      rw [coeff_N, map_zero] at this
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  rw [PhiMod.xi_apply, PhiMod.red_xiExt, ← hw]

theorem PhiMod.mem_ext_of_plusInl (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    (h : (P.plusInl hy).app v ∈ (P.plus hy).ext B) : v ∈ P.ext B := by
  rw [PhiMod.plusInl_app] at h
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, hmv⟩ := (P.plus hy).mem_extc.1 (mem_tot.1 h τ)
  refine P.mem_extc.2 ⟨fun i => m (Sum.inl i), fun i => hm (Sum.inl i), ?_⟩
  have h0 : m (Sum.inr ()) = 0 := by
    have := congrFun hmv (Sum.inr ())
    simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this.symm
  funext i
  have := congrFun hmv (Sum.inl i)
  simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using this

end GlobalTheory.BK

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

theorem exists_conn_eq_zeta_of_mem_Y (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Y) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  have hy' := mem_invE_of_mem_Y hy
  set P := D.toPhiMod.plus hy'
  set F := D.toPhiMod.plusInl hy'
  set G := D.toPhiMod.plusProj hy'
  set t := P.phi xVec - P.xi (red (P.phi xVec)) with ht
  have inj : ∀ v w, F.app v = F.app w → v = w := fun v w h => by
    rw [PhiMod.plusInl_app, PhiMod.plusInl_app] at h
    funext τ i
    exact congrFun (congrFun h τ) (Sum.inl i)
  have hct : P.conn t = F.app (D.zeta y) := by
    rw [ht, map_sub, PhiMod.conn_xi, sub_zero]
    exact D.conn_phi_extension_generator_eq_zeta hy'
  have hrt : red t = 0 := by
    rw [ht, map_sub, PhiMod.red_xi, sub_self]
  have hx : G.app t = 0 := by
    have h1 : (rankOne O K l e fun _ : ZMod a => 0).conn (G.app t) = 0 := by
      rw [← Hom.app_conn, hct, PhiMod.plusInl_app, PhiMod.plusProj_app]
      rfl
    rw [PhiMod.eq_xi_red_of_conn_eq_zero _ h1, Hom.red_app, hrt, map_zero, map_zero]
  have key : ∀ τ, t τ (Sum.inr ()) = 0 := fun τ => by
    rw [← join_eta t, PhiMod.plusProj_app] at hx
    have := congrFun (congrFun hx τ) ()
    simpa using this
  set s : Vec K a ι := fun τ i => t τ (Sum.inl i)
  have hts : t = F.app s := by
    rw [PhiMod.plusInl_app]
    conv_lhs => rw [← join_eta t]
    congr 1
    funext τ
    exact key τ
  have hxM : (xVec : Vec K a (ι ⊕ Unit)) ∈ P.M := by
    rw [← PhiMod.bas_inr]
    exact P.bas_mem_M _
  have htM : t ∈ P.MMl := by
    refine sub_mem (P.ext_mono ((A_le_S l e).trans (le_away _ _)) (P.phi_mem_L hxM)) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a (ι ⊕ Unit) P).2 _).2 (mem_tot.2 fun τ i => ?_)
    rw [cst_apply]
    exact HasK.C_mem _
  refine ⟨s, D.toPhiMod.mem_ext_of_plusInl hy' (hts ▸ htM), fun g => ?_, inj _ _ ?_⟩
  · have hΔ : (D.desc.plus hy' hy.2).act g t = t := by
      rw [ht, map_sub, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g, Descent.act_xi,
        ← Descent.red_act, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g]
    apply inj
    have h2 : (D.desc.plus hy' hy.2).act g (F.app s) = F.app s := by rw [← hts]; exact hΔ
    exact ((Descent.plusInl D.desc hy' hy.2).app_act g s).trans h2
  · rw [Hom.app_conn, ← hts, hct]

end BKDat

end GlobalTheory.BK

namespace GlobalTheory.BK

namespace BKDat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem exists_conn_eq_zeta (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Yl) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  obtain ⟨n, hn⟩ := D.desc.mem_Yl_iff.1 hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta_of_mem_Y hn
  have hl : ((l : K) ^ n) ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ n)⁻¹ • s, ?_, D.desc.inv.smul_mem _ hsi, ?_⟩
  · have : ((l : K) ^ n)⁻¹ • s = (fun _ : ZMod a => C ((l : K) ^ n)⁻¹) • s := by
      funext τ i
      simp [smul_eq_C_mul]
    rw [this]
    exact D.smul_tot_mem_ext (fun _ => HasK.C_mem _) hsM
  · rw [map_smul, hsc, map_smul, smul_smul, inv_mul_cancel₀ hl, one_smul]

theorem Mon_mem_range_Lc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl,
    (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧
      D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta hy
  have hyi : ∀ g, D.desc.act g y = y := hy.2
  have hsi' : ∀ g, D.desc.act g s = s := hsi
  refine ⟨⟨s, hsM, hsi, hsc, ?_⟩, D.cls (y - s), ⟨⟨y - s, ?_, rfl⟩, fun g => ?_⟩, ?_⟩
  · set v := D.phi s - s - D.phi y with hv
    have hcv : D.conn v = 0 := by
      have hz := D.zeta_eq y
      rw [PhiMod.lphi_apply, map_sub, smul_sub] at hz
      rw [hv, map_sub, map_sub, PhiMod.conn_phi, PhiMod.conn_phi, hsc, sub_right_comm]
      exact sub_eq_zero.2 hz.symm
    refine ⟨red v, fun g => ?_, D.eq_xi_red_of_conn_eq_zero hcv⟩
    rw [← Descent.red_act, hv]
    congr 1
    rw [(D.desc.act g).map_sub, (D.desc.act g).map_sub, Descent.act_phi, Descent.act_phi, hsi' g,
      hyi g]
  · rw [SetLike.mem_coe, mem_divE, smul_sub]
    refine sub_mem ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_A_le_Rpi l e) (mem_divE.1 hy.1)))
      ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_S_le_Rpi l e)
        (D.smul_mem_Mext ((A_le_S l e).trans (le_away _ _)) hsM)))
  · rw [Descent.actPol_cls, map_sub, hyi g, hsi' g]
  · rw [Lc_cls, PhiMod.Mon_apply, map_sub, PhiMod.EN_apply D.toPhiMod s, hsc]

end BKDat

end GlobalTheory.BK
end
end

section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK

namespace PhiMod

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NeZero a]

theorem exists_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.MMl) :
    ∃ N : ℕ, (l : K) ^ N • v ∈ P.MM := by
  have hc : ∀ p : ZMod a × ι, ∃ n : ℕ,
      (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e := by
    intro p
    obtain ⟨n, hn⟩ := mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)
    exact ⟨n, by simpa using hn⟩
  choose n hn using hc
  refine ⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast,
    pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))

theorem mem_MMl_of_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {w : Vec K a ι} (N : ℕ)
    (h : (l : K) ^ N • w ∈ P.MM) : w ∈ P.MMl := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)
  have h1 := mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast] at h1
  simpa using h1

end PhiMod

theorem BKDat.phi_mem_MMl : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv
  obtain ⟨N, hN⟩ := D.toPhiMod.exists_lpow_smul_mem_MM hv
  have h := PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN
  rw [map_smul, smul_smul, ← pow_add] at h
  exact D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_integral_leftInverse_of_phiModule_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  first | exact @GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple | exact GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple | (intros; apply GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.injective_of_phiModule_exact_triple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  first | exact @GlobalTheory.BK.IsExactTriple.injective_app | exact GlobalTheory.BK.IsExactTriple.injective_app | (intros; apply GlobalTheory.BK.IsExactTriple.injective_app <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | exact GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | (intros; apply GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr <;> assumption)
end

section

noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem E_pow_mul_mem_colon_frob (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a) :
    ∀ α ∈ colon O K (F.mat τ),
      (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  intro α hα w hw
  set x := D₂.mx τ *ᵥ w with hxdef
  have hx : x ∈ D₂.Lcomp τ := D₂.mem_extc.2 ⟨w, hw, rfl⟩
  have hxL : (Pi.single τ x : Vec K a κ) ∈ D₂.L := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      simpa using hx
    · simp [h, zero_mem]
  have hup := mem_tot.1 (D₂.upper _ hxL) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hup
  obtain ⟨m, hm, hαm⟩ := hα (E K l e ^ η • x) hup
  have hmM : (Pi.single τ m : Vec K a ι) ∈ D₁.M := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      rw [Pi.single_eq_same]
      exact hm
    · simp [h, zero_mem]
  have hlow := mem_tot.1 (D₁.lower _ hmM) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hlow
  obtain ⟨m', hm', hm'eq⟩ := D₁.mem_extc.1 hlow
  have hE : PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) =
      E K l e ^ (H + η) * PowerSeries.map (algebraMap O K) α := by
    simp [E, map_X, map_natCast]
  refine ⟨m', hm', ?_⟩
  · have key : D₂.mx τ *ᵥ (PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) • w) =
        D₂.mx τ *ᵥ ((F.mat (τ - 1)).map (frob K l) *ᵥ m') := by
      rw [Matrix.mulVec_smul, ← hxdef, hE, pow_add,
        show E K l e ^ H * E K l e ^ η * PowerSeries.map (algebraMap O K) α =
          E K l e ^ H * (PowerSeries.map (algebraMap O K) α * E K l e ^ η) by ring,
        mul_smul, mul_smul, hαm,
        ← Matrix.mulVec_smul, hm'eq, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
    have := congrArg (fun v => D₂.mxInv τ *ᵥ v) key
    rwa [Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ),
      Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ), PhiMod.mxInv_mul_mx,
      Matrix.one_mulVec, Matrix.one_mulVec] at this

end GlobalTheory.LiftCoker
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_large_compactOpen_subgroup_with_small_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  first | exact @GlobalTheory.JR.WeilQuad.LargeLattice.main | exact GlobalTheory.JR.WeilQuad.LargeLattice.main | (intros; apply GlobalTheory.JR.WeilQuad.LargeLattice.main <;> assumption)
end
