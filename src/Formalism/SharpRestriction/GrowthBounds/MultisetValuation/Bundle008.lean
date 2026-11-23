module

import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.OddLogRelation
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF altF)

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_dual_even {n' : ℕ} (B : OmBasis p n') (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  classical
  have hAB : (Matrix.of fun (r j : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.om r)) *
      (Matrix.of fun (j r' : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.omS r')) = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply, Matrix.of_apply, iterate_map_mul]
  have hBA := mul_eq_one_comm.mp hAB
  have h := congrFun (congrFun hBA i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa using h

theorem sx_dual {n' : ℕ} (B : OmBasis p n') (hev : Even n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0 := by
  apply Formalism.L2.G.Pend.dualS <;> assumption

theorem frobenius_congruence_witt (a : WW p) : ∃ y : WW p, sigW p a = a ^ p + p * y := by
  obtain ⟨y, hy⟩ := Formalism.InvariantFactorPaths.G7.WModel.frob_sub_pow p a
  exact ⟨y, by unfold sigW; linear_combination hy⟩

theorem sx_lift {ι K' : Type} [Field K'] {R : Subring K'} {f : MvPowerSeries ι K'} (hf : IntR R f) :
    ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = f := by
  refine ⟨fun m => ⟨MvPowerSeries.coeff m f, hf m⟩, ?_⟩
  ext m
  rfl

theorem sx_sum_pow {A α : Type} [CommRing A] (s : Finset α) (x : α → A) :
    ∃ r : A, (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + (p : A) * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow hp.out.ne_zero]⟩
  | insert a s ha ih =>
    obtain ⟨r1, hr1⟩ := ih
    obtain ⟨r2, hr2⟩ := exists_add_pow_prime_eq hp.out (x a) (∑ i ∈ s, x i)
    refine ⟨r1 + x a * (∑ i ∈ s, x i) * r2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr2, hr1]
    ring

theorem sx_frob_sum {ι α K' : Type} [Field K'] (R : Subring K') (s : Finset α) (x : α → MvPowerSeries ι K')
    (hx : ∀ i ∈ s, IntR R (x i)) :
    ∃ Y, IntR R Y ∧ (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y := by
  classical
  have hlift : ∀ i ∈ s, ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = x i :=
    fun i hi => sx_lift (hx i hi)
  choose y hy using hlift
  let y' : α → MvPowerSeries ι R := fun i => if h : i ∈ s then y i h else 0
  obtain ⟨r, hr⟩ := sx_sum_pow (p := p) s y'
  refine ⟨MvPowerSeries.map R.subtype r, fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n r).2
  · have hsum : ∀ i ∈ s, MvPowerSeries.map R.subtype (y' i) = x i := fun i hi => by
      simp only [y', dif_pos hi]
      exact hy i hi
    have h2 := congrArg (MvPowerSeries.map R.subtype) hr

    simp only [map_pow, map_sum, map_add (f := _), map_mul, map_natCast] at h2
    have e3 : ∑ i ∈ s, (MvPowerSeries.map R.subtype (y' i)) ^ p = ∑ i ∈ s, x i ^ p :=
      Finset.sum_congr rfl fun i hi => by rw [hsum i hi]
    rw [Finset.sum_congr rfl hsum, e3] at h2
    rw [h2, map_natCast]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem inLatC_sum {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {κ : Type*} (s : Finset κ) (f : κ → XspC (X.Pj j) Y.Kc)
    (h : ∀ k ∈ s, Y.inLatC j g L (f k)) : Y.inLatC j g L (∑ k ∈ s, f k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  exact AddSubgroup.sum_mem _ h

theorem inLatC_smulC {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (b : Y.Kc) (k : ℤ)
    (hb : b * (p : Y.Kc) ^ k ∈ Y.Oc) {y : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y) :
    Y.inLatC j (g - k) L (b • y) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  have hm := AddSubgroup.mem_map_of_mem (DistribSMul.toAddMonoidHom (XspC (X.Pj j) Y.Kc) b) h
  rw [AddMonoidHom.map_closure] at hm
  refine AddSubgroup.closure_mono ?_ hm
  rintro _ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩
  exact ⟨b * a, geC_mul_shift (Y := Y) k ha hb, z, hz, by simp [smul_smul]⟩

theorem inLatC_rep {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {y' : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y') :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Y.Kc) (z : κ → (X.Pj j).Xsp), (∀ k, Y.geC (a k) g) ∧
      (∀ k, z k ∈ (X.Pj j).HtupW L) ∧ y' = ∑ k, a k • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (z k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => a, fun _ => z, fun _ => ha, fun _ => hz, by simp⟩
  | zero =>
    exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun k => k.elim, fun k => k.elim, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    obtain ⟨κ2, i2, a2, z2, ha2, hz2, rfl⟩ := hy
    refine ⟨κ1 ⊕ κ2, inferInstance, Sum.elim a1 a2, Sum.elim z1 z2, ?_, ?_, ?_⟩
    · rintro (k | k)
      exacts [ha1 k, ha2 k]
    · rintro (k | k)
      exacts [hz1 k, hz2 k]
    · rw [Fintype.sum_sum_type]
      rfl
  | neg x _ hx =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    refine ⟨κ1, i1, fun k => -a1 k, z1, fun k => geC_neg (Y := Y) (ha1 k), hz1, ?_⟩
    simp [neg_smul]

theorem descent {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (y : (X.Pj j).Xsp)
    (h : Y.inLatC j g L (MvPolynomial.map (algebraMap X.G.Kf Y.Kc) y)) :
    y ∈ scale (X.vsc g) ((X.Pj j).HtupW L) := by
  classical
  obtain ⟨κ, _, a, z, ha, hz, hy⟩ := inLatC_rep Y h
  obtain ⟨c, hc, hyc⟩ := descent_core (K := X.G.Kf) (Kc := Y.Kc) (V := (X.Pj j).Xsp) (Vc := XspC (X.Pj j) Y.Kc)
    (MvPolynomial.map (algebraMap X.G.Kf Y.Kc)).toAddMonoidHom
    (by
      intro c v
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C])
    (fun m => MvPolynomial.lcoeff X.G.Kf m) (fun m => MvPolynomial.lcoeff Y.Kc m)
    (by intro m v; simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map])
    (by
      intro v hv
      ext m
      simpa [MvPolynomial.lcoeff_apply] using hv m)
    (RK X) (RK_val Y) (geCgrp Y g)
    (by
      intro r hr a ha
      exact geC_mul_Oc Y ha ((mem_RK_iff Y).mp hr))
    (Finset.univ : Finset κ).card Finset.univ rfl z a (fun k _ => ha k) y hy
  rw [hyc]
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 := vGeK_of_geC Y (c k) g (hc k (Finset.mem_univ k))
  unfold Sys.vGeK at h1
  rw [mem_scale_iff] at h1
  obtain ⟨o, ho, hok⟩ := h1
  obtain ⟨t, rfl⟩ := mem_intKF.mp ho
  rw [mem_scale_iff]
  refine ⟨t • z k, Submodule.smul_mem _ _ (hz k), ?_⟩
  rw [← hok, smul_eq_mul, mul_smul, algebraMap_smul]

theorem natInv_mem (m : ℕ) (hm : ¬ p ∣ m) : ((m : Y.Kc))⁻¹ ∈ Y.Oc := by
  have hk : ((m : kb p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (kb p) p]
    exact hm

  have hu : IsUnit ((m : WW p)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have hc : WittVector.constantCoeff ((m : WW p)) = (m : kb p) := map_natCast _ m
    change WittVector.constantCoeff ((m : WW p)) ≠ 0
    rw [hc]
    exact hk
  obtain ⟨u, hu⟩ := hu
  have h1 : algebraMap (K0 p) Y.Kc (algebraMap (WW p) (K0 p) (↑u⁻¹ : WW p)) * (m : Y.Kc) = 1 := by
    rw [← map_natCast (algebraMap (K0 p) Y.Kc), ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul,
      ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Y.witt_mem_integers_Cp _

theorem wt_inv (N d : ℕ) (hpos : 0 < N) (hle : padicValNat p N ≤ d) :
    ((N : Y.Kc))⁻¹ * (p : Y.Kc) ^ ((d : ℕ) : ℤ) ∈ Y.Oc := by
  have hpp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hpp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have he : e ≤ d := by
    have hv : padicValNat p (p ^ e * m) = e := by
      rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hpp.ne_zero) hm0,
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
    omega
  have hp := pKc_ne (Y := Y)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have key : ((p ^ e * m : ℕ) : Y.Kc)⁻¹ * (p : Y.Kc) ^ (((e + k : ℕ)) : ℤ) = ((m : Y.Kc))⁻¹ * (p : Y.Kc) ^ k := by
    rw [zpow_natCast, pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((p : Y.Kc) ^ e)⁻¹),
      mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hp)]
  rw [key]
  exact Y.Oc.mul_mem (natInv_mem Y m hm) (Y.Oc.pow_mem (natCast_mem Y.Oc p) _)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem nd_al_le (s : Fin (G.P.n' v)) (hs : s ∈ Fl.TT v) (hm : 2 ≤ G.P.m) :
    al (Fl.TT v) (G.P.lam0 v) s ≤ Fl.a v s + (Fl.c : ℤ) := by
  unfold al
  rw [if_pos hs, lambda_index_one v s hm, lambda_index_two v s hm]
  have hb := (Fl.base v s).1 hs
  have := (abs_le.1 (hb.2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).1
  have h0 : G.P.lam0 v s ⟨0, by omega⟩ = Fl.a v s := hb.1
  omega

theorem nd_c_le_w (s : Fin (G.P.n' v)) (l : ℕ) (hl : 1 ≤ l) : (Fl.c : ℤ) ≤ Fl.w v l s :=
  le_trans (le_trans (le_max_left _ _) (Fl.w_ge v s)) (nc_w_ge Fl v s l hl)

theorem nd_lam_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ G.P.m + 1)
    (h : s ∈ Fl.TT v → 2 ≤ i) : lamI (G.P.lam0 v) s i ≤ (Fl.c : ℤ) := by
  unfold lamI
  rw [dite_eq_left ⟨h1, h2⟩]
  have hb := Fl.base v s
  by_cases hs : s ∈ Fl.TT v
  · have h3 := (abs_le.1 ((hb.1 hs).2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).2
    have hd : Antitone (G.P.lam0 v s) := G.P.dom v s
    have h4 := hd (show (⟨1, by omega⟩ : Fin (G.P.m + 1)) ≤ ⟨i - 1, by omega⟩ by
      rw [Fin.le_def]; have := h hs; simp only; omega)
    omega
  · exact (abs_le.1 (hb.2 hs _)).2

theorem nd_lsz_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (j : ℕ) (hj : 1 ≤ j) :
    lsz Fl.t (Fl.TT v) (G.P.lam0 v) (Fl.w v) j s ≤ (NN G.P.m Fl.t j : ℤ) * ((Fl.c : ℤ) + Fl.w v j s) := by
  unfold lsz
  have h1N : 1 ∈ Icc 1 (NN G.P.m Fl.t j) := Finset.mem_Icc.2 ⟨le_rfl, by unfold NN; omega⟩
  have e : ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - al (Fl.TT v) (G.P.lam0 v) s =
      ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' _ 1, if_pos h1N]
  rw [e]
  have hb : ∀ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) ≤ (Fl.c : ℤ) + Fl.w v j s := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold nu
    by_cases hik : i ≤ G.P.m + 1
    · rw [if_pos ⟨hi.1, hik⟩]
      by_cases hi1 : i = 1
      · subst hi1
        rw [if_pos rfl]
        unfold al
        by_cases hs : s ∈ Fl.TT v
        · rw [if_pos hs]
          have := nd_lam_le Fl v s hm 2 (by omega) (by omega) (fun _ => le_rfl)
          omega
        · rw [if_neg hs]
          have := nd_lam_le Fl v s hm 1 le_rfl (by omega) (fun h => absurd h hs)
          omega
      · rw [if_neg hi1]
        have := nd_lam_le Fl v s hm i hi.1 hik (fun _ => by omega)
        omega
    · rw [if_neg (fun h => hik h.2), if_pos ⟨by omega, hi.2⟩, if_neg (by omega)]
      have := nd_c_le_w Fl v s ((i - (G.P.m + 2)) / (Fl.t + 1) + 1) (Nat.le_add_left 1 _)
      have hc : (0 : ℤ) ≤ (Fl.c : ℤ) := Int.natCast_nonneg _
      omega
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
  simpa using this

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

section CgCalc

variable {ι K : Type} [Field K] (R : Subring K) (pp : K)

def Cg (f g : MvPowerSeries ι K) : Prop := ∃ Y : MvPowerSeries ι K, IntR R Y ∧ f = g + MvPowerSeries.C pp * Y

variable {R pp}

theorem cg_refl (f : MvPowerSeries ι K) : Cg R pp f f := ⟨0, IntR_zero, by simp⟩

theorem cg_of_eq {f g : MvPowerSeries ι K} (h : f = g) : Cg R pp f g := h ▸ cg_refl f

theorem cg_trans {f g k : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_add {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f + f') (g + g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_sum {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Cg R pp (F a) (G a)) :
    Cg R pp (∑ a ∈ s, F a) (∑ a ∈ s, G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cg_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cg_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem cg_mul {f g f' g' : MvPowerSeries ι K} (hf' : IntR R f') (hg : IntR R g) (h1 : Cg R pp f g)
    (h2 : Cg R pp f' g') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  refine ⟨g * Y' + Y * f', IntR_add (IntR_mul hg hY') (IntR_mul hY hf'), ?_⟩
  rw [e]
  conv_lhs => rw [add_mul, e']
  conv_rhs => rw [e']
  ring

theorem cg_pow {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) (h : Cg R pp f g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq (by simp)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul hf (IntR_pow hg k) ih h

theorem cg_of_coeff {f g : MvPowerSeries ι K}
    (h : ∀ n, ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y) : Cg R pp f g := by
  choose y hy he using h
  let Y : MvPowerSeries ι K := fun n => y n
  have hYc : ∀ n, MvPowerSeries.coeff n Y = y n := fun _ => rfl
  refine ⟨Y, fun n => by rw [hYc]; exact hy n, ?_⟩
  ext n
  rw [map_add (f := _), MvPowerSeries.coeff_C_mul, he n, hYc]

theorem cg_coeff {f g : MvPowerSeries ι K} (h : Cg R pp f g) (n : ι →₀ ℕ) :
    ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨_, hY n, by rw [e, map_add (f := _), MvPowerSeries.coeff_C_mul]⟩

end CgCalc

section Pos

theorem th_posSub_posAdd {n' : ℕ} (s : Fin n') (d : ℕ) : posSub (posAdd s d) d = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := s.pos; omega⟩
  apply Fin.ext
  show ((s.val + d) % (m + 1) + (m + 1) * d - d) % (m + 1) = s.val
  have e : (s.val + d) % (m + 1) + (m + 1) * d - d = (s.val + d) % (m + 1) + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : s.val + d + m * d = s.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

theorem th_posAdd_posSub {n' : ℕ} (t : Fin n') (d : ℕ) : posAdd (posSub t d) d = t := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := t.pos; omega⟩
  apply Fin.ext
  show ((t.val + (m + 1) * d - d) % (m + 1) + d) % (m + 1) = t.val
  have e : t.val + (m + 1) * d - d = t.val + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : t.val + m * d + d = t.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

theorem th_odd_posAdd {n' : ℕ} (hev : Even n') (s : Fin n') (d : ℕ) :
    (posAdd s d).val % 2 = (s.val + d) % 2 := by
  show (s.val + d) % n' % 2 = _
  exact Nat.mod_mod_of_dvd _ hev.two_dvd

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
