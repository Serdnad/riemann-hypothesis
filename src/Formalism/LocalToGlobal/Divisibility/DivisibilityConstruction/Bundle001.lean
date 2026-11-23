module

public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle006
public import Formalism.SharpRestriction.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
public import Formalism.LocalToGlobal.Divisibility.RecBridge
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

theorem two_r_sq_le_b (L : SizeData₂ D) (hSC : SizeCond L) : 2 * (D.R.r : ℝ) ^ 2 ≤ L.sc.b := by
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hc1 : (1 : ℝ) ≤ szCond L := by
    unfold szCond
    have h4 : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
    have h5 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
    nlinarith
  have hrt : D.R.r + 5 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  have ht5 : (5 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 5 ≤ D.R.t)
  have hrt' : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have ht0 : (0 : ℝ) ≤ D.R.t := by linarith
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _

  have hpow : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := by
    have h1 : (1 : ℝ) ≤ szCond L ^ 36 := one_le_pow₀ hc1
    have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := pow_nonneg ht0 _
    have := hSC
    unfold SizeCond at this
    nlinarith

  have h2t : 2 * (D.R.t : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 150 := by
    have h148 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 148 := by
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.t : ℝ) := ht5
        _ = (D.R.t : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.t : ℝ) ^ 148 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (D.R.t : ℝ) ^ 150 = (D.R.t : ℝ) ^ 2 * (D.R.t : ℝ) ^ 148 := by ring
    rw [this]
    nlinarith [pow_nonneg ht0 2]

  have hb1 : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)
  have hsq : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hrt' 2
  linarith

theorem log_card_le_unitE {G : Type} [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ)
    (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    Real.log (Fintype.card G : ℝ) ≤ 2 * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) := by
  have hx1 : 1 ≤ L.sc.x := le_of_lt L.sc.one_lt_alt
  have hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hX0 : (0 : ℝ) ≤ L.sc.x ^ L.sc.eps := by linarith
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos

  have hlam : Real.log (Fintype.card G : ℝ) ≤
      2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := by
    have h := GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)
    rw [hc]
    exact h

  have hth : L.sc.x ^ szTh L ≤ L.sc.x ^ L.sc.eps := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h1 := (hSG 0 0).2.2
    have h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
      show L.sc.x ^ szTh L * L.sc.x ^ L.sc.eps ≤ _
      exact mul_le_mul_of_nonneg_right hth hX0
    have h3 := Real.log_two_lt_d9
    have h4 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by nlinarith
    linarith
  have hr := two_r_sq_le_b L hSC
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := pow_nonneg (Nat.cast_nonneg _) 2
  have hb0 : (0 : ℝ) ≤ L.sc.b := by linarith
  set X := L.sc.x ^ L.sc.eps with hXdef

  have hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) := rfl
  rw [hU]
  have hXX : (0 : ℝ) ≤ X * X := mul_nonneg hX0 hX0
  calc Real.log (Fintype.card G : ℝ)
      ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * (X * X)) := by
        refine hlam.trans (mul_le_mul_of_nonneg_left hlg ?_)
        positivity
    _ = (D.R.f : ℝ) * (2 * (D.R.r : ℝ) ^ 2) * (2 * (X * X)) := by ring
    _ ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 2 * L.sc.b) * (2 * (X * X)) := by
        have : 2 * (D.R.r : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.b := by
          have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hm2 hb0
          linarith
        have h2 : (0 : ℝ) ≤ 2 * (X * X) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hf0) h2
    _ = 2 * ((D.R.m : ℝ) * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + 0))) := by ring
    _ ≤ 2 * ((D.R.m : ℝ) * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc))) := by
        have hm0 : (0 : ℝ) ≤ D.R.m := by linarith
        gcongr

theorem lamSizeAt_record {G : Type} [Group G] [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L) (Del h0 : ℕ)
    (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (s : ℕ) (cs : ℝ)
    (hs : Real.log (s : ℝ) ≤ cs * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc)) :
    LamSizeAt (G := G) (ofRecord D L Del h0) Nc s (2 + cs) := by
  have h1 := log_card_le_unitE (G := G) L hSG hSC Del h0 Nc hNc hc
  unfold LamSizeAt
  have key : (2 + cs) * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) =
      2 * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) + cs * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) := by
    ring
  show Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ (2 + cs) * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc)
  rw [key]
  linarith

theorem lamSizeAt_record_one {G : Type} [Group G] [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L)
    (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    LamSizeAt (G := G) (ofRecord D L Del h0) Nc 1 2 := by
  have h := lamSizeAt_record (G := G) L hSG hSC Del h0 Nc hNc hc 1 0 (by simp)
  have e : (2 : ℝ) + 0 = 2 := by norm_num
  rw [e] at h
  exact h

end Formalism.L2.DIV.Cons

end
end

section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Indef Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.DIV.Cons

variable {D : D7}

def nuOf (L : SizeData₂ D) (u : D.what₂.Word) {d : ℕ} (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) :
    Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL) :=
  (L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))

private theorem sg_eq_zero_of_not_mem_supp (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : w ∉ L.supp) :
    L.sg u w = 0 := by
  unfold Formalism.BasicNotions.SizeData₂.sg
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [Formalism.BasicNotions.SizeData₂.gainD, L.gain_supp j w hw, L.F_supp j w hw, L.E_supp u j w hw]

private theorem shiftIdeal_shiftZ_sgRec_eq_Iu (L : SizeData₂ D) (u : D.what₂.Word) :
    Formalism.DivisionValues.shiftIdeal (shiftZ (sgRec L u)) = Formalism.BasicNotions.DV.Iu D L u := by
  have hfun : ∀ i, shiftZ (sgRec L u) (D.plEq i) = ⌊Formalism.BasicNotions.DV.ur D i (L.sg u i)⌋ := by
    intro i
    simp [shiftZ, sgRec]
  calc Formalism.DivisionValues.shiftIdeal (shiftZ (sgRec L u))
      = ∏ᶠ i, ((D.plEq i).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
          (-(shiftZ (sgRec L u) (D.plEq i))) := by
        rw [Formalism.DivisionValues.shiftIdeal]
        exact (finprod_comp_equiv D.plEq).symm
    _ = ∏ᶠ i, ((D.plEq i).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
          (-⌊Formalism.BasicNotions.DV.ur D i (L.sg u i)⌋) := by
        simp only [hfun]
    _ = Formalism.BasicNotions.DV.Iu D L u := by
        unfold Formalism.BasicNotions.DV.Iu
        refine finprod_eq_prod_of_mulSupport_subset _ ?_
        intro i hi
        rw [Function.mem_mulSupport] at hi
        by_contra hs
        have hs' : i ∉ L.supp := fun h => hs (Finset.mem_coe.2 h)
        apply hi
        simp [sg_eq_zero_of_not_mem_supp L u i hs', Formalism.BasicNotions.DV.ur]

theorem shift_nuOf (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L =
      NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) :
    NuC = shiftLat (nuOf L u e) (sgRec L u) := by
  have finj : Function.Injective
      ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) :=
    fun x y h => e.injective h
  apply Submodule.map_injective_of_injective finj
  rw [← hlat, hN u]
  unfold shiftLat Formalism.HermitianLatticesTheory.idealSmul nuOf
  rw [Submodule.map_span, shiftIdeal_shiftZ_sgRec_eq_Iu]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    refine ⟨a • e.symm y, ⟨a, ?_, e.symm y, ?_, rfl⟩, ?_⟩
    · simpa using ha
    · show e (e.symm y) ∈ L.NuLat u
      simpa using hy
    · show e (a • e.symm y) = a • y
      simp
  · rintro ⟨z', ⟨a, ha, x, hx, rfl⟩, rfl⟩
    refine ⟨a, ?_, e x, hx, ?_⟩
    · simpa using ha
    · show e (a • x) = a • e x
      exact map_smul e a x

theorem sgRec_fin (L : SizeData₂ D) (u : D.what₂.Word) : (Function.support (shiftZ (sgRec L u))).Finite := by
  refine (L.supp.finite_toSet.image D.plEq).subset ?_
  intro w hw
  rw [Function.mem_support] at hw
  refine ⟨D.plEq.symm w, ?_, D.plEq.apply_symm_apply w⟩
  by_contra hs
  have hs' : D.plEq.symm w ∉ L.supp := fun h => hs (Finset.mem_coe.2 h)
  apply hw
  simp [shiftZ, sgRec, sg_eq_zero_of_not_mem_supp L u _ hs', Formalism.BasicNotions.DV.ur]

end Formalism.L2.DIV.Cons

end
end

section

open Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

theorem rdTie (L : SizeData₂ D) (Del h0 : ℕ) : (ofRecord D L Del h0).rd = D.host.rdE := ofRecord_rd D L Del h0

theorem mainTie (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    (ofRecord D L Del h0).mainT (D.mem u).A.T = L.MAIN u := by
  simp only [NumDatum.mainT, SizeData₂.MAIN]
  rw [← Finset.sum_coe_sort D.host.TT]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ofRecord_aT, ofRecord_logOm]
  first
  | rfl
  | (unfold Formalism.LatticeIndexTer.ph phF; ring)

theorem numRecTie_record (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    NumRecTie (ofRecord D L Del h0) L u ((D.mem u).A.T) L.Nc :=
  numRecTie_ofRecord L Del h0 u (rdTie L Del h0) (mainTie L Del h0 u)

end Formalism.L2.DIV.Cons

end
end
