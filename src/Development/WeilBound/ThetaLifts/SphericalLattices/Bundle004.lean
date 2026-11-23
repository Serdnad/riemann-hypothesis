module

public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006

@[expose] public section

section

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
open scoped Pointwise

section Asm

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem asm_ordL_eq (x : L) : ordL x = -WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)) := by
  unfold ordL
  split_ifs with h
  · rw [h]; simp
  · congr 1
    conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem asm_ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  rw [asm_ordL_eq, asm_ordL_eq, asm_ordL_eq, map_mul, WithZero.log_mul hx' hy']
  ring

theorem asm_ordL_pow (x : L) (n : ℕ) : ordL (x ^ n) = n * ordL x := by
  rw [asm_ordL_eq, asm_ordL_eq, map_pow, WithZero.log_pow]
  simp

theorem asm_ordL_unit {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) (h : x * y = 1) : ordL x = 0 := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≤ 1 := hy
  have h1 : (Valued.v x : WithZero (Multiplicative ℤ)) * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have h2 : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
    refine le_antisymm hx' ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
      _ ≤ Valued.v x * 1 := mul_le_mul_right hy' _
      _ = _ := mul_one _
  rw [asm_ordL_eq, h2]; simp

variable {c : L →+* L} {m : ℕ}

def asmT (p : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m) (Fin m) L :=
  (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁

theorem asm_low {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 :=
  GlobalTheory.LGrp.mem_blockQ_two.1 hp.2

theorem asmT_mul (a : GL (Fin m ⊕ Fin m) L) {b : GL (Fin m ⊕ Fin m) L} (hb : b ∈ PW L c m) :
    asmT (a * b) = asmT a * asmT b := by
  unfold asmT
  rw [Units.val_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L),
    ← fromBlocks_toBlocks (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L), fromBlocks_multiply, toBlocks_fromBlocks₁₁,
    asm_low hb, Matrix.mul_zero, add_zero]

theorem asmT_one : asmT (1 : GL (Fin m ⊕ Fin m) L) = 1 := by
  unfold asmT
  rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem asmT_det_mul_inv {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (asmT p).det * (asmT p⁻¹).det = 1 := by
  rw [← det_mul, ← asmT_mul p (inv_mem hp), mul_inv_cancel, asmT_one, det_one]

theorem asmT_det_ne {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) : (asmT p).det ≠ 0 :=
  left_ne_zero_of_mul_eq_one (asmT_det_mul_inv hp)

theorem asmT_det_int {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ IntGL L m) : (asmT k).det ∈ intL L := by
  obtain ⟨g, rfl⟩ := hk
  have e : asmT (Matrix.GeneralLinearGroup.map (intL L).subtype g) =
      (intL L).subtype.mapMatrix (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L)).toBlocks₁₁ := by
    ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact Subtype.property _

theorem asm_ord_K {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ KPW L c m) : ordL (asmT k).det = 0 :=
  asm_ordL_unit (asmT_det_int hk.2.2) (asmT_det_int (inv_mem hk.2.2)) (asmT_det_mul_inv hk.1)

theorem asm_ord_mul {a b : GL (Fin m ⊕ Fin m) L} (ha : a ∈ PW L c m) (hb : b ∈ PW L c m) :
    ordL (asmT (a * b)).det = ordL (asmT a).det + ordL (asmT b).det := by
  rw [asmT_mul a hb, det_mul, asm_ordL_mul (asmT_det_ne ha) (asmT_det_ne hb)]

theorem ord_det_uniformizer_image_eq {ϖ : L} {q : ℕ} (h : IsUnramInv ϖ c q) (x : Lˣ) (hx : (x : L) = ϖ) :
    ordL (asmT (zW L m x)).det = m := by
  have e : asmT (zW L m x) = (x : L) • (1 : Matrix (Fin m) (Fin m) L) := toBlocks_fromBlocks₁₁ _ _ _ _
  have o : ordL ϖ = 1 := by
    rw [asm_ordL_eq, h.2.2.2.1]
    rfl
  rw [e, det_smul, det_one, mul_one, Fintype.card_fin, asm_ordL_pow, hx, o, mul_one]

end Asm

theorem asm_smul {G : Type} [Group G] (K : Subgroup G) (p : G) :
    MulAut.conj p • K = K.map (MulAut.conj p).toMonoidHom := rfl

theorem asm_relIndex {G : Type} [Group G] (K : Subgroup G) (p : G) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) = (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p⁻¹).toMonoidHom) K
    (K.map (MulAut.conj p).toMonoidHom) (MulAut.conj p⁻¹).injective
  have e : (K.map (MulAut.conj p).toMonoidHom).map (MulAut.conj p⁻¹).toMonoidHom = K := by
    rw [← asm_smul, ← asm_smul, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [e] at h
  exact h.symm

theorem asm_conj_self {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) : MulAut.conj k • K = K :=
  Subgroup.conj_smul_eq_self_of_mem hk

theorem locMod_of (h1 : LocCommSt) (h2 : ZCountSt) (h3 : GenSt) : LocModSt := by
  intro L _ _ ϖ c q hU m p hp
  have hq : (0 : ℝ) < q := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < q)
  obtain ⟨hmul, hpos, -, -⟩ := GlobalTheory.T.haarInvVolume_conj_modular_character (PW L c m) (KPW L c m) inf_le_left
    (fun h hh => ⟨(h1 L ϖ c q hU m h hh).2, (h1 L ϖ c q hU m h hh).1⟩)
  have key := h3 L ϖ c q hU m
    (fun a => GlobalTheory.HL.invVol (KPW L c m) (MulAut.conj a • KPW L c m) *
      (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (asmT a).det)))
    (fun a ha b hb => by
      rw [hmul a ha b hb, asm_ord_mul ha hb, mul_add, neg_add, zpow_add₀ hq.ne']
      ring)
    (fun a ha => mul_pos (hpos a ha) (zpow_pos hq _))
    (fun k hk => by
      rw [asm_conj_self _ hk, asm_ord_K hk, GlobalTheory.HL.invVol, Subgroup.relIndex_self]
      simp)
    (fun x hx => by
      obtain ⟨hle, hi⟩ := h2 L ϖ c q hU m x hx
      rw [ord_det_uniformizer_image_eq hU x hx, asm_smul, GlobalTheory.HL.invVol, hi, Subgroup.relIndex_eq_one.2 hle, Nat.cast_one, div_one,
        Nat.cast_pow, ← zpow_natCast, ← zpow_add₀ hq.ne']
      push_cast
      rw [add_neg_cancel, zpow_zero])
    p hp
  have hb := (h1 L ϖ c q hU m p hp).2
  rw [asm_relIndex] at hb
  have hb' : ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hb
  simp only [asm_smul, GlobalTheory.HL.invVol, asm_relIndex] at key
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hb'] at key
  rw [← key, mul_comm]
  rfl

end PositivityTheory.Sph.M2

end
end

section

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace GenC

open GenA GenB

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem lev_sc_val (u : Lˣ) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
      fromBlocks ((u : L) • 1) 0 0 (c ((u⁻¹ : Lˣ) : L) • 1) := by
  rw [lev_val, levM, ← map_inv, dg_val, dg_val]
  congr 1
  · ext i j; by_cases h : i = j <;> simp [h]
  · ext i j
    by_cases h : i = j
    · simp [h]
    · simp [h]

theorem lev_sc_int (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ} (hu : Valued.v (u : L) = 1) (i j) :
    ((lev L c m (dg fun _ => u) : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L := by
  have h1 : (u : L) ∈ intL L := hu.le
  have h2 : c ((u⁻¹ : Lˣ) : L) ∈ intL L := by
    show Valued.v (c _) ≤ 1
    rw [hv, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  rw [lev_sc_val]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h1
    · rw [mul_zero]; exact zero_mem _
  · exact zero_mem _
  · exact zero_mem _
  · rw [fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact h2
    · rw [mul_zero]; exact zero_mem _

theorem lev_sc_mem (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {u : Lˣ}
    (hu : Valued.v (u : L) = 1) : lev L c m (dg fun _ => u) ∈ KPW L c m := by
  refine ⟨lev_mem hc _, (lev_mem hc _).1, mem_IntGL (lev_sc_int hv hu) ?_⟩
  rw [← map_inv, ← map_inv]
  exact lev_sc_int (u := u⁻¹) hv (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem lev_sc_eq {x : Lˣ} (hx : c x = x) : lev L c m (dg fun _ => x) = zW L m x := by
  ext1
  rw [lev_sc_val, zW_val, Units.val_inv_eq_inv_val, map_inv₀, hx]

theorem exists_unit {x : Lˣ} (hx : Valued.v (x : L) = WithZero.exp (-1 : ℤ)) (u : Lˣ) :
    ∃ k : ℤ, Valued.v ((u * x ^ k : Lˣ) : L) = 1 := by
  have h0 : Valued.v (u : L) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  refine ⟨WithZero.log (Valued.v (u : L)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, ← WithZero.exp_zsmul]
  conv_lhs => lhs; rw [← WithZero.exp_log h0]
  rw [← WithZero.exp_add]
  simp

theorem one_add_ne {y : L} (hy : Valued.v y < 1) : 1 + y ≠ 0 := fun e => by
  rw [eq_neg_of_add_eq_zero_right e, Valuation.map_neg, map_one] at hy
  exact lt_irrefl _ hy

end GenC

open GenA GenB GenC in
theorem gen : GenSt := by
  intro L _ _ ϖ c q h m χ hmul hpos hK hz a ha
  obtain ⟨hc, hv, hϖ, hvϖ, -⟩ := h
  have hvϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hvϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hvϖ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hvϖ'; exact WithZero.exp_ne_zero hvϖ'.symm
  let x : Lˣ := Units.mk0 ϖ h0
  have hzx : χ (zW L m x) = 1 := hz x rfl
  have hzm : zW L m x ∈ PW L c m := by rw [← lev_sc_eq (c := c) (x := x) hϖ]; exact lev_mem hc _
  let ψ : GL (Fin m) L →* ℝ :=
    { toFun := fun t => χ (lev L c m t)
      map_one' := by rw [map_one]; exact hK 1 (one_mem _)
      map_mul' := fun s t => by rw [map_mul]; exact hmul _ (lev_mem hc _) _ (lev_mem hc _) }
  have hψ : ∀ t, ψ t = χ (lev L c m t) := fun _ => rfl
  have hsc : ∀ u : Lˣ, ψ (dg fun _ => u) = 1 := by
    let φ : Lˣ →* ℝ := (ψ.comp dg).comp (Pi.constMonoidHom (Fin m) Lˣ)
    have hφ : ∀ u, φ u = ψ (dg fun _ => u) := fun _ => rfl
    intro u
    obtain ⟨k, hk⟩ := exists_unit (x := x) hvϖ' u
    have e1 : φ (u * x ^ k) = 1 := by rw [hφ, hψ]; exact hK _ (lev_sc_mem hc hv hk)
    have e2 : φ x = 1 := by rw [hφ, hψ, lev_sc_eq (x := x) hϖ]; exact hzx
    have e3 : φ (x ^ k) = 1 := zpow_mem (show x ∈ φ.ker from e2) k
    rw [map_mul, e3, mul_one] at e1
    exact e1
  have hall := all_one ψ (fun t => hpos _ (lev_mem hc t)) h0 (one_add_ne hlt) hsc
  obtain ⟨t, X, hX, rfl⟩ := decomp hc ha
  have hr : 1 + -(ϖ * ϖ) ≠ 0 := one_add_ne (by
    rw [Valuation.map_neg, map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le)
  have hs : ∀ r : L, c r = r → (r • X).map c = -(r • X)ᵀ := fun r hr => by
    ext i j
    have : c (X i j) = -X j i := congrFun (congrFun hX i) j
    simp [hr, this]
  set r := (1 + -(ϖ * ϖ))⁻¹ with hrd
  have hcr : c r = r := by simp [hrd, hϖ]
  have m1 := un_mem (hs r hcr)
  have m2 := un_mem (hs (ϖ * ϖ * r) (by simp [hcr, hϖ]))
  have m3 := un_mem hX
  have e1 := congrArg χ (zW_un x (r • X))
  rw [smul_smul] at e1
  have e2 : un (r • X) = un ((ϖ * ϖ * r) • X) * un X := by
    rw [un_mul]
    congr 1
    have : r = ϖ * ϖ * r + 1 := by
      have := mul_inv_cancel₀ hr
      rw [← hrd] at this
      linear_combination this
    conv_lhs => rw [this, add_smul, one_smul]
  have e3 : χ (un (r • X)) = χ (un ((ϖ * ϖ * r) • X)) := by
    rw [hmul _ hzm _ m1, hzx, one_mul] at e1
    rw [e1]
    exact (hmul _ m2 _ hzm).trans (by rw [hzx, mul_one])
  rw [e2, hmul _ m2 _ m3] at e3
  have e4 : χ (un X) = 1 := mul_left_cancel₀ (hpos _ m2).ne' (e3.trans (mul_one _).symm)
  rw [hmul _ (lev_mem hc t) _ m3, e4, mul_one]
  exact hall t

end PositivityTheory.Sph.M2

end
end
