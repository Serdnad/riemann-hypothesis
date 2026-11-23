module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
public import GroundTheory.AutomorphicForms.MacdonaldFormula
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LocalAlgebraPowers

theorem pad_self {k : ℕ} (l : Fin k → ℤ) : pad k l = l := by
  funext a
  simp [pad, a.2]

theorem rhoPair_pad {m k : ℕ} (hkm : k ≤ m) (l : Fin k → ℤ) :
    rhoPair (pad m l) = rhoPair l + ((m : ℤ) - k) * ∑ i, l i := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  simp only [rhoPair, pad, Fin.sum_univ_add, Fin.coe_castAdd, Fin.coe_natAdd, Fin.is_lt, dif_pos]
  simp only [show ∀ j : Fin d, ¬ (k + (j : ℕ) < k) from fun j => by omega, dif_neg, not_false_eq_true,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem antitone_pad {m k : ℕ} (hkm : k < m) (l : Fin k → ℤ) :
    Antitone (pad m l) ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨j, by omega⟩ from hij)
      simpa [pad, i.isLt, j.isLt] using this
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.mpr i.isLt.le)
      simpa [pad, i.isLt] using this
  · rintro ⟨hl, h0⟩ a b hab
    have hab' : (a : ℕ) ≤ b := hab
    by_cases hb : (b : ℕ) < k
    · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
      simp only [pad, ha, hb, dif_pos]
      exact hl (Fin.mk_le_mk.mpr hab')
    · simp only [pad, hb, dif_neg, not_false_eq_true]
      split_ifs
      · exact h0 _
      · exact le_rfl

theorem antitone_pad_iff {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (l : Fin k → ℤ) (hl : Antitone l)
    (h : k < m ∨ ∀ i : Fin k, (i : ℕ) + 1 = k → 0 ≤ l i) : Antitone (pad m l) ↔ ∀ i, 0 ≤ l i := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · rw [antitone_pad hlt l]
    simp [hl]
  · subst heq
    have h' := h.resolve_left (lt_irrefl _)
    have hall : ∀ i, 0 ≤ l i := by
      intro i
      have hlast : 0 ≤ l ⟨k - 1, by omega⟩ := h' _ (by simp; omega)
      exact le_trans hlast (hl (Fin.mk_le_mk.mpr (by omega)))
    rw [pad_self]
    exact ⟨fun _ => hall, fun _ => hl⟩

variable {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)}

theorem nq_pos (w : Off E S) : 0 < nq w := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [nq, Ideal.absNorm_eq_zero_iff] at h
  exact w.1.ne_bot h

theorem qF_eq' (w : Off E S) : qF (w.1.adicCompletion E) = nq w := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.qF_eq w.1

theorem sqrtQ_eq (w : Off E S) :
    sqrtQ (w.1.adicCompletion E) = Complex.exp ((Real.log (nq w) / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [sqrtQ, qF_eq', ← Complex.ofReal_exp]
  norm_cast
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  congr 1
  ring

theorem conj_sqrtQ_zpow (w : Off E S) (j : ℤ) :
    conj (sqrtQ (w.1.adicCompletion E) ^ j) = sqrtQ (w.1.adicCompletion E) ^ j := by
  rw [map_zpow₀]
  congr 1
  simp [sqrtQ, Complex.conj_ofReal]

theorem cast_eq_exp (w : Off E S) : (nq w : ℂ) = Complex.exp (Real.log (nq w)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hpos]

theorem cpow_eq (w : Off E S) (z : ℂ) : (nq w : ℂ) ^ z = Complex.exp (Real.log (nq w) * z) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nq_pos w).ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hpos.le]

theorem zpow_eq (w : Off E S) (j : ℤ) : (nq w : ℂ) ^ j = Complex.exp (j * Real.log (nq w)) := by
  rw [cast_eq_exp, ← Complex.exp_int_mul]

theorem sqrt_zpow_eq (w : Off E S) (j : ℤ) :
    sqrtQ (w.1.adicCompletion E) ^ j = Complex.exp (j * (Real.log (nq w) / 2 : ℝ)) := by
  rw [sqrtQ_eq, ← Complex.exp_int_mul]

theorem rpow_cpow_eq (w : Off E S) (N : ℤ) (z : ℂ) :
    ((((nq w : ℝ) ^ N : ℝ)) : ℂ) ^ z = Complex.exp ((N * Real.log (nq w) : ℝ) * z) := by
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  have hx : (0 : ℝ) < (nq w : ℝ) ^ N := zpow_pos hq N
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow]

theorem local_inputs_from_literature {m k : ℕ} (q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) (l : Fin k → ℤ) :
    loc q α β s l = loc q α β 0 l * (q : ℂ) ^ (-s * ((∑ i, l i : ℤ) : ℂ)) := by
  unfold loc
  split_ifs <;> simp

end LocalAlgebraPowers

open LocalAlgebraPowers in
theorem localHeckeAlgebra_statement : LocalHeckeAlgebra := by
  intro E _ _ S m k α α' w χ hχ hk hkm
  have hψ := hχ.1
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  refine ⟨?_, fun l => ⟨fun s => ?_, fun hcase => ?_, fun hneg => ?_⟩⟩
  · have hp : pad m (0 : Fin k → ℤ) = 0 := by
      funext a
      simp [pad]
    have hA : Antitone (0 : Fin k → ℤ) ∧ ∀ i, 0 ≤ (0 : Fin k → ℤ) i :=
      ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
    simp only [aLoc, loc, if_pos hA, hp, halfModulus_zero, schur_zero, map_one, Pi.zero_apply,
      Finset.sum_const_zero, Int.cast_zero, mul_zero, neg_zero, Complex.cpow_zero, one_pow, mul_one]
    simp [hA.1]
  · have key : ∀ a b c d g : ℂ, a + 2 * b + c + d = g → ∀ L : ℂ,
        Complex.exp a * (Complex.exp b ^ 2 * Complex.exp c * L * Complex.exp d) = L * Complex.exp g := by
      intro a b c d g h L
      rw [← h, Complex.exp_add, Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      ring
    rw [local_inputs_from_literature]
    simp only [aLoc, halfModulus_eq]
    rw [rpow_cpow_eq, sqrt_zpow_eq, zpow_eq, cpow_eq, cpow_eq]
    refine key _ _ _ _ _ ?_ _
    push_cast
    ring
  · rw [sphericalWhittaker_torusPow hψ, sphericalWhittaker_torusPow hψ]
    by_cases hA : Antitone l ∧ ∀ i, 0 ≤ l i
    · have hpA : Antitone (pad m l) := (antitone_pad_iff hk hkm l hA.1 hcase).mpr hA.2
      have hfac : halfModulus (w.1.adicCompletion E) (pad m l) * conj (halfModulus (w.1.adicCompletion E) l) =
          halfModulus (w.1.adicCompletion E) l ^ 2 *
            (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ)) := by
        rw [halfModulus_eq, halfModulus_eq, rhoPair_pad hkm, conj_sqrtQ_zpow, sqrt_zpow_eq, sqrt_zpow_eq,
          cpow_eq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [if_pos hpA, if_pos hA.1]
      simp only [aLoc, loc, if_pos hA, neg_zero, zero_mul, Complex.cpow_zero, mul_one, map_mul]
      linear_combination ((evalAt (α w)) (schur (pad m l)) * conj ((evalAt (α' w)) (schur l))) * hfac
    · have hR : aLoc α α' w l = 0 := by
        simp only [aLoc, loc, if_neg hA, mul_zero]
      rw [hR]
      by_cases hl : Antitone l
      · have hpA : ¬ Antitone (pad m l) := fun h => hA ⟨hl, (antitone_pad_iff hk hkm l hl hcase).mp h⟩
        rw [if_neg hpA, zero_mul]
      · rw [if_neg hl, map_zero, mul_zero]
  · have hA : ¬ (Antitone l ∧ ∀ i, 0 ≤ l i) := by
      rintro ⟨-, h⟩
      obtain ⟨i, hi⟩ := hneg
      exact absurd (h i) (not_le.mpr hi)
    simp only [aLoc, loc, if_neg hA, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace UpperBlockProducts

theorem blk_corner {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {j : ℕ} {g : GL (Fin a) R}
    (hg : GlobalTheory j g) : GlobalTheory j (cornerGL a s g) := by
  intro i c hic
  change (1 : Matrix (Fin a) (Fin a) S) i c - s ((1 : Matrix (Fin a) (Fin a) R) i c) + s (g.val i c) = _
  rw [hg i c hic, sub_add_cancel]

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blk_fl (v : Pl E) {j : ℕ} {c : GL (Fin k) (v.adicCompletion E)} (hc : GlobalTheory j c) : GlobalTheory j (fl k v c) :=
  blk_corner (sFin E) (blk_corner (sLoc E v) hc)

theorem posM_blk_zero {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : (c : ℕ) ≤ i) :
    posM Subtype.val Y i c = 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  obtain ⟨t1, t2, t3⟩ := t.2
  rw [h1, h2] at *
  omega

theorem uu_blkU {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU Y : GA E k) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · change (1 + posM Subtype.val Y) i c = 0
    rw [Matrix.add_apply, posM_blk_zero Y i c (le_of_lt hci), Matrix.one_apply_ne hci.ne', add_zero]
  · change (1 + posM Subtype.val Y) i i = 1
    rw [Matrix.add_apply, posM_blk_zero Y i i le_rfl, Matrix.one_apply_eq, add_zero]

theorem uu_mul {u u' : GA E k} (hu : UU 0 u) (hu' : UU 0 u') : UU 0 (u * u') := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hu'.1 l c (lt_of_lt_of_le hci h), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hu.2.1, hu'.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hu.1 i l h, zero_mul]
      · rw [hu'.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end UpperBlockProducts

open UpperBlockProducts UnipotentCharacter in
theorem finite_place_of_jump_windows : jumpWindows.S2 → jumpWindows.S9 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → FinitePlaceStep := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m v hv hmv hm0 U hU x C hxY hsm hlev hB
  obtain ⟨-, -, i3, i4, i5, -, i7, i8, -, i10, -, -, -, i14, -⟩ := hG0 E k
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E k ψ hψ
  obtain ⟨-, b2, b3, b4, b5⟩ := hG5b E k S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (v.adicCompletion E) k (m v + 1)
  obtain ⟨p2law, p2norm, p2uu, p2whit, -, p2good, -⟩ := hP2 E k ψ hψ
  obtain ⟨s0, sadd, ssmul, -, sT, -⟩ := hS2 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly
  let U' : Set (GL (Fin k) (v.adicCompletion E)) := {u | repW k v u (J x) = J x} ∩ (fl k v) ⁻¹' U
  have hU' : U' ∈ 𝓝 (1 : GL (Fin k) (v.adicCompletion E)) :=
    Filter.inter_mem (hlev v hv) ((i14 v).continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU))
  have hne : ∃ y, chi ψ v y ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc v
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, hηr, ⟨Cl, hClc, hClU, hClB, hCl⟩, hmain⟩ :=
    hS9 (v.adicCompletion E) k (m v) hmv (chi ψ v) (chi_cont hψ v) hne (XB E k) (repW k v) U' hU'
  have hClU' : ∀ c ∈ Cl, fl k v c ∈ U := fun c hc => (hClU hc).2
  have inS : ∀ u, InS S (fl k v u : GA E k) := fun u w hw => i5 v w u (fun e => hw (e ▸ hv))
  have stab : ∀ u, ∀ z ∈ Y, repW k v u z ∈ Y := fun u z hz => hY.stable _ (inS u) z hz
  have hJx' : J (∑ t ∈ T, c t • ρ (fl k v t) x) = ∑ t ∈ T, c t • repW k v t (J x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hW.inter, repW_apply]
  have hJY : J (∑ t ∈ T, c t • ρ (fl k v t) x) ∈ Y := by
    rw [hJx']
    exact Y.sum_mem fun t _ => Y.smul_mem _ (stab t _ hxY)
  have hgood' : Good ψ (k - 1) (J (∑ t ∈ T, c t • ρ (fl k v t) x)) := hY.good _ hJY
  have key : ∀ g' : GA E k, cLoc v g' = 1 → ∀ h, GlobalTheory (m v + 1) h →
      Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (g' * fl k v h) = η h * Wh ψ (J x) (g' * fl k v (r h)) := by
    intro g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Y, ∀ y : UnipotentBlockColumnIndex k (m v + 1) (m v + 1) → v.adicCompletion E,
        (Λ : XB E k →ₗ[ℂ] ℂ) (repW k v (blkU y) z) = chi ψ v (lastE (m v + 1) y) * (Λ : XB E k →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hY.good _ (stab _ z hz)),
        hΛ _ (hY.good _ hz), repW_apply, g5r, i8 v g' hg', i10,
        (g5c z (hY.good _ hz)).2.2 (m v + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain (J x) (fun u hu => hu.1) Y stab hxY (Λ : XB E k →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    have hsum : ∑ t ∈ T, c t • repW k v t (J x) ∈ Y := by rw [← hJx']; exact hJY
    rw [hΛ _ (hY.good _ (stab _ _ hsum)), hΛ _ (hY.good _ (stab _ _ hxY)),
      repW_apply, repW_apply, g5r, g5r] at this
    rw [hJx']
    exact this
  have hpre : Pre ψ 0 (Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x))) :=
    p2whit (k - 1) (by omega) _ (p2good _ _ hgood')
  have hlawW : ∀ u, UU 0 u → ∀ z, Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (u * z) =
      psN ψ u * Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) z :=
    fun u hu z => p2law 0 _ hpre u (p2uu u hu) z
  have hpsN : ∀ u : GA E k, psN ψ u ≠ 0 := fun u e0 => by
    have h1 := p2norm u
    rw [e0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨∑ t ∈ T, c t • ρ (fl k v t) x, fl k v '' Cl, ?_, hJY, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact hClU' c₂ hc₂
  · refine sum_of _ s0 sadd ssmul T c _ fun t => sT (ρ (fl k v t)) (fun g z => ?_) x hsm
    simp only [MonoidHom.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, i7 _ (i3 v t) g, map_mul, ContinuousLinearMap.mul_apply]
  · rw [hJx']
    exact sum_of _ b5 b4 b3 T c _ fun t => by rw [repW_apply]; exact b2 _ _ hlev
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact blk_fl v (hClB c₂ hc₂)
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hCb⟩ := hB
  refine ⟨hCc.mul (hClc.image (i14 v)), ?_, ?_, ?_⟩
  · rintro _ ⟨c₁, hc₁, _, ⟨c₂, hc₂, rfl⟩, rfl⟩ w hw
    rw [map_mul, hCS c₁ hc₁ w hw, inS c₂ w hw, one_mul]
  · have h1 := key 1 (map_one _) 1 s10blk1
    rw [hr1] at h1
    simp only [map_one, mul_one] at h1
    obtain ⟨s₁, hs₁, hηs₁⟩ := hηr 1
    have hs₁' : 0 < s₁ := lt_of_le_of_ne hs₁ fun e0 => hη1 (by rw [hηs₁, ← e0, Complex.ofReal_zero])
    refine ⟨s₁ * t₀, mul_pos hs₁' ht₀, ?_⟩
    rw [h1, hηs₁, hW1]
    push_cast
    ring
  · intro g hg hg0
    obtain ⟨hgI, hgL⟩ := hg
    have hgv : Mir (m v + 1) (cLoc v g) := by simpa using hgL v
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgv
    set g' : GA E k := g * (fl k v (cLoc v g))⁻¹ with hg'def
    have hg' : cLoc v g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have e : g = blkU (fun t => sFin E (sLoc E v (y t))) * (g' * fl k v h) := by
      rw [← i10, ← mul_assoc, ← i8 v g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
    have hWg : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) g =
        ψ (lastE (m v + 1) fun t => sFin E (sLoc E v (y t))) * (η h * Wh ψ (J x) (g' * fl k v (r h))) := by
      rw [e, (g5c _ hgood').2.2 (m v + 1) (Nat.succ_pos _), key g' hg' h hh]
    have hηh : η h ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    have hW'' : Wh ψ (J x) (g' * fl k v (r h)) ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    obtain ⟨c₂, hc₂, hhc⟩ := hCl h hh hηh
    have hOm : Om n m (g' * fl k v (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
        exact hgI
      · rcases eq_or_ne w v with rfl | hwv
        · rw [map_mul, hg', i4, one_mul]
          exact hrMir h hh hηh
        · rw [map_mul, hg'def, map_mul, map_inv, i5 v w _ hwv, i5 v w _ hwv, inv_one, mul_one, mul_one]
          simpa [hwv] using hgL w
    obtain ⟨nn₀, c₁, hc₁, t₁, hnn₀, hnnS, hgeq₀, ht₁, hWv⟩ := hCb _ hOm hW''
    obtain ⟨sh, hsh, hηsh⟩ := hηr h
    have hYg : (blkU fun t => sFin E (sLoc E v (y t)) : GA E k) = fl k v (blkU y) := (i10 v _ y).symm
    have h2 : nn₀ * (c₁ * fl k v c₂) = g' * fl k v h := by
      rw [hhc, map_mul, ← mul_assoc g', hgeq₀, mul_assoc]
    have hcc : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (c₁ * fl k v c₂) = ((sh * t₁ : ℝ) : ℂ) := by
      have h1 := hlawW nn₀ hnn₀ (c₁ * fl k v c₂)
      rw [h2, key g' hg' h hh, hWv, hηsh] at h1
      apply mul_left_cancel₀ (hpsN nn₀)
      rw [← h1]
      push_cast
      ring
    have huu : UU 0 ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀ : GA E k) := uu_mul (uu_blkU _) hnn₀
    refine ⟨(blkU fun t => sFin E (sLoc E v (y t))) * nn₀, c₁ * fl k v c₂,
      Set.mem_image2_of_mem hc₁ ⟨c₂, hc₂, rfl⟩, sh * t₁, huu, ?_, ?_, mul_nonneg hsh ht₁, ?_⟩
    · intro w hw
      rw [map_mul, hYg, i5 v w _ (fun e0 => hw (e0 ▸ hv)), hnnS w hw, one_mul]
    · rw [mul_assoc, h2]
      exact e
    · have hg2 : g = ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀) * (c₁ * fl k v c₂) := by
        rw [mul_assoc, h2]
        exact e
      rw [hg2, hlawW _ huu, hcc]

end PositivityTheory.AdelicQuotientData

end
end
