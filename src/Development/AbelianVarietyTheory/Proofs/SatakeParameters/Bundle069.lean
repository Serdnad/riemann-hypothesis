module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem signs_alternate_inert : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 →
    Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧
      Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  intro e ε τ φ hφ
  have hsnd : ∀ k : ℕ, (τ * φ ^ k).1.2 = τ.1.2 * (-1) ^ k := by
    intro k; simp [Prod.snd_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_snd, hφ]
  have hn : 0 < orderOf φ := orderOf_pos φ
  have h1 : ((-1 : ℤˣ)) ^ orderOf φ = 1 := by
    have h : (φ ^ orderOf φ).1.2 = 1 := by rw [pow_orderOf_eq_one]; rfl
    rwa [Prod.pow_fst, Prod.pow_snd, hφ] at h
  haveI : NeZero (orderOf φ) := ⟨hn.ne'⟩
  have key : ∀ i : ZMod (orderOf φ), (letter τ φ (i + 1)).1.2 = -(letter τ φ i).1.2 := by
    intro i
    unfold letter
    rw [hsnd, hsnd, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have hm : ((-1 : ℤˣ)) ^ ((i.val + 1) % orderOf φ) = (-1) ^ (i.val + 1) := by
      conv_rhs => rw [← Nat.mod_add_div (i.val + 1) (orderOf φ), pow_add, pow_mul, h1, one_pow, mul_one]
    rw [hm, pow_succ]
    simp
  have hA : Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) := by
    intro i
    simp only [pos]
    rw [key i]
    rcases Int.units_eq_one_or (letter τ φ i).1.2 with h | h <;>
      rcases Int.units_eq_one_or ε with h' | h' <;> simp [h, h'] <;> decide
  refine ⟨hA, fun i => ?_⟩
  have h := hA i
  simp only at h ⊢
  rw [h]

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem size_not_thick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  intro D L C g j hR hnt
  obtain ⟨-, hw100, hwη, hwb, hbT, -⟩ := hR
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρe : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  have hfl : (⌊(hcAt D g).e j⌋ : ℝ) = wj D (j.1 + 1) ρ := by
    rw [hw]
    show (⌊(D.hc ρ).e j⌋ : ℝ) = (((D.hc ρ).e j : ℚ) : ℝ)
    rw [hz, Int.floor_intCast]; push_cast; rfl
  rw [hfl]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb' : 0 < L.sc.b' := by linarith
  have hq : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hnt' : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρe]; exact hnt
  by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht'⟩
    have a4 := hbT ⟨t, ht'⟩
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := L.win_thin _ (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hnt'⟩
    constructor <;> linarith

end GlobalTheory.HTW
end

section

noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool)

def twistedJump (y : ℤ) : ℤ :=
  if s then -(⌊P.e j⌋ + y + ((R.t : ℤ) + 1) / 2) else ⌊P.e j⌋ + y - ((R.t : ℤ) + 1) / 2

theorem twistedDualJumps_eq_hodgeTateJump_images : jT2 P j s =
    (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => twistedJump P j s ⌊P.v i⌋) +
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
  obtain ⟨q, hq⟩ := R.t_odd
  cases s <;>
    simp only [jT2, jW, cloud, lows, twistedJump, Multiset.map_add (f := _), Multiset.map_map,
      Function.comp_def, ↓reduceIte, Bool.false_eq_true] <;>
    congr 1 <;>
    refine Multiset.map_congr rfl fun i _ => ?_ <;>
    omega

theorem twistedJump_low_small (η : ℝ) (h : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) (i : Fin R.m) :
    |twistedJump P j s (-⌊P.b i⌋)| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  obtain ⟨zb, hzb⟩ := P.b_int i
  obtain ⟨ze, hze⟩ := P.e_int j
  obtain ⟨q, hq⟩ := R.t_odd
  have hb : ⌊P.b i⌋ = zb := by rw [hzb]; exact Int.floor_intCast zb
  have he : ⌊P.e j⌋ = ze := by rw [hze]; exact Int.floor_intCast ze
  have hr : (((zb - ze : ℤ) : ℝ)) = (((P.b i - P.e j : ℚ) : ℝ)) := by
    rw [hzb, hze]; push_cast; ring
  have hn : (zb - ze).natAbs ≤ ⌊η⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs, hr]
    exact h i
  have habs : |zb - ze| ≤ (⌊η⌋₊ : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  rw [abs_le] at habs ⊢
  unfold twistedJump
  rw [hb, he]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> constructor <;> omega

theorem twistedJump_cloud_large (n : ℕ) (hv : ∀ i, 0 ≤ P.v i) (h : (n : ℤ) < szT P j s)
    (i : Fin (R.k - 1)) : ¬ |twistedJump P j s ⌊P.v i⌋| ≤ (n : ℤ) := by
  obtain ⟨q, hq⟩ := R.t_odd
  have hV : 0 ≤ ⌊P.v i⌋ := Int.floor_nonneg.mpr (hv i)
  unfold twistedJump
  unfold szT at h
  rw [abs_le]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

end Count

theorem card_small_twistedDualJumps_eq_rank {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ)
    (hv : ∀ i, 0 ≤ P.v i) (hb : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η)
    (hs : ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s) :
    ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  rw [twistedDualJumps_eq_hodgeTateJump_images, Multiset.filter_add, Multiset.card_add]
  have hc : ((Finset.univ : Finset (Fin (R.k - 1))).val.map
      (fun i => twistedJump P j s ⌊P.v i⌋)).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_cloud_large P j s _ hv hs i
  have hl : ((Finset.univ : Finset (Fin R.m)).val.map
      (fun i => twistedJump P j s (-⌊P.b i⌋))).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) =
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
    rw [Multiset.filter_eq_self]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_low_small P j s η hb i
  rw [hc, hl]
  simp

end GlobalTheory.HTW
end
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem winClusters_exists_step {n : ℕ} (th : ZMod n → Prop) (j : ℕ) (x : ZMod n) :
    ∃ s : ℕ, s ≤ j ∧ (s = 0 → ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x + q)) ∧ (0 < s → th (x + s)) ∧
      ∀ q : ℕ, 0 < q → q < s → ¬ th (x + q) := by
  classical
  by_cases h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩
    intro q hq hqs hth
    exact Nat.find_min h hqs ⟨hq, by omega, hth⟩
  · push_neg at h
    refine ⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0),
      fun q hq hq0 => absurd hq0 (by omega)⟩

theorem winClusters : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n →
    WindowTwo th L → Clusters th j := by
  intro n th L j _ hL hn hW
  choose sp hsp using winClusters_exists_step th j
  set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef
  have key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j →
      x1 + s1 = x2 + s2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 s1 s2 hs hs2 he
    rcases Nat.lt_or_ge s1 s2 with hlt | hge
    · exfalso
      apply hx1.2 (s2 - s1) (by omega) (by omega)
      have : x1 - ((s2 - s1 : ℕ) : ZMod n) = x2 := by
        rw [Nat.cast_sub hs]
        linear_combination he
      rw [this]; exact hx2.1
    · have : s1 = s2 := le_antisymm hs hge
      subst this
      exact add_right_cancel he
  have ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s := by
    intro x y h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simp [h]⟩
    · exact ⟨sp x, (hsp x).1, h⟩
  refine ⟨F, sp, ?_, ?_⟩
  · rintro x ⟨hx, hxF⟩
    obtain ⟨h1, _, h3, h4⟩ := hsp x
    refine ⟨hx, h1, by omega, ?_, h4, hxF⟩
    rcases Nat.eq_zero_or_pos (sp x) with h | h
    · rw [h]; simpa using hx
    · exact h3 h
  · intro y hy
    have ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n)) := by
      by_cases hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)
      · exact ⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩
      · push_neg at hyF
        obtain ⟨q, hq1, hqj, hq⟩ := hyF
        have hxF : y - (q : ZMod n) ∈ F := by
          refine ⟨hq, ?_⟩
          intro q' hq'1 hq'j hth
          apply hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)
          refine ⟨by simpa using hth, ?_, ?_⟩
          · have : y - (q : ZMod n) - q' + (q' : ℕ) = y - q := by ring
            rw [this]; exact hq
          · have : y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y := by push_cast; ring
            rw [this]; exact hy
        have hyx : y - (q : ZMod n) + (q : ZMod n) = y := by ring
        obtain ⟨h1, h2, h3, h4⟩ := hsp (y - q)
        have hspq : sp (y - q) = q := by
          rcases Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos
          · exact absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)
          rcases lt_trichotomy (sp (y - q)) q with hlt | heq | hgt
          · exfalso
            apply hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)
            refine ⟨by simpa using hq, h3 hpos, ?_⟩
            rw [hyx]; exact hy
          · exact heq
          · exact absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)
        refine ⟨y - q, hxF, Or.inr ?_⟩
        rw [hspq, hyx]
    obtain ⟨x, hxF, hx⟩ := ex
    refine ⟨x, ⟨hxF, hx⟩, ?_⟩
    rintro z ⟨hzF, hz⟩
    obtain ⟨s1, hs1, e1⟩ := ofCl z y hz
    obtain ⟨s2, hs2, e2⟩ := ofCl x y hx
    rcases le_total s1 s2 with h | h
    · exact key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)
    · exact (key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem _root_.GlobalTheory.noThree_of_windowTwo : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ),
    3 ≤ L → _root_.GlobalTheory.HTW.WindowTwo th L →
    _root_.GlobalTheory.HTW.NoThree th ∧ ∃ i, ¬ th i := by
  intro n th L hL hw
  have key : ∀ i, ¬(th i ∧ th (i + 1) ∧ th (i + 2)) := by
    intro i h
    have := hw i 0 1 2 (by norm_num) (by norm_num) (by omega)
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at this
    exact this h
  refine ⟨key, ?_⟩
  by_contra hall
  push_neg at hall
  exact key 0 ⟨hall _, hall _, hall _⟩

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem noThree_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  intro n th hn hone
  have h10 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1)) := by
    rintro i ⟨ha, hb⟩
    exact h10 (by linear_combination (hone _ _ ha hb).symm)
  refine ⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩
  by_cases h0 : th 0
  · exact ⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.SizeThick

theorem size_thick {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hT : Thick D.host g) :
    L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hmem : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces := by
    rw [hρ, Equiv.apply_symm_apply]; exact hT
  have h := L.win_thick (j.1 + 1) (by omega) j.2 ρ hmem
  rw [hw] at h
  have hc : hcAt D g = D.hc ρ := rfl
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  rw [hc, hz, Int.floor_intCast]
  rw [hz] at h
  push_cast at h ⊢
  exact h

end GlobalTheory.HTW.SizeThick
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem depth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l →
    LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧
      ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  intro D L P l hl
  obtain ⟨j, hj, hjL⟩ := P.Lw_j l hl
  have hne : ({j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} : Set ℕ).Nonempty := ⟨j, hj⟩
  have hmem : LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l := Nat.sInf_mem hne
  have hle : depth L l ≤ j := Nat.sInf_le hj
  refine ⟨hmem, by omega, fun hlt => ?_⟩
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  by_contra hc
  push_neg at hc
  interval_cases h : depth L l
  · simp at hmem
    linarith
  · simp at hmem
    linarith

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.ConjWord

theorem cc_comm {fr : Formalism.HC.Frame} (g : fr.GG) : g * fr.cc = fr.cc * g := mul_comm _ _

theorem plc_cc_mul {fr : Formalism.HC.Frame} (g : fr.GG) : plc (fr.cc * g) = plc g := UpperTheory.KStar.Words.placeOf_cc_mul g

theorem conj_word_one_place {fr : Formalism.HC.Frame} (τ : fr.GG) :
    orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  refine ⟨fr.orderOf_cc, fun i => ?_⟩
  unfold letter
  generalize i.val = k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ fr.cc k, ← mul_assoc, cc_comm, plc_cc_mul, ih]

end GlobalTheory.HTW.ConjWord
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem short_orbit_one_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG),
    orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) →
      Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  intro R H τ φ hord a b ha hb
  have key : ∀ g : R.GG, Thick H g → ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    intro g hg
    unfold Thick Host.thickPlaces at hg
    simpa [Finset.mem_image] using hg
  exact UpperTheory.KStar.Words.thick_one_place H.T2 H.second_set_range H.u0 τ φ
    ((Nat.le_of_dvd (orderOf_pos _) (R.toFrame.orderOf_hH_dvd φ.2)).trans hord) a.val b.val (key _ ha) (key _ hb)

end GlobalTheory.HTW
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsTame χ → IsParahoricVec χ π v → IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  first | exact @GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | exact GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | (intros; apply GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec <;> assumption)
end

end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.atMostOneThick_short_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) → Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  first | exact @GlobalTheory.HTW.short_orbit_one_thick | exact GlobalTheory.HTW.short_orbit_one_thick | (intros; apply GlobalTheory.HTW.short_orbit_one_thick <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.card_filter_abs_le_jT2_eq_rank : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ), (∀ i, 0 ≤ P.v i) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s → ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  first | exact @GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | exact GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | (intros; apply GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.complexConjugation_orbit_one_realPlace : ∀ {fr : Formalism.HC.Frame} (τ : fr.GG), orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  first | exact @GlobalTheory.HTW.ConjWord.conj_word_one_place | exact GlobalTheory.HTW.ConjWord.conj_word_one_place | (intros; apply GlobalTheory.HTW.ConjWord.conj_word_one_place <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n → WindowTwo th L → Clusters th j := by
  first | exact @GlobalTheory.HTW.winClusters | exact GlobalTheory.HTW.winClusters | (intros; apply GlobalTheory.HTW.winClusters <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_atMostOne | exact GlobalTheory.noThree_of_atMostOne | (intros; apply GlobalTheory.noThree_of_atMostOne <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ), 3 ≤ L → WindowTwo th L → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_windowTwo | exact GlobalTheory.noThree_of_windowTwo | (intros; apply GlobalTheory.noThree_of_windowTwo <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.embeddingSign_alternate_of_sign_neg : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 → Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧ Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  first | exact @GlobalTheory.signs_alternate_inert | exact GlobalTheory.signs_alternate_inert | (intros; apply GlobalTheory.signs_alternate_inert <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.floor_size_bounds_at_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m), Thick D.host g → L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  first | exact @GlobalTheory.HTW.SizeThick.size_thick | exact GlobalTheory.HTW.SizeThick.size_thick | (intros; apply GlobalTheory.HTW.SizeThick.size_thick <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.floor_size_bounds_not_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.size_not_thick | exact GlobalTheory.HTW.size_not_thick | (intros; apply GlobalTheory.HTW.size_not_thick <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.jumps_mem_box_neg_M_h : ∀ {n : ℕ} (W : WordData n), (∀ i, 0 ≤ W.sz i) → W.T1 → ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  first | exact @GlobalTheory.HTW.WordData.jumps_mem_box | exact GlobalTheory.HTW.WordData.jumps_mem_box | (intros; apply GlobalTheory.HTW.WordData.jumps_mem_box <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.leastPowerDepth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l → LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧ ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  first | exact @GlobalTheory.depth_spec | exact GlobalTheory.depth_spec | (intros; apply GlobalTheory.depth_spec <;> assumption)

end
end
