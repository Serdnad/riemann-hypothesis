module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractRow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem mem_iw {g : GL (Fin n) E} : g ∈ iwahori E (Fin n) ↔
    ((∀ i j, valuation E (g.val i j) ≤ 1) ∧ ∀ i j, valuation E (g⁻¹.val i j) ≤ 1) ∧
      ∀ i j, j < i → valuation E (g.val i j) < 1 := by
  rw [mem_iwahori, GlobalTheory.SplitFlip.mem_KO_iff]
  rfl

private theorem diag_one {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) (i : Fin n) :
    valuation E (g.val i i) = 1 := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  have h4 := (mem_iw.1 (inv_mem hg)).2
  refine le_antisymm (h1 i i) (not_lt.1 fun h => ?_)
  have : valuation E (∑ l, g.val i l * g⁻¹.val l i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    rw [map_mul]
    rcases lt_trichotomy l i with hl | hl | hl
    · exact (mul_le_of_le_one_right' (h2 l i)).trans_lt (h3 i l hl)
    · subst hl
      exact (mul_le_of_le_one_right' (h2 l l)).trans_lt h
    · exact (mul_le_of_le_one_left' (h1 i l)).trans_lt (h4 l i hl)
  change valuation E ((g.val * g⁻¹.val) i i) < 1 at this
  rw [g.mul_inv] at this
  simp at this

private theorem sg_mem {σ : E ≃+* E} (hσ : Isom σ) {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) :
    sg σ g ∈ iwahori E (Fin n) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  rw [mem_iw, ← map_inv]
  exact ⟨⟨fun i j => (hσ _).le.trans (h1 i j), fun i j => (hσ _).le.trans (h2 i j)⟩,
    fun i j h => (hσ _).le.trans_lt (h3 i j h)⟩

end

theorem UpperTheory.ConvolutionTheory.Loc.contractI :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E), Isom σ → ∀ t : Fin n → Eˣ, Strict t → ∀ g ∈ iwahoriCoset t,
      ∃ k ∈ iwahori E (Fin n), ∃ s ∈ torusO E (Fin n), g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  rintro E _ _ _ _ n σ hσ t ht g ⟨a, ha, b, hb, rfl⟩
  have hb' : b * sg σ a ∈ iwahori E (Fin n) := mul_mem hb (sg_mem hσ ha)
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hb'
  have hu : uniformizer E < 1 := uniformizer_lt_one
  have ht' : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ uniformizer E := fun j l h => by
    rw [le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_le.trans_lt (ht j l h))]
    exact ht j l h
  let B := b * sg σ a
  have hdiag := diag_one (inv_mem hb')
  have hone (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∃ k ∈ ball n (uniformizer E), (∀ i j, valuation E (k⁻¹.val i j) ≤ 1) ∧
      ∃ s : Fin n → Eˣ,
        (∀ i, valuation E ((((s i)⁻¹ : Eˣ) : E) - B⁻¹.val i i) ≤ uniformizer E) ∧
        diagT E (Fin n) t * B = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    choose x μ hμ hx hxe using exists_row hσ t le_rfl hu ht' B.val B⁻¹.val B.inv_mul
      h1 h2 (diag_one hb') hdiag (fun j l h => le_uniformizer_iff.2 (h3 j l h))
      (fun j l h => by
        rw [map_mul]
        exact (mul_le_of_le_one_right' (h2 j l)).trans (ht' j l h))
    have hμ0 : ∀ i, μ i ≠ 0 := fun i h => by
      have hi := hμ i
      rw [h, zero_sub, Valuation.map_neg, hdiag i] at hi
      exact (not_le.2 hu) hi
    let M : Matrix (Fin n) (Fin n) E := Matrix.of x
    have hoff (i j) (h : i ≠ j) : valuation E (M i j) < 1 := by
      simpa [M, one_apply_ne h] using (hx i j).trans_lt hu
    have hd (i) : valuation E (M i i) = 1 := by
      have hi := (hx i i).trans_lt hu
      rw [one_apply_eq] at hi
      change valuation E (x i i) = 1
      rw [← sub_add_cancel (x i i) 1, Valuation.map_add_eq_of_lt_right, map_one]
      simpa only [map_one] using hi
    have hbound := vecMul_bound M (fun i j => by
      by_cases h : i = j
      · exact h ▸ (hd i).le
      · exact (hoff i j h).le) hd (fun i j h => hoff i j h.ne') n
    have hunit : IsUnit M := by
      refine vecMul_injective_iff_isUnit.1 fun u v huv => funext fun l => ?_
      have hzero : (u - v) ᵥ* M = 0 := by
        rw [sub_vecMul, sub_eq_zero]
        exact huv
      have hl := hbound (u - v) 0 (fun j hj => absurd j.2 (not_lt.2 hj))
        (fun j _ => le_of_eq ((map_eq_zero _).2 (congrFun hzero j))) l
      simpa [sub_eq_zero] using hl
    obtain ⟨k, hk⟩ := hunit
    refine ⟨k, fun i j => by rw [hk]; exact hx i j, ?_, fun i => (Units.mk0 _ (hμ0 i))⁻¹,
      fun i => by simpa using hμ i, ?_⟩
    · intro i j
      refine hbound (fun l => k⁻¹.val i l) 1 (fun l hl => absurd l.2 (not_lt.2 hl))
        (fun j _ => ?_) j
      rw [← hk]
      change valuation E ((k⁻¹.val * k.val) i j) ≤ 1
      rw [k.inv_mul]
      exact hone i j
    · rw [mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc]
      ext i j
      rw [Units.val_mul, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal,
        diagonal_mul, Matrix.mul_apply]
      have hsg (l) : (sg σ k).val i l = σ (x i l) := by
        show σ (k.val i l) = _
        rw [hk]
        rfl
      simp only [hsg, Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [mul_right_comm, ← hxe, hk, mul_inv_cancel_right₀ (hμ0 i)]
      rfl
  obtain ⟨k, hk, hk', s, hs, e⟩ := hconj
  have hkI : k ∈ iwahori E (Fin n) := by
    refine mem_iw.2 ⟨⟨fun i j => ?_, hk'⟩, fun i j h => by simpa [one_apply_ne h.ne'] using (hk i j).trans_lt hu⟩
    rw [← sub_add_cancel (k.val i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hk i j).trans hu.le) (hone i j)
  refine ⟨k * a⁻¹, mul_mem hkI (inv_mem ha), s, inv_mem_iff.1 fun i => ?_, ?_⟩
  · have hd := diag_one (inv_mem hb') i
    show valuation E (((s i)⁻¹ : Eˣ) : E) = 1
    rw [← sub_add_cancel (((s i)⁻¹ : Eˣ) : E) ((b * sg σ a)⁻¹.val i i), Valuation.map_add_eq_of_lt_right, hd]
    exact hd ▸ (hs i).trans_lt hu
  · calc a * diagT E (Fin n) t * b = a * (diagT E (Fin n) t * (b * sg σ a)) * (sg σ a)⁻¹ := by group
      _ = _ := by rw [e, map_mul (sg σ), map_inv]; group
end

section

open ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.BallG

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.neg (h : Bd a M) : Bd a (-M) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact h i j

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.pow (h : Bd a M) (ha : a ≤ 1) (m : ℕ) : Bd (a * a) ((1 + M) ^ m - 1 - m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have e : (1 + M) ^ (m + 1) - 1 - (m + 1) • M =
        ((1 + M) ^ m - 1 - m • M) + ((1 + M) ^ m - 1 - m • M) * M + (m • M) * M := by
      rw [pow_succ, succ_nsmul]
      generalize m • M = D
      noncomm_ring
    rw [e]
    exact (ih.add ((ih.mul h).mono (mul_le_of_le_one_right' ha))).add ((h.nsmul m).mul h)

private theorem Bd.inv (h : Bd a M) (ha : a < 1) (e : N = -M + -(M * N)) : Bd a N := by
  intro i j
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin n × Fin n => valuation E (N p.1 p.2)
  have hN : Bd (valuation E (N p.1 p.2)) N := fun i j => hp (i, j)
  refine (hp (i, j)).trans ?_
  have h1 : Bd (max a (a * valuation E (N p.1 p.2))) (-M + -(M * N)) :=
    (h.neg.mono (le_max_left _ _)).add ((h.mul hN).neg.mono (le_max_right _ _))
  have h2 := h1 p.1 p.2
  rw [← e] at h2
  rcases le_max_iff.mp h2 with h3 | h3
  · exact h3
  · by_contra h4
    have h0 : 0 < valuation E (N p.1 p.2) := lt_of_le_of_lt zero_le (not_le.mp h4)
    exact absurd h3 (not_le.mpr (mul_lt_of_lt_one_left h0 ha))

theorem valuation_natCast_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

theorem ball_mono {r s : ValueGroupWithZero E} (h : r ≤ s) : ball n r ⊆ ball n s := fun _ hg i j => (hg i j).trans h

def ballSub (n : ℕ) (r : ValueGroupWithZero E) (hr : r < 1) : Subgroup (GL (Fin n) E) where
  carrier := ball n r
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    have hy' : Bd r ((y : Matrix (Fin n) (Fin n) E) - 1) := hy
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
        (x - 1) + (y - 1) + ((x : Matrix (Fin n) (Fin n) E) - 1) * (y - 1) := by
      rw [Units.val_mul]; noncomm_ring
    have := (hx'.add hy').add ((hx'.mul hy').mono (mul_le_of_le_one_right' hr.le))
    rw [← e] at this
    exact this
  inv_mem' := by
    intro x hx
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    refine (hx'.inv hr (N := ((x⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) ?_ :)
    rw [mul_sub, sub_mul, Units.mul_inv]
    noncomm_ring

theorem isOpen_ball {r : ValueGroupWithZero E} (hr : r ≠ 0) : IsOpen (ball n r) := by
  have hO : IsOpen {x : E | valuation E x ≤ r} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 r hr, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact Valuation.map_add_le _ hx (le_of_lt (show valuation E z < r from hz))
  have e : ball n r = ⋂ i, ⋂ j, (fun g : GL (Fin n) E =>
      (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ⁻¹' {x : E | valuation E x ≤ r} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem isCompact_ball {r : ValueGroupWithZero E} (hr : r < 1) : IsCompact (ball n r) := by
  have h0 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r M} :=
    isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
      fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
  have h1 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r (M - 1)} :=
    (Homeomorph.subRight (1 : Matrix (Fin n) (Fin n) E)).isCompact_preimage.mpr h0
  have h2 := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ h1 h1
  convert h2 using 1
  ext g
  exact ⟨fun hg => ⟨hg, (ballSub n r hr).inv_mem hg⟩, fun hg => hg.1⟩

theorem pow_mem_ball {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E)) {u : GL (Fin n) E}
    (hu : u ∈ ball n r) : u ^ q ∈ ball n (r * valuation E (q : E)) := by
  have hu' : Bd r ((u : Matrix (Fin n) (Fin n) E) - 1) := hu
  have h1 := (hu'.pow (hr.le.trans (valuation_natCast_le_one q)) q).mono (mul_le_mul' le_rfl hr.le)
  have h2 : Bd (r * valuation E (q : E)) (q • ((u : Matrix (Fin n) (Fin n) E) - 1)) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, map_mul, mul_comm]
    exact mul_le_mul' (hu' i j) le_rfl
  have h3 := h1.add h2
  rw [sub_add_cancel, add_sub_cancel, ← Units.val_pow_eq_pow_val] at h3
  exact h3

theorem sg_mem_ball_iff {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} {u : GL (Fin n) E} :
    sg σ u ∈ ball n r ↔ u ∈ ball n r := by
  refine forall₂_congr fun i j => ?_
  have e : ((sg σ u : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      σ ((u : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [map_sub]
    congr 1
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [e, hσ]

theorem exists_fixed_root {σ : E ≃+* E} (hσ : Isom σ) {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E))
    {g : GL (Fin n) E} (hg : g ∈ ball n (r * valuation E (q : E))) (hf : sg σ g = g) :
    ∃ u ∈ ball n r, sg σ u = u ∧ u ^ q = g := by
  obtain ⟨u, ⟨hu, huq⟩, huu⟩ := rootEx E n q r hr g hg
  exact ⟨u, hu, huu _ ⟨(sg_mem_ball_iff hσ).mpr hu, by rw [← map_pow, huq, hf]⟩, huq⟩

theorem exists_radius {w : ValueGroupWithZero E} (hw : w ≠ 0) : ∃ r : ValueGroupWithZero E, 0 < r ∧ r < w := by
  obtain ⟨c, hc0, hc1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := E)
  exact ⟨c * w, mul_pos hc0 (zero_lt_iff.mpr hw), mul_lt_of_lt_one_left (zero_lt_iff.mpr hw) hc1⟩

end UpperTheory.ConvolutionTheory.Loc.BallG
end
