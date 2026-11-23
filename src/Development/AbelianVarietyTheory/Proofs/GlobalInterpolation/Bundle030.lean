module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import ReciprocityTheory.GaloisValuations.Bundle002
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TangentSection

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot GlobalTheory.QuadricSection

variable {P Q P' Q' : ℕ}

theorem jpq_eq_diagonal (P Q : ℕ) :
    Formalism.UG.Jpq P Q = diagonal fun i : Fin P ⊕ Fin Q => ((sg i : ℝ) : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, sg, diagonal_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp

theorem norm_sg (i : Fin P ⊕ Fin Q) : ‖((sg i : ℝ) : ℂ)‖ = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

def flipAt (k : Fin P ⊕ Fin Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  diagonal fun i => if i = k then 1 else -1

theorem flipAt_unitary (k : Fin P ⊕ Fin Q) :
    (flipAt k)ᴴ * Formalism.UG.Jpq P Q * flipAt k = Formalism.UG.Jpq P Q := by
  rw [jpq_eq_diagonal, flipAt, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = k <;> simp [h]

theorem flipAt_mulVec (k : Fin P ⊕ Fin Q) :
    flipAt k *ᵥ (Pi.single k 1 : Sp P Q) = Pi.single k 1 := by
  funext i
  rw [flipAt, mulVec_diagonal]
  by_cases h : i = k <;> simp [h]

theorem coef_single (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) = star (1 + y k) * (sg k : ℂ) := by
  rw [coef, jpq_eq_diagonal, dotProduct, Finset.sum_eq_single k]
  · simp [mulVec_diagonal]
  · intro b _ hb; simp [mulVec_diagonal, hb]
  · simp

theorem coef_single_ne (k : Fin P ⊕ Fin Q) (y : Sp P Q) (hy : y k ≠ -1) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) ≠ 0 := by
  rw [coef_single]
  refine mul_ne_zero (star_ne_zero.2 fun h => hy ?_) (by exact_mod_cast sg_ne_zero k)
  linear_combination h

theorem qf_single (k : Fin P ⊕ Fin Q) : qf (Pi.single k 1 : Sp P Q) = sg k := by
  rw [qf_eq_sum, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp


open Classical in
def tanMat (k : Fin P ⊕ Fin Q) (y : Sp P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  if qf y = sg k ∧ y k ≠ -1 then -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) * flipAt k
  else sectMat (sg k) (Pi.single k 1) y

theorem tanMat_spec (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    (tanMat k y)ᴴ * Formalism.UG.Jpq P Q * tanMat k y = Formalism.UG.Jpq P Q ∧
      (qf y = sg k → tanMat k y *ᵥ (Pi.single k 1 : Sp P Q) = y) := by
  unfold tanMat
  split_ifs with h
  · have hc := coef_single_ne k y h.2
    have hu := qrefl_unitary _ (jpq_conjTranspose P Q) (Pi.single k 1) (-y)
      (by rw [form_self, form_self, qf_neg, qf_single, h.1]) hc
    refine ⟨?_, fun _ => ?_⟩
    · rw [neg_mul, conjTranspose_neg, neg_mul, neg_mul_neg, conjTranspose_mul]
      calc _ = (flipAt k)ᴴ * ((qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y))ᴴ * Formalism.UG.Jpq P Q *
            qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y)) * flipAt k := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu, flipAt_unitary]
    · rw [← mulVec_mulVec, flipAt_mulVec, neg_mulVec, qrefl_mulVec _ _ _ hc, neg_neg]
  · exact sectMat_spec (sg_ne_zero k) (qf_single k) y

theorem measurable_tanMat (k i j : Fin P ⊕ Fin Q) : Measurable fun y => tanMat k y i j := by
  classical
  have : (fun y => tanMat k y i j) = fun y => if qf y = sg k ∧ y k ≠ -1 then
      -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) i j * (if j = k then 1 else -1)
      else sectMat (sg k) (Pi.single k 1) y i j := by
    funext y
    unfold tanMat
    by_cases h : qf y = sg k ∧ y k ≠ -1
    · rw [if_pos h, if_pos h, flipAt, mul_diagonal]; rfl
    · rw [if_neg h, if_neg h]
  rw [this]
  refine Measurable.ite ?_
    (((measurable_qrefl _ _ i j).comp measurable_neg).neg.mul measurable_const)
    (measurable_sectMat _ _ i j)
  have h2 : MeasurableSet ((fun y : Sp P Q => y k) ⁻¹' ({-1} : Set ℂ)ᶜ) :=
    (measurable_pi_apply k) (measurableSet_singleton (-1 : ℂ)).compl
  exact (measurable_qf (measurableSet_singleton (sg k))).inter h2

theorem tanMat_sub_one (k i b : Fin P ⊕ Fin Q) (y : Sp P Q) (h1 : qf y = sg k) (h2 : y k ≠ -1)
    (hb : b ≠ k) :
    ‖(tanMat k y - 1) i b‖ = ‖(Pi.single k 1 : Sp P Q) i + y i‖ * ‖y b‖ / ‖1 + y k‖ := by
  have : (tanMat k y - 1) i b = -((star (1 + y k) * (sg k : ℂ))⁻¹ *
      (((Pi.single k 1 : Sp P Q) i + y i) * (star (y b) * (sg b : ℂ)))) := by
    rw [tanMat, if_pos ⟨h1, h2⟩, Matrix.sub_apply, flipAt, mul_diagonal, if_neg hb, qrefl,
      coef_single]
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, jpq_eq_diagonal, vecMul_diagonal, Pi.star_apply, Pi.add_apply,
      Pi.single_eq_of_ne hb, sub_neg_eq_add, zero_add]
    ring
  rw [this]
  simp only [norm_neg, norm_mul, norm_inv, norm_star, norm_sg, mul_one]
  ring

theorem exists_tangent_section : ∀ (P Q P' Q' : ℕ)
    (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), ∃ σ : Sp P Q → UpqT P Q,
    IsSection (sg (e none)) (baseVec e) σ ∧ ∀ y : Sp P Q, qf y = sg (e none) → y (e none) ≠ -1 →
      (∀ b, ‖UpqT.mat (σ y) (e none) (e (some b))‖ = ‖y (e (some b))‖) ∧
      ∀ a b, ‖(UpqT.mat (σ y) - 1) (e (some a)) (e (some b))‖ =
        ‖y (e (some a))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖ := by
  intro P Q P' Q' e
  have hex : ∀ y, ∃ g : UpqT P Q, UpqT.mat g = tanMat (e none) y := fun y => by
    have : tanMat (e none) y ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
      rw [GlobalTheory.UpqTopology.range_mat]; exact (tanMat_spec _ y).1
    exact this
  choose s hs using hex
  have hne : ∀ b, e (some b) ≠ e none := fun b h => by simpa using e.injective h
  refine ⟨s, ⟨?_, fun y hy => ?_⟩, fun y h1 h2 => ⟨fun b => ?_, fun a b => ?_⟩⟩
  · have : BorelSpace (UpqT P Q) := (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
    have he : MeasurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) (UpqT.mat (P := P) (Q := Q)) :=
      Topology.IsClosedEmbedding.measurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) GlobalTheory.UpqTopology.isClosedEmbedding_mat
    refine he.measurable_comp_iff.1 ?_
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Function.comp, hs] using measurable_tanMat (e none) i j
  · rw [act, hs]; exact (tanMat_spec _ y).2 hy
  · have h := tanMat_sub_one (e none) (e none) (e (some b)) y h1 h2 (hne b)
    rw [Matrix.sub_apply, Matrix.one_apply_ne (hne b).symm, sub_zero, Pi.single_eq_same] at h
    have h0 : ‖1 + y (e none)‖ ≠ 0 := norm_ne_zero_iff.2 fun h => h2 (by linear_combination h)
    rw [hs, h]
    field_simp
  · rw [hs, tanMat_sub_one (e none) _ _ y h1 h2 (hne b), Pi.single_eq_of_ne (hne a), zero_add]

end GlobalTheory.TangentSection
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcMult


open Polynomial in
noncomputable def linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) : k[X] :=
  ∏ i, (1 - Polynomial.C (a i) * Polynomial.X)

open Polynomial in
theorem linProd_ne_zero {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    linProd a ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [linProd, Polynomial.eval_prod] at this

open Polynomial in
theorem count_roots_factor {k : Type} [Field k] [DecidableEq k] (c y : k) (hy : y ≠ 0) :
    Multiset.count y⁻¹ (1 - Polynomial.C c * Polynomial.X).roots = if c = y then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc
    have : (0 : k) ≠ y := fun h => hy h.symm
    simp [this]
  · have e : (1 - Polynomial.C c * Polynomial.X) = Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹) := by
      rw [mul_sub, ← Polynomial.C_mul]
      simp [hc]
      ring
    rw [e, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc), Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
    by_cases h : c = y
    · simp [h]
    · have : y⁻¹ ≠ c⁻¹ := fun h' => h (inv_injective h').symm
      simp [h, this]

open Polynomial in
theorem count_roots_linProd {k : Type} [Field k] [DecidableEq k] {ι : Type} [Fintype ι] (a : ι → k) (y : k)
    (hy : y ≠ 0) :
    Multiset.count y⁻¹ (linProd a).roots = (Finset.univ.filter fun i => a i = y).card := by
  classical
  have h := linProd_ne_zero a
  unfold linProd at h ⊢
  rw [Polynomial.roots_prod _ _ h, Multiset.count_bind]
  simp only [count_roots_factor _ _ hy]
  rw [Finset.card_filter]
  rfl

theorem coe_linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    ((linProd a : Polynomial k) : PowerSeries k) = ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) := by
  rw [linProd, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem zmod_const_of_step (p : ℕ) [Fact p.Prime] (m m' : ZMod p → ℕ)
    (h : ∀ y : ZMod p, y + 1 ≠ 0 → m y + m' (y + 1) = m' y + m (y + 1))
    (hs : ∑ x, m x = ∑ x, m' x) : ∀ x, m x = m' x := by
  set d : ZMod p → ℤ := fun x => (m x : ℤ) - m' x with hd
  have step : ∀ y : ZMod p, y + 1 ≠ 0 → d (y + 1) = d y := by
    intro y hy
    have := h y hy
    simp only [hd]
    omega
  have hp := (Fact.out : p.Prime)
  have hn : ∀ n : ℕ, n < p → d (n : ZMod p) = d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hlt
      have hne : ((n : ZMod p) + 1) ≠ 0 := by
        intro h0
        have : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      push_cast
      rw [step _ hne, ih (by omega)]
  have hc : ∀ x, d x = d 0 := by
    intro x
    have := hn x.val (ZMod.val_lt x)
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ x, d x = 0 := by
    simp only [hd, Finset.sum_sub_distrib]
    have hs' : (∑ x, (m x : ℤ)) = ∑ x, (m' x : ℤ) := by exact_mod_cast hs
    rw [hs', sub_self]
  rw [Finset.sum_congr rfl (fun x _ => hc x), Finset.sum_const, Finset.card_univ, ZMod.card] at hsum
  have h0 : d 0 = 0 := by
    rcases smul_eq_zero.mp hsum with h | h
    · exact absurd h hp.ne_zero
    · exact h
  intro x
  have := hc x
  rw [h0] at this
  simp only [hd] at this
  omega

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem card_cast_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i)]
  exact (ZMod.castHom_injective k).eq_iff

theorem card_cast_succ_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) + 1 = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z - 1).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i), ← map_one (ZMod.castHom (dvd_refl p) k),
    ← map_add, (ZMod.castHom_injective k).eq_iff, eq_sub_iff_add_eq]

theorem sum_card_fiber {p : ℕ} [NeZero p] {N : ℕ} (l : Fin N → ℕ) :
    ∑ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = N := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i => (l i : ZMod p)) (s := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp

end GlobalTheory.AlcMult

open GlobalTheory.AlcMult in
theorem GlobalTheory.Alc.multiset_eq_of_series_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (l l' : Fin N → ℕ), (∏ i, (1 - PowerSeries.C ((l i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l' i : k) * PowerSeries.X) = (∏ i, (1 - PowerSeries.C ((l' i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l i : k) * PowerSeries.X) → ∀ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = (Finset.univ.filter fun i => (l' i : ZMod p) = x).card := by
  intro p hp k _ _ N l l' H
  haveI : Fact p.Prime := ⟨hp⟩
  letI : DecidableEq k := Classical.decEq k
  have HP : linProd (fun i => (l i : k) + 1) * linProd (fun i => (l' i : k)) =
      linProd (fun i => (l' i : k) + 1) * linProd (fun i => (l i : k)) := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, coe_linProd, coe_linProd, coe_linProd, coe_linProd]
    exact H
  have hcount : ∀ y : k, y ≠ 0 →
      (Finset.univ.filter fun i => (l i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l' i : k) = y).card =
      (Finset.univ.filter fun i => (l' i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l i : k) = y).card := by
    intro y hy
    have e := congrArg (fun q => Multiset.count y⁻¹ q.roots) HP
    rw [Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Multiset.count_add, Multiset.count_add, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy,
      count_roots_linProd _ _ hy, count_roots_linProd _ _ hy] at e
    exact e
  apply zmod_const_of_step p
  · intro y hy
    have hne : ZMod.castHom (dvd_refl p) k (y + 1) ≠ 0 := by
      rw [← map_zero (ZMod.castHom (dvd_refl p) k)]
      exact fun h => hy ((ZMod.castHom_injective k) h)
    have := hcount _ hne
    rw [card_cast_succ_eq, card_cast_succ_eq, card_cast_eq, card_cast_eq, add_sub_cancel_right] at this
    exact this
  · rw [sum_card_fiber, sum_card_fiber]
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.CMRam

theorem val_int_le {E Ω : Type*} [Field E] [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι a) ≤ 1 :=
  (A.valuation_le_one_iff _).2
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (a.isIntegral_coe.map ι.toIntAlgHom))

theorem exists_den_field {E Ω : Type*} [Field E] [NumberField E] [Field Ω] (ι : E →+* Ω)
    (A : ValuationSubring Ω) {x : E} (hx : A.valuation (ι x) ≤ 1) :
    ∃ s t : 𝓞 E, A.valuation (ι s) = 1 ∧ (s : E) * x = t := by
  first
  | exact @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | (apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator ..)

end GlobalTheory.CMRam
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.V

namespace GlobalTheory.OrdLoc.Dcmp

open ReciprocityTheory.Gal (H0 H1 H2 Z2 B1 B2 ContAction charRep twDual cup20 TDual)

section Abstract

variable {n : ℕ} [NeZero n] {G : Type} [Group G] [TopologicalSpace G] {R : Type} [CommRing R] [Finite R]
  [Algebra (ZMod n) R] [TopologicalSpace R] [DiscreteTopology R]



end Abstract

open NumberField IsDedekindDomain in
private lemma span_prime_isMaximal_ratRingOfIntegers {l : ℕ} [hl : Fact l.Prime] :
    (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal := by
  have hZ : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hc := Ideal.comap_isMaximal_of_surjective (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
    (Rat.ringOfIntegersEquiv).surjective (K := Ideal.span {((l : ℕ) : ℤ)})
  have heq : Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
      (Ideal.span {((l : ℕ) : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) _ = _
    rw [← Ideal.map_symm, Ideal.map_span]
    simp
  rwa [heq] at hc

open NumberField IsDedekindDomain in
private lemma asIdeal_eq_span_of_prime_mem {l : ℕ} [Fact l.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} :=
  (span_prime_isMaximal_ratRingOfIntegers.eq_of_le w.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.OrdLoc.Dcmp.locDeg_rat {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    _root_.ReciprocityTheory.Gal.locDeg v = 1 := by
  have hT : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ ({v} : Finset _) ↔ ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
    intro w
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact hv
    · intro hw
      exact HeightOneSpectrum.ext
        ((asIdeal_eq_span_of_prime_mem hw).trans (asIdeal_eq_span_of_prime_mem hv).symm)
  have h := _root_.ReciprocityTheory.Gal.sum_locDegree (F := ℚ) l {v} hT
  rw [Finset.sum_singleton, Module.finrank_self] at h
  exact h

variable {l : ℕ} [Fact l.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

end GlobalTheory.OrdLoc.Dcmp
end
end
