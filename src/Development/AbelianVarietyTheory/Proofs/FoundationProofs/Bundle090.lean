module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle062
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  first | exact @GlobalTheory.FN.mob_props | exact GlobalTheory.FN.mob_props | (intros; apply GlobalTheory.FN.mob_props <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N → (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  first | exact @GlobalTheory.PsType.twKer_one_mem_aug_stage | exact GlobalTheory.PsType.twKer_one_mem_aug_stage | (intros; apply GlobalTheory.PsType.twKer_one_mem_aug_stage <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_det_of_mem_KO' {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, rfl⟩ := hg
  have hu : IsUnit (h.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  change valuation k ((algebraMap 𝒪[k] k).mapMatrix h.val).det = 1
  rw [← RingHom.map_det]
  exact this

private theorem ev_one' (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

private theorem minor_last {n : ℕ} (g : GL (Fin (n + 1)) k) : minor g (Fin.last n) = g.val.det := by
  unfold minor Matrix.toSquareBlockProp Matrix.toBlock
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin (n + 1) => i ≤ Fin.last n)
    (fun i => Fin.le_last i)) g.val
  rw [← this]; rfl

theorem const_family (n : ℕ) (χ : kˣ →* ℂˣ) :
    grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧
      ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]
    intro _ i j _ u _ _
    rfl
  · intro g hg
    cases n with
    | zero =>
      simp [theta, detChar_apply]
      have h0 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      rw [h0, map_one, Units.val_one]
    | succ n =>
      unfold theta
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1 := by
        intro i
        have : nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ := by
          unfold nxt; rw [dite_eq_left (by simp)]
        rw [this, div_self']; exact ev_one' _
      have h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1 := by
        unfold nxt; rw [dite_eq_right (by simp)]
      simp only [h1, Finset.prod_const_one, one_mul, h2, div_one, minor_last]
      have hv := valuation_det_of_mem_KO' hg
      unfold ev
      rw [dite_eq_left hv, detChar_apply]
      congr 2
      ext; simp

theorem const_family_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) :=
  fun _ _ _ _ _ n χ => const_family n χ

end GlobalTheory.PsType
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.StripGrp

variable {k : Type} [Field k] [ValuativeRel k]

theorem triv_mono {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y :=
  fun u hu h1 => hx u hu (h1.trans h)

theorem triv_add {χ : kˣ →* ℂˣ} {x y : k} (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le h le_rfl)) hy
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le le_rfl h)) hx

theorem triv_neg {χ : kˣ →* ℂˣ} {x : k} (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono (by rw [Valuation.map_neg]) hx

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h1
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h1) zero_le'
  have hu : u = 1 := Units.ext (sub_eq_zero.mp ((Valuation.zero_iff _).mp h0))
  simp [hu]

theorem le_inv_of_mul_le {a b : ValueGroupWithZero k} (ha : a ≠ 0) (h : a * b ≤ 1) : b ≤ a⁻¹ :=
  calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left₀ ha b).symm
    _ ≤ a⁻¹ * 1 := by gcongr
    _ = a⁻¹ := mul_one _

variable {n : ℕ}

theorem ne_of_blk {r : ℕ} {i j : Fin n} (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) : i ≠ j := by
  rintro rfl; omega

theorem val_one_apply_le (i j : Fin n) : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mul_eq_zero_of_blk {r : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → A i j = 0)
    (hB : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → B i j = 0) : A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < r
  · rw [hA i l (fun h => absurd h.2 (not_le.mpr hl)), zero_mul]
  · rw [hB l j (fun h => hl h.1), mul_zero]

variable {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ}

theorem mem_strip {g : GL (Fin n) k} : g ∈ strip ψ r ϖ m ↔ ∀ i j : Fin n,
    if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := Iff.rfl

theorem sub_one_of_mem {g : GL (Fin n) k} (hg : g ∈ strip ψ r ϖ m) (i j : Fin n)
    (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : (g.val - 1) i j = 0 := by
  have := mem_strip.mp hg i j
  rw [if_neg h] at this
  simp [Matrix.sub_apply, this]

theorem one_mem : (1 : GL (Fin n) k) ∈ strip ψ r ϖ m := by
  intro i j
  split_ifs with h
  · simp only [Units.val_one, Matrix.one_apply_ne (ne_of_blk h), mul_zero, map_zero, zero_le',
      true_and]
    exact triv_zero _
  · rfl

theorem mul_mem {a b : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) (hb : b ∈ strip ψ r ϖ m) :
    a * b ∈ strip ψ r ϖ m := by
  have key : (a * b).val = 1 + (a.val - 1) + (b.val - 1) := by
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem hb)
    rw [Units.val_mul]
    calc a.val * b.val = (1 + (a.val - 1)) * (1 + (b.val - 1)) := by simp
      _ = 1 + (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  have hB := mem_strip.mp hb i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA hB
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.add_apply, Matrix.sub_apply, h1, sub_zero, zero_add]
    rw [mul_add]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le hA.1 hB.1), triv_add hA.2 hB.2⟩
  · rw [if_neg h] at hA hB
    simp only [Matrix.add_apply, Matrix.sub_apply, hA, hB, sub_self, add_zero]

theorem inv_mem {a : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) : a⁻¹ ∈ strip ψ r ϖ m := by
  have key : (a⁻¹).val = 1 - (a.val - 1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem ha)
    calc a.val * (1 - (a.val - 1)) = 1 - (a.val - 1) * (a.val - 1) := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.sub_apply, h1, sub_zero, zero_sub, mul_neg, Valuation.map_neg]
    exact ⟨hA.1, triv_neg hA.2⟩
  · rw [if_neg h] at hA
    simp only [Matrix.sub_apply, hA, sub_self, sub_zero]

theorem mono {m m' : ℕ} (hϖ : valuation k ϖ < 1) (hmm : m ≤ m') :
    strip ψ r ϖ m ⊆ strip ψ r ϖ m' := by
  intro g hg i j
  have hA := mem_strip.mp hg i j
  split_ifs with h
  · rw [if_pos h] at hA
    have hle : valuation k (ϖ ^ m' * g.val i j) ≤ valuation k (ϖ ^ m * g.val i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      gcongr ?_ * _
      exact pow_le_pow_right_of_le_one' hϖ.le hmm
    exact ⟨hle.trans hA.1, triv_mono hle hA.2⟩
  · rwa [if_neg h] at hA

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_triv (χ : kˣ →* ℂˣ) : IsClosed {x : k | Triv χ x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation k x ≠ 0 := fun h0 => hx (by
    have : x = 0 := (Valuation.zero_iff _).mp h0
    rw [this]; exact triv_zero χ)
  refine Filter.mem_of_superset ((valuation k).locally_const hx0) ?_
  intro y hy hT
  exact hx (triv_mono (le_of_eq hy.symm) hT)

theorem isClosed_strip : IsClosed (strip ψ r ϖ m) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hball : IsClosed {z : k | valuation k z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed
  have hS : IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ i j : Fin n,
      if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * A i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * A i j)
      else A i j = (1 : Matrix (Fin n) (Fin n) k) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) k => A i j :=
      (continuous_apply j).comp (continuous_apply i)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [if_pos h]
      exact (hball.inter (isClosed_triv _)).preimage (continuous_const.mul hc)
    · simp only [if_neg h]
      exact isClosed_eq hc continuous_const
  exact hS.preimage Units.continuous_val

theorem isCompact_strip (hϖ0 : ϖ ≠ 0) (hϖ : valuation k ϖ < 1) : IsCompact (strip ψ r ϖ m) := by
  set a := valuation k (ϖ ^ m) with ha_def
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hϖ0)
  have ha1 : a ≤ 1 := by rw [ha_def, map_pow]; exact pow_le_one' hϖ.le _
  have h1t : (1 : ValueGroupWithZero k) ≤ a⁻¹ := le_inv_of_mul_le ha0 (by rw [mul_one]; exact ha1)
  have hbd : ∀ g ∈ strip ψ r ϖ m, ∀ i j : Fin n, valuation k (g.val i j) ≤ a⁻¹ := by
    intro g hg i j
    have hA := mem_strip.mp hg i j
    split_ifs at hA with h
    · exact le_inv_of_mul_le ha0 (by rw [ha_def, ← map_mul]; exact hA.1)
    · rw [hA]; exact (val_one_apply_le i j).trans h1t
  refine (GlobalTheory.PairingOne.isCompact_bounded (m := Fin n) a⁻¹).of_isClosed_subset isClosed_strip ?_
  intro g hg
  exact ⟨hbd g hg, hbd g⁻¹ (inv_mem hg)⟩

theorem strip_datum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  intro k _ _ _ _ n ψ r ϖ _ hϖ0 hϖ _
  refine ⟨fun m => ⟨one_mem, fun a ha b hb => mul_mem ha hb, fun a ha => inv_mem ha,
    isCompact_strip hϖ0 hϖ, rfl, fun _ _ _ _ => (mul_one 1).symm,
    ⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩⟩, fun m m' hmm => mono hϖ hmm⟩

end GlobalTheory.StripGrp
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  first | exact @GlobalTheory.PsType.triv_ev_props | exact GlobalTheory.PsType.triv_ev_props | (intros; apply GlobalTheory.PsType.triv_ev_props <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  first | exact @GlobalTheory.PsType.cut_or_const | exact GlobalTheory.PsType.cut_or_const | (intros; apply GlobalTheory.PsType.cut_or_const <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.Tower.B_sub_mem | exact GlobalTheory.KZ.Tower.B_sub_mem | (intros; apply GlobalTheory.KZ.Tower.B_sub_mem <;> assumption)
end

section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.derivationOn_adjoin_mem_span_image : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D → ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  first | exact @GlobalTheory.AlmostEt.derOn_adjoin_mem_span | exact GlobalTheory.AlmostEt.derOn_adjoin_mem_span | (intros; apply GlobalTheory.AlmostEt.derOn_adjoin_mem_span <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  first | exact @GlobalTheory.diam_exists | exact GlobalTheory.diam_exists | (intros; apply GlobalTheory.diam_exists <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ), (∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := by
  first | exact @GlobalTheory.KZ.PolAct.act_mem_pol | exact GlobalTheory.KZ.PolAct.act_mem_pol | (intros; apply GlobalTheory.KZ.PolAct.act_mem_pol <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.isDiamondMatrix_chosenDiamondMatrixGamma1Gamma0 : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N → IsDiam N l d (sgD N l d) := by
  first | exact @GlobalTheory.KZ.isDiam_sgD_of_prime | exact GlobalTheory.KZ.isDiam_sgD_of_prime | (intros; apply GlobalTheory.KZ.isDiam_sgD_of_prime <;> assumption)
end
