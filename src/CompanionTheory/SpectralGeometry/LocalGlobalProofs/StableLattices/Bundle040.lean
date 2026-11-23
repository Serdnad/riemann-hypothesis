module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle033
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle034
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.creation_product_support_degree : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | exact GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | (intros; apply GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_ordered_creation_list : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  first | exact @GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | exact GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | (intros; apply GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.highest_weight_vector_killed_by_raising : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.lF_single_omU | exact GlobalTheory.CompanionTheory.RgExh.lF_single_omU | (intros; apply GlobalTheory.CompanionTheory.RgExh.lF_single_omU <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.levi_action_unitary_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | exact GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | (intros; apply GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.ordered_creation_commutes_past_levi : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  first | exact @GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | exact GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | (intros; apply GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.locally_finite_levi_invariant_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cn n V), LocFin ε E → SuppIn (inU lev) y → Deg d y →
    ∃ T : Submodule ℂ (Cn n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppIn (inU lev) x ∧ Deg d x) ∧
      ∀ p q : Fin n, ε p = ε q → lev p = lev q → ∀ x ∈ T, lF E p q x ∈ T := by
  first | exact @GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable | exact GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable | (intros; apply GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable <;> assumption)
end

section

open Finset

namespace GlobalTheory.CompanionTheory.Labels

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Dec.J

variable {n : ℕ}

theorem tie_step {χ₀ χ : Fin n → ℂ} {t : Fin n}
    (hT : ∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) (hg : ∀ r, χ r ≠ χ t + 1) :
    ∀ r s, r ≠ s → (χ + Pi.single t 1 : Fin n → ℂ) r = (χ + Pi.single t 1 : Fin n → ℂ) s →
      (χ + Pi.single t 1 : Fin n → ℂ) r = χ₀ r ∧ (χ + Pi.single t 1 : Fin n → ℂ) s = χ₀ s := by
  intro r s hrs h
  by_cases hr : r = t
  · subst hr
    have hs : s ≠ r := hrs.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hs, add_zero] at h
    exact absurd h.symm (hg s)
  by_cases hs : s = t
  · subst hs
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hr, add_zero] at h
    exact absurd h (hg r)
  simp only [Pi.add_apply, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hs, add_zero] at h ⊢
  exact hT r s hrs h

theorem apply_swap_of_eq (χ : Fin n → ℂ) {r s : Fin n} (h : χ r = χ s) (i : Fin n) :
    χ i = χ (Equiv.swap r s i) := by
  by_cases h1 : i = r
  · subst h1; simp [h]
  by_cases h2 : i = s
  · subst h2; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem sum_filter_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) (a : Fin 3) :
    ∑ i ∈ univ.filter (fun i => (L ∘ Equiv.swap r s) i = a), χ i = ∑ i ∈ univ.filter (fun i => L i = a), χ i :=
  Finset.sum_equiv (Equiv.swap r s) (by simp) fun i _ => apply_swap_of_eq χ h i

theorem deg_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) :
    deg χ (L ∘ Equiv.swap r s) = deg χ L := by
  simp only [deg, sum_filter_swap χ L h]

theorem isLabel_swap {j : ℕ} {L : Fin n → Fin 3} (h : IsLabel j L) (r s : Fin n) :
    IsLabel j (L ∘ Equiv.swap r s) := by
  intro a
  rw [← h a]
  exact Finset.card_equiv (Equiv.swap r s) (by simp)

theorem moved_labels (χ₀ : Fin n → ℂ) (j : ℕ) : ∀ (ss : List (Fin n)) (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)),
    GoodPath χ ss → (∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) →
    (∀ L ∈ Λ, IsLabel j L ∧ (deg χ₀ L).re < 0) →
    ∀ L ∈ moveIter χ Λ ss, IsLabel j L ∧ (deg χ₀ L).re < 0 := by
  intro ss
  induction ss with
  | nil =>
    intro χ Λ _ _ hΛ L hL
    exact hΛ L hL
  | cons t ss ih =>
    intro χ Λ hg hT hΛ L hL
    refine ih (χ + Pi.single t 1) (move χ Λ t) hg.2 (tie_step hT hg.1) ?_ L hL
    rintro _ ⟨L₀, hL₀, r, hr, rfl⟩
    obtain ⟨hl, hd⟩ := hΛ L₀ hL₀
    refine ⟨isLabel_swap hl r t, ?_⟩
    by_cases hrt : r = t
    · subst hrt
      simpa using hd
    · obtain ⟨h1, h2⟩ := hT r t hrt hr
      rw [deg_swap χ₀ L₀ (h1.symm.trans (hr.trans h2))]
      exact hd

theorem labelTrack : LabelTrack := by
  intro n χ ss B j hg hf L hL
  obtain ⟨hl, hd⟩ := moved_labels χ j ss χ _ hg (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun _ h => h) L hL
  refine hf (univ.filter fun s => L s = 2) (univ.filter fun s => L s = 0) ?_ ?_ hd
  · refine Finset.disjoint_filter.2 fun x _ h1 h2 => ?_
    rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [hl 2, hl 0]
    simp [dims]

end GlobalTheory.CompanionTheory.Labels
end

section

noncomputable section

open Matrix CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.GradEig

variable {n : ℕ}

theorem Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem trace_eq_zero {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) : A.trace = 0 := by
  obtain ⟨hG, hH, -, -⟩ := h
  have hG' : A.conjTranspose * Jm ε + Jm ε * A = 0 := hG
  rw [hH] at hG'
  have h1 : A * Jm ε = -(Jm ε * A) := eq_neg_of_add_eq_zero_left hG'
  have h2 : (A * Jm ε * Jm ε).trace = -(Jm ε * A * Jm ε).trace := by
    rw [h1, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.mul_assoc A, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_cycle, Jm_mul_self,
    Matrix.one_mul] at h2
  linear_combination h2 / 2

theorem eigenvalue_cases {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h3 : A * A * A = A) (i : Fin n) :
    hA.eigenvalues i = -1 ∨ hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have hev := hA.mulVec_eigenvectorBasis i
  obtain ⟨v, hv⟩ : ∃ v, v = (hA.eigenvectorBasis i).ofLp := ⟨_, rfl⟩
  rw [← hv] at hev
  obtain ⟨r, hr⟩ : ∃ r, r = hA.eigenvalues i := ⟨_, rfl⟩
  rw [← hr] at hev ⊢
  have h3v : (A * A * A) *ᵥ v = (r ^ 3) • v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hev, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [h3, hev] at h3v
  have hne : v ≠ 0 := by
    intro h0
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
    have h2 : hA.eigenvectorBasis i = 0 := by
      rw [hv] at h0
      simpa using h0
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1
  have hr3 : r ^ 3 = r := by
    have h4 : (r ^ 3 - r) • v = 0 := by rw [sub_smul, ← h3v, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 hne
  have hf : r * (r - 1) * (r + 1) = 0 := by linear_combination hr3
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

theorem exists_perm_blocks {c : Fin n → Fin 3} {d : Fin 3 → ℕ} (hd : ∑ i, d i = n)
    (hc : ∀ i, Fintype.card {x // c x = i} = d i) :
    ∃ σ : Fin n ≃ Fin n, ∀ p, c (σ p) = ((stdBlocks d hd).symm p).1 := by
  classical
  let e : ∀ i, {x // c x = i} ≃ Fin (d i) := fun i => Fintype.equivFinOfCardEq (hc i)
  let τ : Fin n ≃ Fin n :=
    ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight e)).trans (stdBlocks d hd)
  refine ⟨τ.symm, fun p => ?_⟩
  have hτ : τ.symm p = (((e ((stdBlocks d hd).symm p).1).symm ((stdBlocks d hd).symm p).2) : Fin n) := rfl
  rw [hτ]
  exact ((e _).symm _).2

theorem exists_gradBasis {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) :
    Nonempty (GradBasis A) := by
  classical
  have htr := trace_eq_zero h
  obtain ⟨_, hH, h3, _⟩ := h
  have hA : A.IsHermitian := hH
  have hcase := eigenvalue_cases hA h3
  let c : Fin n → Fin 3 := fun x =>
    if hA.eigenvalues x = -1 then 0 else if hA.eigenvalues x = 0 then 1 else 2
  have hc0 : ∀ x, c x = 0 ↔ hA.eigenvalues x = -1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc1 : ∀ x, c x = 1 ↔ hA.eigenvalues x = 0 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc2 : ∀ x, c x = 2 ↔ hA.eigenvalues x = 1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hval : ∀ x, (![-1, 0, 1] : Fin 3 → ℂ) (c x) = ((hA.eigenvalues x : ℝ) : ℂ) := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> rfl
  obtain ⟨j, hj⟩ : ∃ j, (Finset.univ.filter fun x => hA.eigenvalues x = -1).card = j := ⟨_, rfl⟩
  have hsumR : ∑ x, hA.eigenvalues x = 0 := by
    have h1 := hA.trace_eq_sum_eigenvalues
    rw [htr] at h1
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2.symm
  have hk1 : (Finset.univ.filter fun x => hA.eigenvalues x = 1).card = j := by
    have hs : ∑ x, hA.eigenvalues x = ∑ x, ((if hA.eigenvalues x = 1 then (1 : ℝ) else 0) -
        (if hA.eigenvalues x = -1 then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsumR, hj] at hs
    have hs' : ((Finset.univ.filter fun x => hA.eigenvalues x = 1).card : ℝ) = j := by linarith
    exact_mod_cast hs'
  have htot : j + (Finset.univ.filter fun x => hA.eigenvalues x = 0).card + j = n := by
    have hs : ∑ x : Fin n, ((if hA.eigenvalues x = -1 then 1 else 0) +
        (if hA.eigenvalues x = 0 then 1 else 0) + (if hA.eigenvalues x = 1 then 1 else 0) : ℕ) =
        ∑ x : Fin n, 1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, hj, hk1] at hs
    simpa using hs
  have hcard : ∀ i, Fintype.card {x // c x = i} = dims n j i := by
    intro i
    fin_cases i
    · show Fintype.card {x // c x = 0} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc0 x, hj]
    · show Fintype.card {x // c x = 1} = n - 2 * j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc1 x]
      omega
    · show Fintype.card {x // c x = 2} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc2 x, hk1]
  have hd : ∑ i, dims n j i = n := by
    rw [Fin.sum_univ_three]
    show j + (n - 2 * j) + j = n
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_blocks hd hcard
  have hs := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hdiag : (diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) =
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).submatrix σ σ := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext p
    rw [← hσ p, hval]
    rfl
  have e1 : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, hUU, Matrix.submatrix_id_id]
  have e2 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hUU', Matrix.submatrix_one_equiv]
  have e3 : A = ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id := by
    rw [hdiag, ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.submatrix_id_id]
    exact hs
  exact ⟨⟨_, _, e1, e2, j, hd, e3⟩⟩

end GlobalTheory.CompanionTheory.GradEig

theorem GlobalTheory.CompanionTheory.GradEig.basis : CompanionTheory.RgExh.Dec.J.Basis := by
  intro n ε A h
  exact GlobalTheory.CompanionTheory.GradEig.exists_gradBasis h
end
end
