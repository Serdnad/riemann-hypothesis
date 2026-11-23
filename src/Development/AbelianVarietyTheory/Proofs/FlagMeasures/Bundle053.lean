module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerBetweenLatticeStabilizers
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsProdDenominatorUnitriangularFactors
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariant
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem absNorm_dInv_eq_abs_discr_pow_inv :
    ∀ (K : Type) [Field K] [NumberField K] (j : ℕ),
      (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  intro K _ _ j

  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm (K := K),
    NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs]
  push_cast
  rw [inv_pow]

end GlobalTheory.SnMass.VolN
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.UniCount

section
variable {E : Type} [CommRing E] {N : ℕ}

theorem isUni_mul {s t : Matrix (Fin N) (Fin N) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h1 | h1
    · rw [hs.1 i l h1, zero_mul]
    · rw [ht.1 l j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, ht.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [hs.1 i l h1, zero_mul]
      · rw [ht.1 l i h1, mul_zero]
    · simp

def rowM (k : Fin N) (c : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  1 + Matrix.of fun a b => if a = k then c b else 0

theorem mul_rowM (w : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E) (i j : Fin N) :
    (w * rowM k c) i j = w i j + w i k * c j := by
  rw [rowM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp

theorem isUni_rowM (k : Fin N) (c : Fin N → E) (hc : ∀ j, j ≤ k → c j = 0) :
    IsUni (rowM k c) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne h.ne']
    split_ifs with h1
    · rw [hc j (h1 ▸ h.le), add_zero]
    · simp
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    split_ifs with h1
    · rw [hc i h1.le, add_zero]
    · simp
end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}

theorem isIntM_mul (L : LocE F E) {s t : Matrix (Fin N) (Fin N) E} (hs : IsIntM L s)
    (ht : IsIntM L t) : IsIntM L (s * t) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hs i l) (ht l j)

theorem isIntM_rowM (L : LocE F E) (k : Fin N) (c : Fin N → E) (hc : ∀ j, c j ∈ L.O) :
    IsIntM L (rowM k c) := fun i j => by
  simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  refine add_mem ?_ ?_
  · split_ifs
    exacts [one_mem _, zero_mem _]
  · split_ifs
    exacts [hc j, zero_mem _]

def cos (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}

theorem cos_mul_subset (L : LocE F E) (u B : Matrix (Fin N) (Fin N) E) (h1 : IsUni B)
    (h2 : IsIntM L B) : cos L (u * B) ⊆ cos L u := by
  rintro v ⟨A, hA, hA', rfl⟩
  exact ⟨B * A, isUni_mul h1 hA, isIntM_mul L h2 hA', Matrix.mul_assoc _ _ _⟩

theorem cos_rowM (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E)
    (hc : ∀ j, j ≤ k → c j = 0) (hc' : ∀ j, c j ∈ L.O) : cos L (u * rowM k c) = cos L u := by
  refine (cos_mul_subset L u _ (isUni_rowM k c hc) (isIntM_rowM L k c hc')).antisymm ?_
  have : u = u * rowM k c * rowM k (-c) := by
    ext i j
    rw [mul_rowM, mul_rowM, mul_rowM, hc k le_rfl]
    simp
  conv_lhs => rw [this]
  exact cos_mul_subset L _ _ (isUni_rowM k _ fun j hj => by simp [hc j hj])
    (isIntM_rowM L k _ fun j => neg_mem (hc' j))

theorem exists_rep (L : LocE F E) (δ : E) (R : Set E)
    (hR : ∀ x : E, δ * x ∈ L.O → ∃ r ∈ R, r - x ∈ L.O)
    (u : Matrix (Fin N) (Fin N) E) (hu : IsUni u) (hδ : ∀ i j, δ * u i j ∈ L.O) (m : ℕ) :
    ∃ w : Matrix (Fin N) (Fin N) E, IsUni w ∧ (∀ i j, δ * w i j ∈ L.O) ∧ cos L w = cos L u ∧
      ∀ i j : Fin N, N ≤ i.val + m → i < j → w i j ∈ R := by
  induction m with
  | zero => exact ⟨u, hu, hδ, rfl, fun i j h _ => absurd i.2 (by omega)⟩
  | succ m ih =>
    obtain ⟨w, hw, hwδ, hc, hg⟩ := ih
    by_cases hm : N ≤ m
    · exact ⟨w, hw, hwδ, hc, fun i j _ h => hg i j (by omega) h⟩
    let k : Fin N := ⟨N - 1 - m, by omega⟩
    choose r hrR hr using fun j => hR (w k j) (hwδ k j)
    let c : Fin N → E := fun j => if k < j then r j - w k j else 0
    have hc0 : ∀ j, j ≤ k → c j = 0 := fun j hj => if_neg (not_lt.2 hj)
    have hc1 : ∀ j, c j ∈ L.O := fun j => by
      simp only [c]
      split_ifs
      exacts [hr j, zero_mem _]
    refine ⟨w * rowM k c, isUni_mul hw (isUni_rowM k c hc0), fun i j => ?_,
      (cos_rowM L w k c hc0 hc1).trans hc, fun i j h hij => ?_⟩
    · rw [mul_rowM, mul_add, ← mul_assoc]
      exact add_mem (hwδ i j) (mul_mem (hwδ i k) (hc1 j))
    · rw [mul_rowM]
      by_cases hik : i = k
      · subst hik
        rw [hw.2, one_mul]
        simp only [c, if_pos hij]
        simpa using hrR j
      · have h2 : i.val ≠ N - 1 - m := fun h => hik (Fin.ext h)
        have h3 : k < i := by
          show N - 1 - m < i.val
          omega
        rw [hw.1 i k h3, zero_mul, add_zero]
        exact hg i j (by omega) hij

theorem encard_le (L : LocE F E) (δ : L.O) (hδ : IsUnit (δ : E))
    [Finite (L.O ⧸ Ideal.span {δ})] (N : ℕ) :
    {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, (δ : E) * u i j ∈ L.O) ∧
      C = cos L u}.encard ≤
      ((Nat.card (L.O ⧸ Ideal.span {δ}) ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) := by
  obtain ⟨d, hd⟩ := hδ
  let ρ : (L.O ⧸ Ideal.span {δ}) → E := fun q => (d⁻¹ : Eˣ) * (Quotient.out q : L.O)
  have hR : ∀ x : E, (δ : E) * x ∈ L.O → ∃ r ∈ Set.range ρ, r - x ∈ L.O := by
    intro x hx
    let y : L.O := ⟨_, hx⟩
    refine ⟨_, ⟨Ideal.Quotient.mk _ y, rfl⟩, ?_⟩
    have h1 : Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) - y ∈ Ideal.span {δ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : ((Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) : L.O) : E)
        = (a : E) * d + d * x := by
      have := congrArg (Subtype.val) ha
      push_cast at this
      rw [hd, this]
      simp [y]
    have h3 : ρ (Ideal.Quotient.mk _ y) - x = a := by
      simp only [ρ]
      rw [h2]
      have := d.inv_mul
      linear_combination ((a : E) + x) * this
    rw [h3]
    exact a.2
  let P := {p : Fin N × Fin N // p.1 < p.2}
  let mk : (P → L.O ⧸ Ideal.span {δ}) → Matrix (Fin N) (Fin N) E := fun f =>
    Matrix.of fun i j => if h : i < j then ρ (f ⟨(i, j), h⟩) else if i = j then 1 else 0
  have hsub : {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧
      (∀ i j, (δ : E) * u i j ∈ L.O) ∧ C = cos L u} ⊆ (fun f => cos L (mk f)) '' Set.univ := by
    rintro C ⟨u, hu, huδ, rfl⟩
    obtain ⟨w, hw, -, hc, hg⟩ := exists_rep L δ _ hR u hu huδ N
    choose f hf using fun p : P => hg p.1.1 p.1.2 (by omega) p.2
    refine ⟨f, trivial, ?_⟩
    rw [← hc]
    show cos L (mk f) = _
    congr 1
    ext i j
    simp only [mk, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hf ⟨(i, j), h1⟩
    · rw [h2, hw.2]
    · exact (hw.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans (le_of_eq ?_))
  have hP : Nat.card P = N * (N - 1) / 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
      Fintype.card_fin, Nat.choose_two_right]
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, hP]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  have : Finite (𝒪[F] ⧸ Ideal.span {ϖ}) := by
    rw [← h.maximalIdeal_eq]
    exact inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

end GlobalTheory.HL.UniCount

theorem GlobalTheory.HL.encard_uniCosets_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (δ : E), δ ∈ L.O → IsUnit δ → ∀ N : ℕ, ({C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}}.encard : ℝ≥0∞) ≤ (resQ ϖ : ℝ≥0∞) ^ ((vE L ϖ (δ * L.cj δ)).toNat * (N * (N - 1) / 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ hu N
  have hc := (GlobalTheory.UnramCard.card_quot_eq_pow L ϖ hϖ ⟨δ, hδ⟩ hu).2
  have hfin : Finite (L.O ⧸ Ideal.span {(⟨δ, hδ⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (UniCount.resQ_ne_zero ϖ hϖ))
  have h := UniCount.encard_le L ⟨δ, hδ⟩ hu N
  rw [hc, ← pow_mul] at h
  have h2 := ENat.toENNReal_le.2 h
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h2
  exact h2
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.definite_unitary_stabilizer_subspace_prod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ U : Submodule K V, ∃ φ : MulAction.stabilizer (isom h) U ≃* isom (hRes h U) × isom (hRes h (perp h U)), ∀ (γ : MulAction.stabilizer (isom h) U) (L : Submodule (𝓞 K) V), latIn U (γ • L) = (φ γ).1 • latIn U L ∧ latIn (perp h U) (γ • L) = (φ γ).2 • latIn (perp h U) L := by
  first | exact @GlobalTheory.Mass.StabSplit.main | exact GlobalTheory.Mass.StabSplit.main | (intros; apply GlobalTheory.Mass.StabSplit.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.FrameTuple

section Alg
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}

def tup (t : E) (g g' : Fin m → V) : Fin m ⊕ Fin m → V := Sum.elim g fun b => t • (g' b - g b)

theorem tup_indep {t θ : E} (h : θ * t = 1) {g g' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) : LinearIndependent E (tup t g g') := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have key := hli (Sum.elim (fun a => c (Sum.inl a) - t * c (Sum.inr a)) fun b => t * c (Sum.inr b))
    (by
      rw [← hc]
      simp only [Fintype.sum_sum_type, tup, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [sub_smul, smul_sub, smul_smul, mul_comm t]
      abel)
  have h2 : ∀ b, c (Sum.inr b) = 0 := fun b => by
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    linear_combination θ * this - c (Sum.inr b) * h
  rintro (a | b)
  · have := key (Sum.inl a)
    simpa [h2] using this
  · exact h2 b

theorem tup_span {t θ : E} (h : θ * t = 1) (g g' : Fin m → V) :
    Submodule.span E (Set.range (tup t g g')) = Submodule.span E (Set.range (Sum.elim g g')) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl b, rfl⟩))
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have : Sum.elim g g' (Sum.inr b) = tup t g g' (Sum.inl b) + θ • tup t g g' (Sum.inr b) := by
        simp [tup, smul_smul, h]
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))

theorem tup_change (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by
  rcases j with j | j
  · simp [tup, Fintype.sum_sum_type, hp]
  · simp only [tup, Fintype.sum_sum_type, hp, hp', Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.smul_sum, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    module

theorem det_uni (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) :
    s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem comb_mul (g : Fin m → V) (s A : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    ∑ i, A i j • ∑ l, s l i • g l = ∑ l, (s * A) l j • g l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem gram_unit (L : LocE F E) [IsArtinianRing E] {n m : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) (x : Fin m → Fin n → E) (hli : LinearIndependent E x)
    (hd : Disjoint (Submodule.span E (Set.range x)) (perp L H (Submodule.span E (Set.range x)))) :
    IsUnit (gramT L H x).det := by
  have hinj : Function.Injective (Matrix.toLin' (gramT L H x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro α hα
    have h1 : ∑ i, α i • x i = 0 := by
      refine Submodule.disjoint_def.1 hd _ ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩) ?_
      rw [FrameBasic.mem_perp_span L h]
      intro j
      change FrameBasic.hfL L H (x j) _ = 0

      rw [map_sum]
      refine Eq.trans ?_ (congrFun hα j)
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gramT, Matrix.of_apply, map_smul,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h1 i
  have hb := IsArtinian.bijective_of_injective_endomorphism _ hinj
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_toLin'_iff]
  exact (Module.End.isUnit_iff _).2 hb

theorem isLat_std (L : LocE F E) (n : ℕ) :
    IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin n → E))) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := FrameOnto.unipotent_onto L r k S
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (2 * r + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have hθ : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hspan : Submodule.span E (Set.range (tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm)) = S.ME := by
    rw [e.symm.surjective.range_comp, tup_span hθ, hME]
  refine ⟨tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm, ?_, hspan, rfl, isLat_std L _, fun _ => rfl, ?_⟩
  · refine gram_unit L S.herm.1 _ ((tup_indep hθ hli).comp _ e.symm.injective) ?_
    rw [hspan]
    exact hco.disjoint
  · rintro C ⟨n, hn, n', hn', rfl⟩ p ⟨A, A', -, -, h0, h1, -, hp, hp'⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hN n hn
    obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := hN' n' hn'
    simp only [hs, hs', comb_mul] at hp hp'
    refine ⟨tup (algebraMap F E S.th⁻¹) p.1 p.2 ∘ e.symm,
      (Matrix.fromBlocks (s * A) (algebraMap F E S.th⁻¹ • (s' * A' - s * A)) 0 (s' * A')).submatrix
        e.symm e.symm, ?_, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul,
        det_uni s hs0 hs1, det_uni s' hs0' hs1', det_uni A (fun i j h => (h0 i j h).1) fun i => (h1 i).1,
        det_uni A' (fun i j h => (h0 i j h).2) fun i => (h1 i).2]
      simp
    · funext j
      rw [Function.comp_apply, tup_change _ S.f S.f' p.1 p.2 _ _ hp hp', rmul]
      exact (e.symm.sum_comp _).symm
    · rw [e.symm.surjective.range_comp, tup, Set.Sum.elim_range]
      rfl

end GlobalTheory.HL.FrameTuple
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.datum_stabilizer_between_lattice_stabilizers : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.H0 ⊓ stabL L Λ ≤ S.H0 ⊓ MulAction.stabilizer S.GLV d ∧ ∃ Λ₂ : Submodule L.O S.V, IsLat L Λ₂ ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d ≤ S.H0 ⊓ stabL L Λ₂ := by
  first | exact @GlobalTheory.HL.DatumStab.main | exact GlobalTheory.HL.DatumStab.main | (intros; apply GlobalTheory.HL.DatumStab.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) → IsIntM L (cT L u * S.Zh * u') → ∀ Δ : E, Δ = ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) → Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧ ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
  first | exact @GlobalTheory.OrbitDenom.main | exact GlobalTheory.OrbitDenom.main | (intros; apply GlobalTheory.OrbitDenom.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_double_coset_term_basic_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  first | exact @GlobalTheory.HL.TermBasic.term_basic | exact GlobalTheory.HL.TermBasic.term_basic | (intros; apply GlobalTheory.HL.TermBasic.term_basic <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_frameUnipotent_exchanging_dual_isotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  first | exact @GlobalTheory.FrameDual.exists_unip_change_dual | exact GlobalTheory.FrameDual.exists_unip_change_dual | (intros; apply GlobalTheory.FrameDual.exists_unip_change_dual <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  first | exact @GlobalTheory.FrameGram.main | exact GlobalTheory.FrameGram.main | (intros; apply GlobalTheory.FrameGram.main <;> assumption)
end
