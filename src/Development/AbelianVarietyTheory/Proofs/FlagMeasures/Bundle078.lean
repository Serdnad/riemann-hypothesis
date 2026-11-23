module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle059
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle069
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem exists_lift_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a l hl
  obtain ⟨c, hc, hσ, hlw⟩ := hl
  have hσ' : σ c = -c := hσ
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a 0 c ?_ ?_ ?_ hc
    · intro b _
      simp [form]
    · simp [form, hσ']
    · intro b _
      simp
  have hE : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c) w i j =
      (if i = j then 1 else 0) +
        (if j = esI k r a then (if i = eI k r a then (s a : ℂ) * ((s a : ℂ) * w.embedding c) else 0) else 0) := by
    intro w i j
    have h0 : (A w *ᵥ fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
      have h1 : (fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
        funext l
        simp
      rw [h1, mulVec_zero]
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a 0 c w i j, h0]
    simp [herm]
  have hne : ∀ b b' : Fin r, eI k r b ≠ esI k r b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [eI, esI] at this
    omega
  have hnw : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, esI] at this
    omega
  have hnw' : ∀ (j : Fin (k + 1)) (b : Fin r), eI k r b ≠ wI k r j := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, eI] at this
    omega
  have hee : ∀ b b' : Fin r, b ≠ b' → eI k r b ≠ eI k r b' := by
    intro b b' hb h
    apply hb
    have := congrArg Fin.val h
    simp only [eI] at this
    exact Fin.ext this
  have hss : ∀ b b' : Fin r, esI k r b = esI k r b' → b = b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [esI] at this
    exact Fin.ext (by omega)
  constructor
  · intro w
    show ((gM A _ w) (eI k r a) (esI k r a)).im = l w
    rw [hE, hlw w]
    simp [hne a a, pow_two, mul_assoc, Complex.mul_im]
  · rintro (p | b | p | b) hβ _ w
    · show (gM A _ w) (eI k r p.1.1) (eI k r p.1.2) = 0
      rw [hE]
      have h1 : eI k r p.1.1 ≠ eI k r p.1.2 := hee _ _ (ne_of_lt p.2)
      simp [h1, (hne p.1.2 a)]
    · funext j
      show (gM A _ w) (eI k r b) (wI k r j) = 0
      rw [hE]
      simp [hnw' j b, hnw j a]
    · show (gM A _ w) (eI k r p.1.1) (esI k r p.1.2) = 0
      rw [hE]
      have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      by_cases h2 : p.1.2 = a
      · have h3 : eI k r p.1.1 ≠ eI k r a := hee _ _ (h2 ▸ h1)
        simp [hne p.1.1 p.1.2, h3]
      · have h3 : esI k r p.1.2 ≠ esI k r a := fun h => h2 (hss _ _ h)
        simp [hne p.1.1 p.1.2, h3]
    · show ((gM A _ w) (eI k r b) (esI k r b)).im = 0
      rw [hE]
      have hb : b ≠ a := fun h => hβ (by rw [h])
      have h3 : esI k r b ≠ esI k r a := fun h => hb (hss _ _ h)
      simp [hne b b, h3]

end GlobalTheory.SnMass.VolN
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.SkewVol
theorem dom_of_basis {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Finite ι]
    (b : Module.Basis ι ℝ W) (v : W) :
    ∃! l, l ∈ (Submodule.span ℤ (Set.range b) : Set W) ∧ v + l ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨⟨l, hl⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
  refine ⟨l, ⟨hl, by simpa [Submodule.vadd_def, add_comm] using h1⟩, ?_⟩
  rintro l' ⟨hl', h'⟩
  have := h2 ⟨l', hl'⟩ (by simpa [Submodule.vadd_def, add_comm] using h')
  simpa using congrArg Subtype.val this

theorem dInv_ne_zero (K : Type) [Field K] [NumberField K] (j : ℕ) : dInv K j ≠ 0 := by
  unfold dInv
  refine pow_ne_zero _ (inv_ne_zero ?_)
  exact FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem skew_covol_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  intro F E _ _ _ _ _ σ hCM hU t c hc
  have hTC : IsTotallyComplex E := hCM.2.1
  have hTR : IsTotallyReal F := hCM.1
  have hσw : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hCM.2.2.2 w.embedding x
  have hre : ∀ x : E, reV (σ x) = reV x := fun x => funext fun w => by simp [reV, hσw]
  have him : ∀ x : E, imV (σ x) = -imV x := fun x => funext fun w => by simp [imV, hσw]
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex E hTC
  obtain ⟨ι, _, b, hbs, hbv⟩ := GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving E volume e he (Units.mk0 (dInv E (2 * t)) (dInv_ne_zero E _))
  obtain ⟨e1, he1, he1x⟩ := GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords F E σ hCM
  obtain ⟨ι1, _, b1, hb1s, hb1v⟩ :=
    GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving F volume e1 he1 (Units.mk0 (dInv F (2 * t)) (dInv_ne_zero F _))
  simp only [Units.val_mk0] at hbs hbv hb1s hb1v
  set Λ := Submodule.span ℤ (Set.range b) with hΛdef
  have hΛ : ∀ p, p ∈ Λ ↔ ∃ x ∈ dInv E (2 * t), (reV x, imV x) = p := by
    intro p
    rw [← SetLike.mem_coe, hbs]
    simp [hex]
  have hL1 : ∀ a, a ∈ (Submodule.span ℤ (Set.range b1) : Set (InfinitePlace E → ℝ)) ↔
      (a, (0 : InfinitePlace E → ℝ)) ∈ Λ := by
    intro a
    rw [hb1s, hΛ]
    simp only [Set.mem_image, Set.mem_setOf_eq, he1x, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU (2 * t) (algebraMap F E y)).2 ⟨y, hy, rfl⟩
      exact ⟨_, h.1, rfl, h.2⟩
    · rintro ⟨x, hx, rfl, h0⟩
      obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU _ _).1 ⟨hx, h0⟩
      exact ⟨y, hy, rfl⟩
  have hD1 : ∀ a, ∃! l, l ∈ {a : InfinitePlace E → ℝ | (a, (0 : InfinitePlace E → ℝ)) ∈ Λ.toAddSubgroup} ∧
      a + l ∈ ZSpan.fundamentalDomain b1 := by
    intro a
    obtain ⟨l, hl, hu⟩ := dom_of_basis b1 a
    exact ⟨l, ⟨(hL1 l).1 hl.1, hl.2⟩, fun l' hl' => hu l' ⟨(hL1 l').2 hl'.1, hl'.2⟩⟩
  have h2 : ∀ a y, (a, y) ∈ Λ → ((0 : InfinitePlace E → ℝ), (2 : ℝ) • y) ∈ Λ := by
    intro a y hay
    obtain ⟨x, hx, hxe⟩ := (hΛ _).1 hay
    rw [Prod.mk.injEq] at hxe
    refine (hΛ _).2 ⟨x - σ x, Submodule.sub_mem (dInv E (2 * t) : Submodule (𝓞 E) E) hx (GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx), ?_⟩
    have h1 : reV (x - σ x) = reV x - reV (σ x) := funext fun w => by simp [reV]
    have h1' : imV (x - σ x) = imV x - imV (σ x) := funext fun w => by simp [imV]
    rw [h1, h1', hre, him, ← hxe.2]
    refine Prod.ext ?_ ?_
    · simp
    · funext w; simp; ring
  have hsp : Submodule.span ℝ (Λ : Set ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ))) = ⊤ := by
    rw [hΛdef, Submodule.span_span_of_tower, b.span_eq]
  obtain ⟨D2, hD2m, hD2⟩ := GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' Λ hsp h2
  have hprod := GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension Λ.toAddSubgroup _ D2 hD1 hD2
  have heq := GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable ((volume : Measure (InfinitePlace E → ℝ)).prod (volume : Measure (InfinitePlace E → ℝ))) Λ _ _ ((ZSpan.fundamentalDomain_measurableSet b1).prod hD2m)
    (ZSpan.fundamentalDomain_measurableSet b) hprod (dom_of_basis b)
  rw [Measure.prod_prod, ← Measure.volume_eq_prod, hbv, hb1v] at heq
  have hL2 : ∀ y, (∃ a, (a, y) ∈ Λ) ↔ ∃ x ∈ dInv E (2 * t), imV x = y := by
    intro y
    simp only [hΛ, Prod.mk.injEq]
    constructor
    · rintro ⟨a, x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, x, hx, rfl, rfl⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' F E σ hCM hU
  have hfin := GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts F E σ hCM (dInv E (2 * t)) (fun x hx => GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx) θ hθ c hc D2 _
    hD2m (fun y => by simpa only [Set.mem_setOf_eq, hL2] using hD2 y) rfl
  have hd : (1 : ℝ) ≤ |(discr F : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero F)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hnc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h
    exact h.symm
  have hnr : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension F E σ hCM hU, hnc, hnr] at heq
  rw [GlobalTheory.T.covolumeQuotient_ofReal_identity _ c _ t _ hd hc heq.symm] at hfin
  exact hfin

end GlobalTheory.SnMass.SkewVol
end
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_eq_sum_tail {α : Type} [Fintype α] {m : ℕ} (S : Set (Fin (m + 1) → α))
    (T : Set (Fin m → α)) (h : ∀ X ∈ S, Fin.tail X ∈ T) :
    S.ncard = ∑ x ∈ T.toFinset, Set.ncard {y : α | (Fin.cons y x : Fin (m + 1) → α) ∈ S} := by
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := fun X => Fin.tail X) (t := T.toFinset)
      (by intro X hX; simpa using h X (by simpa using hX))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun y _ => (Fin.cons y x : Fin (m + 1) → α)) ?_ ?_ ?_
  · intro y hy
    simpa using hy
  · intro y _ y' _ hyy
    simpa using congrFun hyy 0
  · intro X hX
    simp only [Finset.mem_filter, Set.mem_toFinset] at hX
    obtain ⟨h1, rfl⟩ := hX
    exact ⟨X 0, by simpa using h1, by simp⟩

variable {B : Type} [CommRing B]

theorem tail_mem_sols (c : B →+* B) {m n : ℕ} (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (X : Fin (m + 1) → Fin n → B) (hX : X ∈ sols c n G) :
    Fin.tail X ∈ sols c n (G.submatrix Fin.succ Fin.succ) := by
  obtain ⟨⟨y, hy⟩, h2⟩ := hX
  refine ⟨⟨Fin.tail y, fun a b => ?_⟩, fun a b => h2 _ _⟩
  simpa [Fin.tail] using hy a.succ b.succ

theorem cons_mem_sols (c : B →+* B) (hc : ∀ u, c (c u) = u) {m n : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (hG : ∀ a b, c (G b a) = G a b)
    (x : Fin m → Fin n → B) (hx : x ∈ sols c n (G.submatrix Fin.succ Fin.succ))
    (y : Fin n → B) :
    (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G ↔
      Prim c (Fin.cons y x : Fin (m + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = G i.succ 0) ∧
        ip c y y = G 0 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by simpa using h2 i.succ 0, by simpa using h2 0 0⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simpa using h3
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [← cj_ip c hc, h2, hG]
    · simpa using h2 a
    · simpa using hx.2 a b

theorem pow_le_eta_mul {q m n : ℕ} (hq : 2 ≤ q) (h : 2 * m + 1 ≤ n) :
    (q : ℝ) ^ n ≤ (2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n - (2 * m + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : 2 * (2 * m + 1 + d) - (2 * m + 1) = (2 * m + 1 + d) + d := by omega
  have h2 : (2 : ℝ) ^ d ≤ (q : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) d
  have h3 : (2 : ℝ) ^ (2 * m + 1) / 2 ^ (2 * m + 1 + d) = 1 / 2 ^ d := by
    rw [pow_add (2 : ℝ) (2 * m + 1) d]; field_simp
  rw [h1, h3, pow_add (q : ℝ) (2 * m + 1 + d) d, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  gcongr

theorem eta_le {m n : ℕ} (h : 2 * m + 3 ≤ n) : (2 : ℝ) ^ (2 * m + 1) / 2 ^ n ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * m + 3) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 : ℝ) ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1) := by ring
  linarith

theorem ncard_sols_eta [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) (ω : B)
    (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (n m : ℕ) :
    2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) →
      (1 - 2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n * m - m ^ 2)
          ≤ (Set.ncard (sols c n G) : ℝ) ∧
        (Set.ncard (sols c n G) : ℝ)
          ≤ (1 + 2 * (2 ^ (2 * m + 1) / 2 ^ n)) * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  induction m with
  | zero =>
    intro _ G _
    have h1 : sols c n G = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact ⟨⟨x, fun a => a.elim0⟩, fun a => a.elim0⟩
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * 0 + 1) / 2 ^ n := by positivity
    rw [h1, Set.ncard_univ, Nat.card_unique]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsub_self,
      pow_zero, mul_one, Nat.cast_one] at h2 ⊢
    constructor <;> linarith
  | succ m ih =>
    intro hn G hG
    obtain ⟨i1, i2⟩ := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    have hη := eta_le (m := m) (n := n) (by omega)
    have hp := pow_le_eta_mul (m := m) (n := n) hq (by omega)
    have he : (2 : ℝ) ^ (2 * (m + 1) + 1) / 2 ^ n = 4 * (2 ^ (2 * m + 1) / 2 ^ n) := by ring
    have hx : 2 * n * (m + 1) - (m + 1) ^ 2 = (2 * n * m - m ^ 2) + (2 * n - (2 * m + 1)) := by
      have h1 : m ^ 2 ≤ 2 * n * m := by nlinarith
      have h2 : 2 * n * (m + 1) = 2 * n * m + 2 * n := by ring
      have h3 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      omega
    have hη0 : (0 : ℝ) ≤ 2 ^ (2 * m + 1) / 2 ^ n := by positivity
    rw [he, hx, pow_add (q : ℝ)]
    set η : ℝ := 2 ^ (2 * m + 1) / 2 ^ n
    set Q : ℝ := (q : ℝ) ^ (2 * n * m - m ^ 2) with hQ
    set R : ℝ := (q : ℝ) ^ (2 * n - (2 * m + 1)) with hR
    have hQ0 : 0 ≤ Q := by positivity
    have hR0 : 0 ≤ R := by positivity
    have key : ∀ x ∈ (sols c n (G.submatrix Fin.succ Fin.succ)).toFinset,
        (1 - 3 * η) * R ≤ (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ∧
          (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ≤ (1 + 3 * η) * R := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      have := GlobalTheory.T.card_primitiveTuple_extensions_le c hc ω hω hf q hq hB m n (by omega) x hx.1 (fun i => G i.succ 0)
        (G 0 0) (hG 0 0)
      simp only [cons_mem_sols c hc G hG x hx]
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    rw [ncard_eq_sum_tail _ _ (tail_mem_sols c G), Nat.cast_sum]
    rw [Set.ncard_eq_toFinset_card'] at i1 i2
    have k1 := Finset.card_nsmul_le_sum _ _ _ (fun x hx => (key x hx).1)
    have k2 := Finset.sum_le_card_nsmul _ _ _ (fun x hx => (key x hx).2)
    rw [nsmul_eq_mul] at k1 k2
    have hQR : 0 ≤ Q * R := mul_nonneg hQ0 hR0
    constructor
    · refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right i1
        (mul_nonneg (by linarith) hR0)) k1)
      nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hQR]
    · refine le_trans k2 (le_trans (mul_le_mul_of_nonneg_right i2
        (mul_nonneg (by linarith) hR0)) ?_)
      nlinarith [mul_nonneg (mul_nonneg hη0 (show 0 ≤ 1 / 4 - η by linarith)) hQR,
        mul_nonneg hη0 hQR]

theorem ncard_sols_residue : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  intro B _ _ c hc ω hω hf q hq hB m n hn G hG
  obtain ⟨h1, h2⟩ := ncard_sols_eta c hc ω hω hf q hq hB n m hn G hG
  have hη := eta_le hn
  have hQ : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n * m - m ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hη hQ
  constructor <;> nlinarith

end GlobalTheory.GramCount
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (P Q : Ideal (𝓞 E)), Q.IsMaximal → P ≤ Q → P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) → P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  first | exact @GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | exact GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | (intros; apply GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj <;> assumption)
end

section

namespace GlobalTheory

theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
end

section

open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory

theorem eq_of_inner_eq_on_dense_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by
  have h1 : ∀ y ∈ Submodule.span ℂ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, inner_add_left, hy, hz]
    | smul c y _ hy => rw [inner_smul_left, inner_smul_left, hy]
  have h2 : (fun y : E => ⟪y, a⟫_ℂ) = fun y => ⟪y, b⟫_ℂ :=
    Continuous.ext_on hs (by fun_prop) (by fun_prop) h1
  exact ext_inner_left ℂ fun y => congrFun h2 y

theorem exists_continuousMultilinearMap_of_inner_prod {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
  have hn : ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
    intro x
    have h := hin x x
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖t x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
      rw [← Finset.prod_pow]
      exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)
      two_ne_zero).1 h'
  have hu : ∀ [DecidableEq ι] (y x : ∀ v, H v) (i : ι) (a : H i),
      ⟪t y, t (Function.update x i a)⟫_ℂ =
        ⟪y i, a⟫_ℂ * ∏ j ∈ Finset.univ.erase i, ⟪y j, x j⟫_ℂ := by
    intro _ y x i a
    rw [hin, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  let m : MultilinearMap (RingHom.id ℂ) H E :=
    { toFun := t
      map_update_add' := by
        intro _ x i a b
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_add_right, hu, hu, hu, inner_add_right, add_mul]
      map_update_smul' := by
        intro _ x i c a
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [RingHom.id_apply, inner_smul_right, hu, hu, inner_smul_right, mul_assoc] }
  refine ⟨m.mkContinuous 1 fun x => ?_, fun x => rfl, hn⟩
  rw [one_mul]
  exact (hn x).le

theorem rowsAut_tens_continuousMultilinear :
    ∀ B : RowsAut, ∃ m : ContinuousMultilinearMap ℂ B.H B.Hs,
      (∀ x, m x = B.tens x) ∧ ∀ x, ‖B.tens x‖ = ∏ v, ‖x v‖ := fun B =>
  exists_continuousMultilinearMap_of_inner_prod B.tens B.tens_spec.1 B.tens_spec.2.2

end GlobalTheory
end
