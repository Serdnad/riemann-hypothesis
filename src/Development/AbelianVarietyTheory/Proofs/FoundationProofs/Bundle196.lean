module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TwistedSelmerCompare

theorem isSSRep_map_iff {Γ K L : Type} [Group Γ] [Field K] [Field L] [CharZero K] [CharZero L] (f : K →+* L)
    {a : ℕ} (ρ : Γ →* GL (Fin a) K) : IsSSRep (mapRep f ρ) ↔ IsSSRep ρ :=
  ⟨fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ K a ρ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).1 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ L a _ h)),
    fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ L a _ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).2 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ K a ρ h))⟩

section Param

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem speh_twist (p : Part A.CG) (χ : A.CG 1) (w : PlE H) (c : ℂ) (hp : A.unr (A.locG p.π w))
    (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (spehLoc N A p w) ∧ A.unr (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) ∧
      A.frobEig (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) = (A.frobEig (spehLoc N A p w)).map (· * c) := by
  have hd := A.locG_dim χ w
  have hp' : A.unr (A.locG (A.tw p.π χ) w) := by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ
  have he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c) := by
    rw [A.locG_tw]; exact A.frobEig_char _ _ c hp hχ hd hc
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3,
      A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    funext x
    simp only [Function.comp_apply]
    ring

theorem iso_twist (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) (c : ℂ)
    (hS : ∀ p ∈ S, A.unr (A.locG p.π w)) (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (isoLoc N A S w) ∧ A.unr (isoLoc N A (twistIso N A S χ) w) ∧
      A.frobEig (isoLoc N A (twistIso N A S χ) w) = (A.frobEig (isoLoc N A S w)).map (· * c) := by
  induction S with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩
  | cons p S ih =>
    obtain ⟨i1, i2, i3⟩ := ih fun q hq => hS q (List.mem_cons_of_mem _ hq)
    obtain ⟨j1, j2, j3⟩ := speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc
    change A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧
      A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧
      A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) =
        (A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A S w))).map (· * c)
    refine ⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add (f := _)]

theorem galPol_twist (S : List (Part A.CG)) (t : ℝ) : ∀ᶠ w in Filter.cofinite,
    galPol A (A.lpTw (A.lpChar (isoLoc N A S w) (A.locG A.etaTinv w)) t) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A S A.etaTinv) w) t) := by
  have h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w) :=
    (Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π
  filter_upwards [h] with w hw
  have hχ := (A.etaTinv_def w).1
  have hd := A.locG_dim A.etaTinv w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)
  obtain ⟨i1, i2, i3⟩ := iso_twist N A S _ w c hw hχ hc
  unfold galPol
  rw [A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]

theorem splitOut_ae (a : N.Loc) : ∀ᶠ w in Filter.cofinite, (SplitOut N a w ↔ IsSplitPl H w) := by
  have h1 : (placesOver H.E (N.l a)).Finite := by
    have h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (N.lPrime a).out.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    simpa [Ideal.dvd_span_singleton, placesOver] using hv
  filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem,
    (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3
  exact ⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩

end Param

variable (D : D7)

theorem triple_iff (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG))
    (h : HasParamW D.nd D.naut a σ Sg) (s : TwistedTriples.Trip D a) : TwistedTriples.IsTripleOf D a σ s ↔ IsTriple D a s Sg := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    rw [← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]
    have : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    rw [this]
  · refine Filter.eventually_congr ?_
    filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2
    rw [h2]
    refine forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]
    rfl

theorem allTriples_of_tripAll (h : TwistedTriples.TripAll D) : AllTriples D := fun a σ Sg hg hp =>
  (h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs

end GlobalTheory.TwistedSelmerCompare

end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.HarmonicParam

variable {p q : ℕ}

theorem card_filter_sum (P : Ix p q → Prop) [DecidablePred P] (A : Finset (Fin p)) (B : Finset (Fin q))
    (hA : ∀ i, P (Sum.inl i) ↔ i ∈ A) (hB : ∀ j, P (Sum.inr j) ↔ j ∈ B) :
    (Finset.univ.filter P).card = A.card + B.card := by
  rw [← Finset.card_disjSum]
  congr 1
  ext x
  cases x <;> simp [hA, hB]

theorem rhoNC_of_strictAnti (lam : Ix p q → ℚ) (h1 : StrictAnti fun i => lam (Sum.inl i))
    (h2 : StrictAnti fun j => lam (Sum.inr j)) (h3 : ∀ i j, lam (Sum.inr j) < lam (Sum.inl i)) :
    (∀ i : Fin p, rhoNC lam (Sum.inl i) = (q : ℚ) / 2 - ((p : ℚ) - 1 - 2 * (i.1 : ℚ)) / 2) ∧
    (∀ j : Fin q, rhoNC lam (Sum.inr j) = -(p : ℚ) / 2 - ((q : ℚ) - 1 - 2 * (j.1 : ℚ)) / 2) := by
  have h1' : ∀ i i', lam (Sum.inl i) < lam (Sum.inl i') ↔ i' < i := fun i i' => h1.lt_iff_gt
  have h2' : ∀ i i', lam (Sum.inr i) < lam (Sum.inr i') ↔ i' < i := fun i i' => h2.lt_iff_gt
  have h4 : ∀ i j, ¬ lam (Sum.inl i) < lam (Sum.inr j) := fun i j => (h3 i j).not_gt
  constructor
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ Finset.univ (by simp [sameBlock]) (by simp [sameBlock, h3]),
      card_filter_sum _ ∅ ∅ (by simp [sameBlock]) (by simp [sameBlock, h4]),
      card_filter_sum _ (Finset.Ioi i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock]),
      card_filter_sum _ (Finset.Iio i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock])]
    have hi : i.1 + 1 ≤ p := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ ∅ (by simp [sameBlock, h4]) (by simp [sameBlock]),
      card_filter_sum _ Finset.univ ∅ (by simp [sameBlock, h3]) (by simp [sameBlock]),
      card_filter_sum _ ∅ (Finset.Ioi i) (by simp [sameBlock]) (by simp [sameBlock, h2']),
      card_filter_sum _ ∅ (Finset.Iio i) (by simp [sameBlock]) (by simp [sameBlock, h2'])]
    have hi : i.1 + 1 ≤ q := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

theorem hcParam_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) →
    IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧
    ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  intro p q n hn ap am hap ham _ _
  have hn' : (p : ℚ) + q + 1 ≤ n := by exact_mod_cast hn
  have h1 : StrictAnti fun i => hcParam n ap am (Sum.inl i) := by
    intro i j hij
    have a : (ap j : ℚ) ≤ ap i := by exact_mod_cast hap hij.le
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h2 : StrictAnti fun i => hcParam n ap am (Sum.inr i) := by
    intro i j hij
    have a : (am i.rev : ℚ) ≤ am j.rev := by exact_mod_cast ham (Fin.rev_le_rev.2 hij.le)
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h3 : ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
    intro i j
    have a : (0 : ℚ) ≤ ap i := Nat.cast_nonneg _
    have b : (0 : ℚ) ≤ am j.rev := Nat.cast_nonneg _
    have c : (0 : ℚ) ≤ j.1 := Nat.cast_nonneg _
    have d : (i.1 : ℚ) + 1 ≤ p := by exact_mod_cast i.2
    simp only [hcParam]
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h3⟩
  · rintro (a | a) (b | b) h
    · rw [h1.injective h]
    · exact absurd h (h3 a b).ne'
    · exact absurd h (h3 b a).ne
    · rw [h2.injective h]
  · rintro (a | a) (b | b) h
    · exact h1 h
    · exact h.elim
    · exact h.elim
    · exact h2 h
  · rintro (a | a)
    · exact ⟨2 * (ap a) + 2 * (p - (a.1 + 1)) + (n - p - q + 1), by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-2 * (am a.rev) - 2 * (a.1 + 1) - (n - p - q - 1), by simp only [hcParam]; push_cast; ring⟩
  · rintro (a | a) (b | b)
    · exact ⟨ap a - ap b - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨ap a + (p - (a.1 + 1)) + am b.rev + (b.1 + 1) + (n - p - q),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-(ap b + (p - (b.1 + 1)) + am a.rev + (a.1 + 1) + (n - p - q)),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨am b.rev - am a.rev - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
  · obtain ⟨r1, r2⟩ := rhoNC_of_strictAnti _ h1 h2 h3
    funext a
    rcases a with a | a
    · simp only [blattner, r1, hcParam, wtK]
      ring
    · simp only [blattner, r2, hcParam, wtK]
      ring

end GlobalTheory.HarmonicParam
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.KilledByLowerStable

theorem act_eq_zero_of_lower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) (hx : KilledByLower act x) (Y : Mat p q)
    (h1 : ∀ (a : Fin p) (j : Ix p q), Y (Sum.inl a) j = 0)
    (h2 : ∀ (i : Ix p q) (b : Fin q), Y i (Sum.inr b) = 0) : act Y x = 0 := by
  have hY : Y = ∑ i, ∑ j, Y i j • Eab i j := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Eab, Matrix.smul_single]
  rw [hY]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases i with a | b
  · rw [h1, zero_smul]
  · rcases j with a | b'
    · rw [hx a b, smul_zero]
    · rw [h2, zero_smul]

theorem killedByLower_act : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z →
    ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  intro p q V _ _ act hact Z hZ x hx a b
  have h := congrArg (fun f : Module.End ℂ V => f x) (hact (Eab (Sum.inr b) (Sum.inl a)) Z)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx a b, map_zero, sub_zero] at h
  rw [← h]
  apply act_eq_zero_of_lower act x hx
  · intro a' j
    have h0 : Z (Sum.inl a') (Sum.inr b) = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hj : j = Sum.inl a
    · subst hj
      simp [Eab, h0]
    · simp [Eab, hj]
  · intro i b'
    have h0 : Z (Sum.inl a) (Sum.inr b') = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hi : i = Sum.inr b
    · subst hi
      simp [Eab, h0]
    · simp [Eab, hi]

end GlobalTheory.KilledByLowerStable
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockUniq

theorem genSub_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (N : Submodule ℂ V)
    (h1 : S ⊆ N) (h2 : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S := by
  intro x hx
  simp only [genSub, SetLike.mem_coe, Submodule.mem_sInf]
  exact fun N hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V)
    (hy : y ∈ genSub act S) : act Z y ∈ genSub act S := by
  simp only [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  intro p q n T0 T1 T2 F M₁ W M I e₀ v₀ hgen hK hirr hM he hv hI
  refine ⟨?_, ?_, ?_⟩
  · intro io hio h0
    have h1 : ∀ v, io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := by
      let N : Submodule ℂ M.V := LinearMap.eqLocus (io ∘ₗ TensorProduct.mk ℂ W M.V e₀)
        (I ∘ₗ TensorProduct.mk ℂ M₁.V M.V e₀)
      have hN : ∀ v, v ∈ N ↔ io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
      rcases hM.2 N (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hio.2, ← hI.2, hy]) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (hN v₀).2 h0)) hv
      · intro v
        exact (hN v).1 (h ▸ Submodule.mem_top)
    refine TensorProduct.ext' fun e v => ?_
    let N : Submodule ℂ W := LinearMap.eqLocus (io ∘ₗ (TensorProduct.mk ℂ W M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v ∘ₗ W.subtype)
    have hN : ∀ e, e ∈ N ↔ io (e ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
    have hst : KStable M₁.act (N.map W.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      refine ⟨⟨M₁.act Z w, hK Z hZ w w.2⟩, ?_, rfl⟩
      have hw' := (hN w).1 hw
      refine (hN _).2 ?_
      rw [← hio.1 Z hZ w _ v rfl, hw', hI.1]
    have h0' : (e₀ : M₁.V) ∈ N.map W.subtype := ⟨e₀, (hN e₀).2 (h1 v), rfl⟩
    rcases hirr _ (Submodule.map_subtype_le W N) hst with h | h
    · rw [h, Submodule.mem_bot] at h0'
      exact absurd (Subtype.ext h0') he
    · have : (e : M₁.V) ∈ N.map W.subtype := by rw [h]; exact e.2
      obtain ⟨e', he', hee⟩ := this
      have : e' = e := Subtype.ext hee
      subst this
      simpa using (hN e').1 he'
  · intro I' hI' hW
    refine TensorProduct.ext' fun x v => ?_
    let N : Submodule ℂ M₁.V := LinearMap.eqLocus (I' ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
    have hN : ∀ e, e ∈ N ↔ I' (e ⊗ₜ v) = I (e ⊗ₜ v) := fun v => Iff.rfl
    have := genSub_le M₁.act (W : Set M₁.V) N (fun w hw => (hN w).2 (hW ⟨w, hw⟩ v))
      (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hI'.1, ← hI.1, hy])
    rw [hgen] at this
    exact (hN x).1 (this Submodule.mem_top)
  · intro v
    let f : M₁.V →ₗ[ℂ] Pol p q n 0 := I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v
    have hf : ∀ x, f x = I (x ⊗ₜ v) := fun x => rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have := genSub_le M₁.act (W : Set M₁.V)
        ((genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v))).comap f)
        (fun w hw => subset_genSub F.act1 _ ⟨⟨w, hw⟩, rfl⟩)
        (fun Z y hy => by
          rw [Submodule.mem_comap, hf] at hy ⊢
          rw [← hI.1]
          exact genSub_stable _ _ _ _ hy)
      rw [hgen] at this
      exact this (Submodule.mem_top : x ∈ ⊤)
    · have := genSub_le F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) (LinearMap.range f)
        (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
        (by rintro Z _ ⟨x, rfl⟩; exact ⟨M₁.act Z x, by rw [hf, hf, hI.1]⟩)
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩

end GlobalTheory.FockUniq
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem normSq_hcParam_sub_rhoSq (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  have hr : rhoSq (p + q) = ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2
      + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    unfold rhoSq
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2) p,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) + q - 1) / 2 - (i : ℕ)) ^ 2) q,
      Nat.add_comm p q, Finset.sum_range_add, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> push_cast <;> ring
  rw [hr]
  unfold normSq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin p, hcParam n ap am (Sum.inl i) ^ 2
      = ∑ i : Fin p, wtK n ap am (Sum.inl i) ^ 2
        + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ))
        + ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  have h2 : ∑ j : Fin q, hcParam n ap am (Sum.inr j) ^ 2
      = ∑ j : Fin q, wtK n ap am (Sum.inr j) ^ 2
        + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))
        + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  rw [h1, h2]
  ring

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.conjugate_modularFamily_along_separatingFamily : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  first | exact @GlobalTheory.FN.conj_family_sep | exact GlobalTheory.FN.conj_family_sep | (intros; apply GlobalTheory.FN.conj_family_sep <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  first | exact @GlobalTheory.NeedB.tsen | exact GlobalTheory.NeedB.tsen | (intros; apply GlobalTheory.NeedB.tsen <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 2 ^ 12 ≤ g → (mass g N fun f => ¬ RootsApart g N f) ≤ 23 * Real.log g / Real.sqrt g := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsApart_le | exact GlobalTheory.BadShare.mass_not_rootsApart_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsApart_le <;> assumption)
end
