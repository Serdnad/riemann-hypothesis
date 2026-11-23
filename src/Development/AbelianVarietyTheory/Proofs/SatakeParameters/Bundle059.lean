module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle056
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isoLoc_perm {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) :
    isoLoc N A Pa w = isoLoc N A Pa' w := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    simp only [isoLoc, List.foldr_cons] at ih ⊢
    rw [ih]
  | swap p q l =>
    simp only [isoLoc, List.foldr_cons]
    rw [← A.lpSum_assoc (spehLoc N A q w), A.lpSum_comm (spehLoc N A q w) (spehLoc N A p w), A.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locV_eq_of_pt (i : N.Loc) {P P' : A.AV i} {x : N.X i} (hx : A.ptV i P = some x)
    (hx' : A.ptV i P' = some x) {w : PlE H} (hso : SplitOut N i w) (hg : ∀ k, w ∉ placesOver H.E (H.g k))
    (hd : w ∉ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)) :
    A.locV i P w = A.locV i P' w := by
  set c : ℝ := (1 - (R.nV : ℝ)) / 2
  have u : A.unr (A.lpTw (A.locV i P w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P w hso.1 hso.2.2.2 hg hd)
  have u' : A.unr (A.lpTw (A.locV i P' w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P' w hso.1 hso.2.2.2 hg hd)
  have h1 := congrArg Polynomial.roots ((A.pt_loc i P x hx w hso).symm.trans (A.pt_loc i P' x hx' w hso))
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have e : A.lpTw (A.locV i P w) c = A.lpTw (A.locV i P' w) c := by
    rw [A.unr_eq_lpUnr _ u, A.unr_eq_lpUnr _ u', h1]
  have back : ∀ a : A.LP w, A.lpTw (A.lpTw a c) (-c) = a := fun a => by
    rw [A.lpTw_add, add_neg_cancel, A.lpTw_zero]
  rw [← back (A.locV i P w), e, back]

theorem locOfPt_of_splitBC : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  intro R H what₂ N A i hBC hS P P' x hx hx' w hw
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hd0 : (if N.l i = H.pde then H.pde' else H.pde) ≠ 0 := by
    split_ifs
    exacts [H.pde'_prime.ne_zero, H.pde_prime.ne_zero]
  have hfin : (placesOver H.E (N.l i) ∪ (N.S i : Set (PlE H)) ∪ (N.Q i : Set (PlE H)) ∪
      placesOver H.E (H.g 0) ∪ placesOver H.E (H.g 1) ∪
      placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)).Finite := by
    refine ((((( placesOver_finite_of_ne_zero _ _ (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet).union (placesOver_finite_of_ne_zero _ _ (H.g_prime 0).ne_zero)).union
      (placesOver_finite_of_ne_zero _ _ (H.g_prime 1).ne_zero)).union (placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl H v → A.locV i P v = A.locV i P' v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => locV_eq_of_pt N A i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  have hperm := hS P P' hev Pa Pa' hPa hPa'
  rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw]
  exact isoLoc_perm N A hperm w

end GlobalTheory.RowTie
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SpehRigid

def seg {C : Type} (p : C × ℕ) : Multiset (C × ℤ) :=
  (Multiset.range p.2).map fun a : ℕ => (p.1, (p.2 : ℤ) - 1 - 2 * (a : ℤ))

theorem seg_nodup {C : Type} (p : C × ℕ) : (seg p).Nodup := by
  refine (Multiset.nodup_range _).map ?_
  intro a b h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem mem_seg {C : Type} (p : C × ℕ) (c : C) (e : ℤ) :
    (c, e) ∈ seg p ↔ p.1 = c ∧ ∃ a : ℕ, a < p.2 ∧ (p.2 : ℤ) - 1 - 2 * (a : ℤ) = e := by
  simp only [seg, Multiset.mem_map, Multiset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨h1, a, ha, h2⟩
  · rintro ⟨h1, a, ha, h2⟩
    exact ⟨a, ha, h1, h2⟩

theorem count_seg {C : Type} [DecidableEq C] (p : C × ℕ) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (seg p).count (c, (d : ℤ) - 1) = (seg p).count (c, (d : ℤ) + 1) + if (c, d) = p then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (seg_nodup p), Multiset.count_eq_of_nodup (seg_nodup p)]
  obtain ⟨c', d'⟩ := p
  have e1 : (c, (d : ℤ) - 1) ∈ seg (c', d') ↔ c' = c ∧ d ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  have e2 : (c, (d : ℤ) + 1) ∈ seg (c', d') ↔ c' = c ∧ d + 2 ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d - 2) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  simp only [e1, e2, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    simp only [true_and]
    split_ifs <;> omega
  · simp [hc, Ne.symm hc]

theorem count_bind_seg {C : Type} [DecidableEq C] (P : Multiset (C × ℕ)) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (P.bind seg).count (c, (d : ℤ) - 1) = (P.bind seg).count (c, (d : ℤ) + 1) + P.count (c, d) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih =>
    rw [Multiset.cons_bind, Multiset.count_add, Multiset.count_add, ih, count_seg p c d hd, Multiset.count_cons]
    omega

theorem eq_of_bind_seg {C : Type} (P P' : Multiset (C × ℕ)) (h : ∀ p ∈ P, 1 ≤ p.2) (h' : ∀ p ∈ P', 1 ≤ p.2)
    (e : P.bind seg = P'.bind seg) : P = P' := by
  classical
  ext ⟨c, d⟩
  by_cases hd : 1 ≤ d
  · have h1 := count_bind_seg P c d hd
    have h2 := count_bind_seg P' c d hd
    rw [e] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hd (h _ hm),
      Multiset.count_eq_zero_of_notMem fun hm => hd (h' _ hm)]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def flat (p : Formalism.BasicNotions.Part A.CG) : List ((Σ a : ℕ, A.CG a) × ℝ) :=
  (List.range p.d).map fun k : ℕ => (⟨p.a, p.π⟩, ((p.d : ℝ) - 1) / 2 - (k : ℝ))

theorem twSum_append (L L' : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    GlobalTheory.RowTie.twSum N A (L ++ L') w = A.lpSum (GlobalTheory.RowTie.twSum N A L w) (GlobalTheory.RowTie.twSum N A L' w) := by
  unfold GlobalTheory.RowTie.twSum
  induction L with
  | nil => rw [List.nil_append, List.foldr_nil, A.lpSum_comm, A.lpSum_zero]
  | cons p L ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, A.lpSum_assoc]

theorem spehLoc_eq (p : Formalism.BasicNotions.Part A.CG) (w : PlE H) :
    spehLoc N A p w = GlobalTheory.RowTie.twSum N A (flat N A p) w := by
  unfold spehLoc GlobalTheory.RowTie.twSum flat
  have hl : (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = (List.range p.d).map (fun a : ℕ => (a : ℝ)) := by
    simp [List.map_eq_flatMap]
  rw [hl, List.foldr_map, List.foldr_map]

theorem isoLoc_eq (P : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) :
    isoLoc N A P w = GlobalTheory.RowTie.twSum N A (P.flatMap (flat N A)) w := by
  induction P with
  | nil => rfl
  | cons p P ih => rw [List.flatMap_cons, twSum_append, ← ih, ← spehLoc_eq]; rfl

def toPair (p : Formalism.BasicNotions.Part A.CG) : (Σ a : ℕ, A.CG a) × ℕ := (⟨p.a, p.π⟩, p.d)

theorem toPair_injective : Function.Injective (toPair N A) :=
  Function.LeftInverse.injective (g := fun q => ⟨q.1.1, q.1.2, q.2⟩) fun _ => rfl

theorem coe_flatMap (P : List (Formalism.BasicNotions.Part A.CG)) :
    Multiset.ofList (P.flatMap (flat N A)) =
      ((Multiset.ofList (P.map (toPair N A))).bind seg).map fun q => (q.1, (q.2 : ℝ) / 2) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
      Multiset.map_add]
    congr 1
    unfold seg flat toPair
    rw [Multiset.map_map, ← Multiset.map_coe]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring

theorem isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' he
  have hpos : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ P.flatMap (flat N A), 1 ≤ q.1.1 := by
    intro P hP q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
    exact (hP p hp).1
  have hd : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ Multiset.ofList (P.map (toPair N A)), 1 ≤ q.2 := by
    intro P hP q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hq)
    exact (hP p hp).2.1
  have h1 := hR _ _ (hpos Pa h) (hpos Pa' h') (by simpa only [isoLoc_eq] using he)
  have h2 := Multiset.coe_eq_coe.2 h1
  rw [coe_flatMap, coe_flatMap] at h2
  have hinj : Function.Injective fun q : (Σ a : ℕ, A.CG a) × ℤ => (q.1, (q.2 : ℝ) / 2) := by
    intro q q' e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    refine Prod.ext e1 ?_
    have : (q.2 : ℝ) = q'.2 := by linarith
    exact_mod_cast this
  have h3 := eq_of_bind_seg _ _ (hd Pa h) (hd Pa' h') (Multiset.map_injective hinj h2)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h3
  exact Multiset.coe_eq_coe.1 (Multiset.map_injective (toPair_injective N A) h3)

end GlobalTheory.SpehRigid
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem isoLoc_eq_twSum_zero (P : List (Part A.CG)) (h : ∀ p ∈ P, p.d = 1) (w : PlE H) :
    isoLoc N A P w =
      GlobalTheory.RowTie.twSum N A (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) w := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have hp : p.d = 1 := h p (by simp)
    have h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0 := by
      simp [spehLoc, hp, A.lpSum_zero]
    change A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _
    rw [h1, ih fun q hq => h q (by simp [hq])]
    rfl

theorem isobaricCuspidalMultiplicityOne_of_twisted : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' hw
  have key := hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h p hp).1)
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h' p hp).1)
    (hw.mono fun w e => by
      rw [← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2),
        ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])
  have back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) →
      (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map
        (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P := by
    intro P hP
    rw [List.map_map]
    conv_rhs => rw [← List.map_id P]
    refine List.map_congr_left fun p hp => ?_
    have := hP p hp
    obtain ⟨a, π, d⟩ := p
    simp only at this
    subst this
    rfl
  have := key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))
  rwa [back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)] at this

end GlobalTheory.RowClose
end

section

namespace GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isoLoc_perm {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) : isoLoc N A Pa w = isoLoc N A Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    rw [← A.lpSum_assoc, ← A.lpSum_assoc, A.lpSum_comm (spehLoc N A y w)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.RowTie.repDet_split : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i →
    ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  intro R H what₂ N A i hBC hSp hRep P P' hP
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hperm := hSp P P' hP Pa Pa' hPa hPa'
  have hiso := GlobalTheory.RowTie.RepDet.isoLoc_perm N A hperm
  apply hRep P P'
  · intro w hw
    rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw, hiso w]
  · intro w hw
    rw [← (hPa.2.2.2.2.1 w hw).2, ← (hPa'.2.2.2.2.1 w hw).2, hiso w]
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem pairs_of_thetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) : GlobalTheory.ThetaExh.Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hF
  exact ⟨f, hf, _, hle hF, fun h0 => hF0 (inner_self_eq_zero.1 h0)⟩

theorem splitLift_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.ThetaExh.SplitLift N A i :=
  fun _ _ _ N A i h σ P hθ => h σ P (pairs_of_thetaLift N A i σ P hθ)

end GlobalTheory.RowTie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

open GlobalTheory.WeilDeligne

theorem tempered_of_rank_le_one (D : D7) (T : WDTie D.nd D.naut) (h1 : RankOneUnitary T)
    (a : ℕ) (π : D.naut.CG a) (ha : a ≤ 1) (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  rw [T.tempered]
  have hd : (T.e w (D.naut.locG π w)).lpDim = a := by rw [T.dim, D.naut.locG_dim]
  refine GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues _ _ _ _ _ _ (hd.le.trans ha) fun φ hφ α hα => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · have hc := WD.card_eig (T.e w (D.naut.locG π w)) φ
    rw [hd, Multiset.card_eq_zero] at hc
    rw [hc] at hα
    exact absurd hα (Multiset.notMem_zero α)
  · refine h1 π w φ.1 (deg_eq_one_iff.mp hφ) α ?_
    rw [WDTie.eig, WD.inePol_of_mem _ φ.2]
    exact hα

theorem tempered_all_ranks : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  intro D T h1 h2
  have key : GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
    intro a π hc hr w
    rcases Nat.lt_or_ge a 2 with ha | ha
    · exact tempered_of_rank_le_one D T h1 a π (by omega) w
    · exact h2 a π ha hc hr w
  exact ⟨fun a π _ hc hr w => key a π hc hr w, key⟩

end GlobalTheory.RowTie
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ) (L : Lat O K r), ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  first | exact @GlobalTheory.SubIdxCount.ncard_subIdx_le | exact GlobalTheory.SubIdxCount.ncard_subIdx_le | (intros; apply GlobalTheory.SubIdxCount.ncard_subIdx_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

theorem _root_.GlobalTheory.T.cechComparison_degreeZero_alternatingPullback : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  first | (exact @GlobalTheory.cechAbPull_degZero) | (exact GlobalTheory.cechAbPull_degZero) | (intros; apply GlobalTheory.cechAbPull_degZero  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

theorem _root_.GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential : ∀ {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
    {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S}
    (ψ : Cube.PullHom σ τ A B) (p : ℕ) (x : Cube.Term A p),
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  first | (exact @GlobalTheory.Cube.PullHom.term_d) | (exact GlobalTheory.Cube.PullHom.term_d) | (intros; apply GlobalTheory.Cube.PullHom.term_d  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.completion_embeddings_single_frobenius_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  first | exact @GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | exact GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | (intros; apply GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit <;> assumption)
end
