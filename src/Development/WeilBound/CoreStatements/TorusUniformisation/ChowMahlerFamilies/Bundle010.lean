module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_coherent_gens

theorem mem_spanOver {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, one_mem R, e, he, (one_smul Ω e).symm⟩

theorem spanOver_le {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hS : ∀ e ∈ S, e ∈ L) : spanOver R S ≤ L := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hL a ha e (hS e he)

theorem spanOver_mono {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E]
    [Module Ω E] (R : Subalgebra o Ω) {S T : Set E} (h : S ⊆ T) : spanOver R S ≤ spanOver R T := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem transition {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) {c t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) (a : K → ℤ) (m : ℕ) (hm : ∀ k, (m : ℤ) ≤ a k) :
    ∃ r ∈ chartRing o (mseg x) t,
      (chartMon x t a)⁻¹ * chartMon x c a = r * (mseg x c / mseg x t) ^ m := by
  refine ⟨∏ k, (x ⟨k, c k⟩ / x ⟨k, t k⟩) ^ (a k - m).toNat,
    prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem (O := o) x ht k (c k)) _, ?_⟩
  simp only [chartMon, mseg]
  rw [← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h : a k = (((a k - m).toNat + m : ℕ) : ℤ) := by
    have := hm k
    push_cast
    omega
  rw [← pow_add, ← zpow_natCast, ← h, div_zpow, div_eq_inv_mul]

end PositivityTheory.Xgn.A_coherent_gens

theorem PositivityTheory.Xgn.t_coherent_gens : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (V : Type) [AddCommGroup V] [Module Ω V] (Γ : (∀ k, ι k) → AddSubgroup V), IsLatFamily O x Γ → (∀ c, mseg x c ≠ 0 → ∃ S : Finset V, Γ c = spanOver (chartRing O (mseg x) c) (S : Set V)) → ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a → ∃ (M : ℕ) (v : Fin M → V), ∀ c, mseg x c ≠ 0 → Γ c = spanOver (chartRing O (mseg x) c) (Set.range fun j => (chartMon x c a)⁻¹ • v j) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x V _ _ Γ ⟨hst, hov⟩ hfg
  choose! S hS using hfg
  let I := Σ c : {c : ∀ k, ι k // mseg x c ≠ 0}, S c.1
  have hmem : ∀ i : I, (i.2 : V) ∈ Γ i.1.1 := fun i => by
    rw [hS _ i.1.2]
    exact A_coherent_gens.mem_spanOver _ i.2.2
  have hex : ∀ p : I × {c : ∀ k, ι k // mseg x c ≠ 0}, ∃ m : ℕ,
      (mseg x p.1.1.1 / mseg x p.2.1) ^ m • (p.1.2 : V) ∈ Γ p.2.1 :=
    fun p => hov _ _ p.1.1.2 p.2.2 _ (hmem p.1)
  choose m hm using hex
  refine ⟨fun _ => ((∑ p, m p : ℕ) : ℤ), fun a ha => ?_⟩
  let e := Fintype.equivFin I
  refine ⟨_, fun j => chartMon x (e.symm j).1.1 a • ((e.symm j).2 : V), fun t ht => ?_⟩
  apply le_antisymm
  · rw [hS t ht]
    refine A_coherent_gens.spanOver_mono _ fun w hw => ⟨e ⟨⟨t, ht⟩, ⟨w, hw⟩⟩, ?_⟩
    have hne : chartMon x t a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ ((Finset.prod_ne_zero_iff.1 ht) k (Finset.mem_univ _))
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · refine A_coherent_gens.spanOver_le _ (hst t ht) ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr, heq⟩ := A_coherent_gens.transition (o := O) x (c := (e.symm j).1.1) ht a
      (m (e.symm j, ⟨t, ht⟩)) fun k => le_trans (by
        exact Nat.cast_le.2
          (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))) (ha k)
    dsimp only
    rw [smul_smul, heq, mul_smul]
    exact hst t ht r hr _ (hm (e.symm j, ⟨t, ht⟩))
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_preserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem below_ne {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (h : mseg (joinCoord x z) s ≠ 0) : mseg x (restrictChart s) ≠ 0 := by
  unfold mseg at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro k _
  exact h (Sum.inl k) (Finset.mem_univ _)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem smul_mem (R : Subalgebra O Ω) (L : AddSubgroup V) (b : Ω) (hb : b ∈ R) (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    b • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    exact AddSubgroup.subset_closure ⟨b * a, R.mul_mem hb ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | neg v _ hv => rw [smul_neg]; exact neg_mem hv

theorem le_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L ≤ L') :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} ≤
      AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  apply AddSubgroup.closure_mono
  rintro v ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem gen_closure [IsDomain O] (R : Subalgebra O Ω) (L L' : AddSubgroup V)
    (h : ∀ v ∈ L, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L') (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨c, hc, hv⟩ := hv
    obtain ⟨d, hd, hw⟩ := hw
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem d) _ hv
    · rw [mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem c) _ hw
  | neg v _ hv =>
    obtain ⟨c, hc, hv⟩ := hv
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hv⟩

theorem scaled_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ L' ↔ ∃ e ∈ L, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}, v = c • e := by
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨e', he', rfl⟩ := (h e).1 he
      exact ⟨a • e', AddSubgroup.subset_closure ⟨a, ha, e', he', rfl⟩, smul_comm _ _ _⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add v w _ _ hv hw =>
      obtain ⟨e, he, rfl⟩ := hv
      obtain ⟨f, hf, rfl⟩ := hw
      exact ⟨e + f, add_mem he hf, (smul_add _ _ _).symm⟩
    | neg v _ hv =>
      obtain ⟨e, he, rfl⟩ := hv
      exact ⟨-e, neg_mem he, (smul_neg _ _).symm⟩
  · rintro ⟨e, he, rfl⟩
    induction he using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      exact AddSubgroup.subset_closure ⟨a, ha, c • e, (h _).2 ⟨e, he, rfl⟩, smul_comm _ _ _⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv

end PositivityTheory.Xgn.A_pull_preserve

theorem PositivityTheory.Xgn.t_pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hP hP'
  refine ⟨fun h s hs => ?_, fun h s hs => ?_, fun c h s hs v => ?_⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.le_closure _ _ _ (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs))
  · rw [hP s hs, hP' s hs]
    have h0 := h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)
    exact ⟨PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.1,
      PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.2⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.scaled_closure _ _ _ c
      (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)) v
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_line
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord (fun p => φ (x p)) z) s =
      φ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type, map_prod]
  rfl

theorem chartMon_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) :
    chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a) =
      φ (chartMon x (restrictChart s) a) := by
  simp only [chartMon, Fintype.prod_sum_type, pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zpow_zero, Finset.prod_const_one, mul_one, map_prod, map_zpow₀]
  rfl

theorem map_mem (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0)
    (r : Ω) (hr : r ∈ chartRing O (mseg x) (restrictChart s)) :
    φ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s).comap φ := by
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : φ (mseg x t / mseg x (restrictChart s)) =
        mseg (joinCoord (fun p => φ (x p)) z) (comb t s) / mseg (joinCoord (fun p => φ (x p)) z) s := by
      rw [mseg_join φ x z (comb t s), mseg_join φ x z s, map_div₀]
      exact (mul_div_mul_right _ _ hw).symm
    have h2 := div_mem_chartRing (o := O) (mseg (joinCoord (fun p => φ (x p)) z)) s (comb t s)
    rw [← h] at h2
    exact h2
  exact hle hr

theorem main [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (u : Ω) (a : K → ℤ)
    (A : (∀ k, ι k) → AddSubgroup Ω) (hA : IsLine O x u a A)
    (B : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup Ω₁)
    (hB : ∀ s, mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0 → B s = AddSubgroup.closure
      {v | ∃ c ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s, ∃ e ∈ A (restrictChart s),
        v = c • φ e}) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0) (v : Ω₁) :
    v ∈ B s ↔ ∃ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s,
      v = r * (φ u * chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a)) := by
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    intro h
    exact left_ne_zero_of_mul hs (by rw [h, map_zero])
  rw [hB s hs, chartMon_join, ← map_mul]
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      obtain ⟨r, hr, rfl⟩ := (hA _ hx e).1 he
      refine ⟨c * φ r, mul_mem hc (map_mem φ x z s hs r hr), ?_⟩
      rw [smul_eq_mul, map_mul, mul_assoc]
    | zero => exact ⟨0, zero_mem _, by rw [zero_mul]⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, rfl⟩ := h₂
      exact ⟨r₁ + r₂, add_mem hr₁ hr₂, by rw [add_mul]⟩
    | neg w _ h =>
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨-r, neg_mem hr, by rw [neg_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact AddSubgroup.subset_closure ⟨r, hr, _, (hA _ hx _).2 ⟨1, one_mem _, (one_mul _).symm⟩, rfl⟩

end PositivityTheory.Xgn.A_pull_line
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_dual

theorem tri_inv {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {N : ℕ}
    (w u : Module.Basis (Fin N) Ω V) (h : ∀ i j, i < j → w.repr (u i) j = 0) :
    (∀ i j, i < j → u.repr (w i) j = 0) ∧ ∀ i, u.repr (w i) i = (w.repr (u i) i)⁻¹ := by
  have hM : (w.toMatrix u).BlockTriangular id := fun i j hij => h j i hij
  have hMN : w.toMatrix u * u.toMatrix w = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w u
  haveI : Invertible (w.toMatrix u) := ⟨u.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip u w, hMN⟩
  have hinv : (w.toMatrix u)⁻¹ = u.toMatrix w := Matrix.inv_eq_right_inv hMN
  have hN : (u.toMatrix w).BlockTriangular id := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨fun i j hij => hN hij, fun i => ?_⟩
  have hii := congrFun (congrFun hMN i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at hii
  · simp only [Module.Basis.toMatrix_apply] at hii
    exact eq_inv_of_mul_eq_one_right hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hM hk, zero_mul]
    · rw [hN hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem repr_of_pair {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (w : Fin N → V) (w₁ : Module.Basis (Fin N) Ω V₁)
    (h : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (y : V₁) (j : Fin N) :
    w₁.repr y j = β (w j.rev) y := by
  have hy := congrArg (β (w j.rev)) (w₁.sum_repr y)

  rw [map_sum] at hy
  simp only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.rev_inj] at hy
  rw [← hy]
  simp

theorem exists_dual {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (hβ : Function.Bijective β.flip) (u : Module.Basis (Fin N) Ω V) :
    ∃ u₁ : Module.Basis (Fin N) Ω V₁, ∀ v j, β v (u₁ j) = u.repr v j.rev := by
  let e := LinearEquiv.ofBijective β.flip hβ
  refine ⟨(u.dualBasis.reindex Fin.revPerm).map e.symm, fun v j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]
  change e (e.symm (u.dualBasis j.rev)) v = _
  simp

end PositivityTheory.Xgn.A_flagframe_dual

theorem PositivityTheory.Xgn.t_flagframe_dual : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hD w b hE w₁ hw₁
  refine ⟨fun c hc j => ?_⟩
  have hne : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  let m : Fin N → Ω := fun i => ∏ k, x ⟨k, c k⟩ ^ b i k
  have hm : ∀ i, m i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hne k)
  have hinvm : ∀ i, ∏ k, x ⟨k, c k⟩ ^ (-b i) k = (m i)⁻¹ := by
    intro i
    simp only [m, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  have hgr := hE.graded c hc
  have hex : ∀ i, ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = m i := by
    intro i
    have hmem : m i ∈ degLat O x (b i) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hgr i] at hmem
    exact hmem
  choose e he1 he2 he3 using hex
  have hP : (w.toMatrix e).BlockTriangular id := fun i j hij => he2 j i hij
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular hP]
    refine (Finset.prod_ne_zero_iff.mpr fun i _ => ?_).isUnit
    rw [Module.Basis.toMatrix_apply, he3]
    exact hm i
  have hbasis := (Module.Basis.is_basis_iff_det w).mpr hdet
  let eb : Module.Basis (Fin N) Ω V := Module.Basis.mk hbasis.1 hbasis.2.ge
  have heb : ∀ i, eb i = e i := fun i => Module.Basis.mk_apply _ _ _
  have htri := A_flagframe_dual.tri_inv w eb (by
    intro i k hik
    rw [heb]
    exact he2 i k hik)
  have hrep : ∀ y k, w₁.repr y k = β (w k.rev) y :=
    fun y k => A_flagframe_dual.repr_of_pair β w w₁ hw₁ y k
  have hstep : ∀ n : ℕ, ∀ v ∈ E.lat c, (∀ k : Fin N, n ≤ k.val → w.repr v k = 0) →
      ∀ k, eb.repr v k ∈ chartRing O (mseg x) c := by
    intro n
    induction n with
    | zero =>
      intro v _ hz k
      have hv0 : v = 0 := w.ext_elem fun i => by rw [hz i (Nat.zero_le _), map_zero]; rfl
      rw [hv0, map_zero]
      exact zero_mem _
    | succ n ih =>
      intro v hv hz k
      by_cases hn : n < N
      · let i : Fin N := ⟨n, hn⟩
        have hmem : w.repr v i ∈ degLat O x (b i) c := by
          rw [← hgr i]
          exact ⟨v, hv, fun j hij => hz j hij, rfl⟩
        obtain ⟨α, hα, hs⟩ := hmem
        have hv' : v - α • e i ∈ E.lat c := sub_mem hv (E.stable c α hα (e i) (he1 i))
        have hz' : ∀ k : Fin N, n ≤ k.val → w.repr (v - α • e i) k = 0 := by
          intro k hk
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          rcases Nat.lt_or_eq_of_le hk with hk | hk
          · have hik : i < k := hk
            rw [hz k hk, he2 i k hik, mul_zero, sub_zero]
          · have hik : k = i := Fin.ext hk.symm
            rw [hik, hs, he3]
            exact sub_self _
        have h1 := ih _ hv' hz' k
        have h2 : eb.repr v k = eb.repr (v - α • e i) k + α * eb.repr (e i) k := by
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          ring
        rw [h2]
        refine add_mem h1 (mul_mem hα ?_)
        rw [← heb, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · exact ih v hv (fun k hk => absurd k.isLt (by omega)) k
  have hcoef : ∀ v ∈ E.lat c, ∀ k, eb.repr v k ∈ chartRing O (mseg x) c :=
    fun v hv => hstep N v hv (fun k hk => absurd k.isLt (by omega))
  ext s
  constructor
  · rintro ⟨w', hw', hz, rfl⟩
    have key : β (e j.rev) w' = m j.rev * w₁.repr w' j := by
      conv_lhs => rw [← w.sum_repr (e j.rev)]

      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, he3, hrep w' j]
      · intro k _ hk
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rcases lt_or_gt_of_ne hk with hk | hk
        · have hjk : j < k.rev := Fin.lt_rev_iff.mp hk
          have hb : β (w k) w' = w₁.repr w' k.rev := by rw [hrep, Fin.rev_rev]
          rw [hb, hz _ hjk, mul_zero]
        · rw [he2 _ _ hk, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    refine ⟨β (e j.rev) w', (hD.2 c hc w').1 hw' (e j.rev) (he1 _), ?_⟩
    show w₁.repr w' j = β (e j.rev) w' * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
    rw [key, hinvm, mul_comm (m j.rev), mul_assoc, mul_inv_cancel₀ (hm _), mul_one]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, hf⟩ := hD.1.2 (a • eb.coord j.rev)
    have hfv : ∀ v, β v f = a * eb.repr v j.rev := by
      intro v
      have := LinearMap.congr_fun hf v
      simpa using this
    refine ⟨f, (hD.2 c hc f).2 fun v hv => ?_, fun k hk => ?_, ?_⟩
    · rw [hfv]
      exact mul_mem ha (hcoef v hv _)
    · rw [hrep, hfv, htri.1 _ _ (Fin.rev_lt_rev.mpr hk), mul_zero]
    · show w₁.repr f j = a * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
      rw [hrep, hfv, htri.2, heb, he3, hinvm]
end
