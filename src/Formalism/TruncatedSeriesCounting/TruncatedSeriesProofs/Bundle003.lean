module

public import Formalism.TruncatedSeriesCounting.Bundle002
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Quotient.Pi

@[expose] public section

section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma hCoef_num (x : ℝ) (hx : 11 ≤ x) : 0 ≤ 7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32 := by

  have hy : 0 ≤ x - 11 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

theorem h_coefficient_bound : HCoef := by
  intro x hx
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : x - 1 ≠ 0 := ne_of_gt h1
  have key := hCoef_num x hx
  have e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))
      = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) := by
    field_simp
    ring
  have hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) :=
    div_nonneg key (by positivity)
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Module

section Snake

variable {O : Type} [CommRing O]

theorem len_coker_add {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    [AddCommGroup C] [Module O C] (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (a : Module.End O A) (b : Module.End O B) (c : Module.End O C)
    (h1 : ∀ x, b (f x) = f (a x)) (h2 : ∀ y, c (g y) = g (b y)) (hc : Function.Injective c) :
    Module.length O (B ⧸ LinearMap.range b) =
      Module.length O (A ⧸ LinearMap.range a) + Module.length O (C ⧸ LinearMap.range c) := by
  have hF : LinearMap.range a ≤ (LinearMap.range b).comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, h1 x⟩
  have hG : LinearMap.range b ≤ (LinearMap.range c).comap g := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, h2 y⟩
  let F := Submodule.mapQ (LinearMap.range a) (LinearMap.range b) f hF
  let G := Submodule.mapQ (LinearMap.range b) (LinearMap.range c) g hG
  refine Module.length_eq_add_of_exact F G ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [F, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    have hgy : g y = 0 := by
      apply hc
      rw [h2, hy, hfg.apply_apply_eq_zero, map_zero]
    obtain ⟨z, rfl⟩ := (hfg y).1 hgy
    have : a z = x := hf (by rw [← h1, hy])
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, this⟩
  · intro w
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, rfl⟩ := hg w
    exact ⟨Submodule.Quotient.mk y, by simp [G]⟩
  · intro w
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [G, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := hg u
      have : g (y - b v) = 0 := by rw [map_sub, ← h2, hu, sub_self]
      obtain ⟨z, hz⟩ := (hfg _).1 this
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      simp only [F, Submodule.mapQ_apply, hz]
      rw [Submodule.Quotient.eq]
      exact ⟨-v, by simp⟩
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      simp only [F, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.eq'] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨g t, ?_⟩
      rw [h2, ht, map_add (f := _), map_neg, hfg.apply_apply_eq_zero, neg_zero, zero_add]

end Snake

section Main

variable {O : Type} [CommRing O] [IsDomain O]

theorem sub_smul_one_injective {M : Type} [AddCommGroup M] [Module O M] [IsTorsionFree O M]
    (ℓ : O) (hℓ : ℓ ≠ 0) (q : Module.End O M) (n : ℕ) (hq : q ^ n = 0) :
    Function.Injective (q - ℓ • (1 : Module.End O M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : q x = ℓ • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have h2 : ∀ k : ℕ, (q ^ k) x = ℓ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]
  have h3 := h2 n
  rw [hq, LinearMap.zero_apply] at h3
  exact (smul_eq_zero.mp h3.symm).resolve_left (pow_ne_zero n hℓ)

theorem len_base (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
    (ℓ : O) :
    Module.length O (R ⧸ LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))) =
      (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  let e := (Module.finBasis O R).equivFun
  have hmap : (LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))).map
      (e : R →ₗ[O] (Fin (finrank O R) → O)) =
      Submodule.pi Set.univ (fun _ => Ideal.span {ℓ}) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      exact ⟨-(e y i), by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨_, ⟨e.symm (fun i => -c i), rfl⟩, ?_⟩
      ext i
      change e (((0 : Module.End O R) - ℓ • (1 : Module.End O R)) (e.symm fun i => -c i)) i = v i
      simp [← hc, mul_comm]
  rw [(Submodule.Quotient.equiv _ _ e hmap).length_eq, (Submodule.quotientPi _).length_eq,
    Module.length_pi_of_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem len_main [IsPrincipalIdealRing O] (ℓ : O) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∀ (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
      (q : Module.End O R), q ^ (n + 1) = 0 →
      Module.length O (R ⧸ LinearMap.range (q - ℓ • (1 : Module.End O R))) =
        (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction n with
  | zero =>
    intro R _ _ _ _ q hq
    rw [zero_add, pow_one] at hq
    subst hq
    exact len_base R ℓ
  | succ n ih =>
    intro R _ _ _ _ q hq
    have hK : ∀ x ∈ LinearMap.ker q, q x ∈ LinearMap.ker q := fun x hx => by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
    have hQ : ∀ x ∈ LinearMap.range q, q x ∈ LinearMap.range q :=
      fun x _ => LinearMap.mem_range_self q x
    let qK := q.restrict hK
    let qQ := q.restrict hQ
    have hqK : qK = 0 := by
      ext ⟨x, hx⟩
      simpa [qK] using hx
    have key : ∀ (k : ℕ) (x : LinearMap.range q), (((qQ ^ k) x : LinearMap.range q) : R) =
        (q ^ k) (x : R) := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
        rfl
    have hqQ : qQ ^ (n + 1) = 0 := by
      ext ⟨x, y, rfl⟩
      rw [key, LinearMap.zero_apply, Submodule.coe_zero, ← Module.End.mul_apply, ← pow_succ, hq,
        LinearMap.zero_apply]
    have hex : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict :=
      LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    have hsn := len_coker_add (LinearMap.ker q).subtype q.rangeRestrict
      (LinearMap.ker q).injective_subtype q.surjective_rangeRestrict hex
      (qK - ℓ • (1 : Module.End O _)) (q - ℓ • (1 : Module.End O R))
      (qQ - ℓ • (1 : Module.End O _))
      (fun x => by simp [qK]) (fun y => by ext; simp [qQ])
      (sub_smul_one_injective ℓ hℓ qQ (n + 1) hqQ)
    rw [hsn, ih _ qK (by rw [hqK, zero_pow (Nat.succ_ne_zero _)]), ih _ qQ hqQ, ← add_mul,
      ← Nat.cast_add]
    congr 2
    have h1 := (LinearMap.ker q).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq q.quotKerEquivRange] at h1
    omega

end Main

theorem length_pi_zero_bound : LenPi0 := by
  intro O _ _ _ R _ _ _ _ ℓ hℓ q hq
  obtain ⟨n, hn⟩ := hq
  exact len_main ℓ hℓ n R q (by rw [pow_succ, hn, zero_mul])

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem chain_len_add (X Y Z : Submodule O M) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) =
      Module.length O (↥Y ⧸ X.comap Y.subtype) + Module.length O (↥Z ⧸ Y.comap Z.subtype) := by
  have hle : X.comap Y.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hYZ) :=
    fun x hx => hx
  have hle2 : X.comap Z.subtype ≤ (Y.comap Z.subtype).comap LinearMap.id := fun x hx => hXY hx
  let f := Submodule.mapQ (X.comap Y.subtype) (X.comap Z.subtype) (Submodule.inclusion hYZ) hle
  let g := Submodule.mapQ (X.comap Z.subtype) (Y.comap Z.subtype) LinearMap.id hle2
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hq
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩
  have hfg : Function.Exact f g := by
    intro q
    constructor
    · intro hz
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (z : M) ∈ Y := hz
      exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact y.2
  exact Module.length_eq_add_of_exact f g hf hg hfg

theorem chain_len_le_of_le_sup (A X Z : Submodule O M) (hAZ : A ≤ Z) (hZ : Z ≤ A ⊔ X) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) ≤ Module.length O (↥A ⧸ X.comap A.subtype) := by
  have hle : X.comap A.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hAZ) :=
    fun x hx => hx
  apply Module.length_le_of_surjective (Submodule.mapQ _ _ (Submodule.inclusion hAZ) hle)
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 (hZ z.2)
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - (z : M)) ∈ X
  rw [← hax, show a - (a + x) = -x by abel]
  exact X.neg_mem hx

theorem chain_len_le_top (A P : Submodule O M) (hA : ⊤ ≤ A ⊔ P) :
    Module.length O (M ⧸ P) ≤ Module.length O (↥A ⧸ P.comap A.subtype) := by
  apply Module.length_le_of_surjective (Submodule.mapQ (P.comap A.subtype) P A.subtype le_rfl)
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ :=
    Submodule.mem_sup.1 (hA (Submodule.mem_top : m ∈ (⊤ : Submodule O M)))
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - m) ∈ P
  rw [← hax, show a - (a + x) = -x by abel]
  exact P.neg_mem hx

end Chain

private lemma comap_subtype_inf_of_le {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (A B C : Submodule O M) (h : A ≤ C) : (B ⊓ C).comap A.subtype = B.comap A.subtype := by
  ext x
  simp [h x.2]

theorem column_chain_bound : ColChain := by
  unfold ColChain
  intro O _ M _ _ P k F h0 hF
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    exact chain_len_le_top (F 0) P (by rw [h0]; exact le_sup_left)
  | succ k ih =>
    have hk : F (k + 1) ≤ F k := hF k (Nat.lt_succ_self k)
    have ih' := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have e1 := chain_len_add (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (F k)
      (inf_le_inf_right _ le_sup_right) inf_le_right
    rw [comap_subtype_inf_of_le (F k) P (F k) le_rfl, comap_subtype_inf_of_le (F k) (F (k + 1) ⊔ P) (F k) le_rfl] at e1
    have e2 := chain_len_le_of_le_sup (F (k + 1)) (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k)
      (le_inf le_sup_left hk) (le_of_eq (sup_inf_assoc_of_le P hk))
    rw [comap_subtype_inf_of_le (F (k + 1)) P (F k) hk] at e2
    rw [Finset.sum_range_succ, add_assoc]
    refine le_trans ih' (add_le_add le_rfl ?_)
    rw [e1, add_comm]
    exact add_le_add le_rfl e2

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem second_exponent_bound : MaxZeroExponentInequality := by
  intro ℓ hℓ b b' S h'' E s₂ L c' hE hs hL hc
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hl1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hcast : (((b + S + 1 : ℕ) : ℝ)) = (b : ℝ) + (S : ℝ) + 1 := by push_cast; ring

  have e2 : (b : ℝ) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + (b : ℝ) / (ℓ : ℝ) := by
    field_simp
    ring
  have e1 : ((b : ℝ) + (S : ℝ) + 1) / ((ℓ : ℝ) - 1)
      = (b : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := by ring

  have e3 : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) ≤ (S : ℝ) + 1 := by
    have hq : 0 ≤ ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by linarith) hl1.le
    have hm : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) = (S : ℝ) + 1 := by
      field_simp
    nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have h4 : 0 ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := div_nonneg hb (mul_pos hl0 hl1).le
  rw [hcast]
  apply max_le
  · linarith
  · rw [e1, e2]
    linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

private lemma comap_subtype_span_sup_eq_span_range_sup {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (Z J : Submodule O M) (s : Finset M) (hs : ∀ x ∈ s, x ∈ Z) :
    (Submodule.span O (s : Set M) ⊔ J).comap Z.subtype =
      Submodule.span O (Set.range fun x : s => (⟨x, hs x x.2⟩ : Z)) ⊔ J.comap Z.subtype := by
  apply Submodule.map_injective_of_injective Z.injective_subtype
  have hle : Submodule.span O (s : Set M) ≤ Z := Submodule.span_le.2 fun x hx => hs x hx
  have hr : Set.range (⇑Z.subtype ∘ fun x : s => (⟨x, hs x x.2⟩ : Z)) = (s : Set M) := by
    ext y
    simp
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    ← Set.range_comp, hr, inf_comm Z, sup_inf_assoc_of_le J hle, inf_comm J Z]

theorem length_quotient_le_of_two_step : ColTwoStep := by
  unfold ColTwoStep
  intro O M _ _ _ ℓ g g₀ e e' Z I s s₀ hIZ hs hs₀ hs₀Z hspan hZ hI
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => by
    rw [← hspan]
    exact Submodule.mem_sup_left (Submodule.subset_span hx)
  have hs₀Z' : ∀ x ∈ s₀, x ∈ Z := fun x hx => hs₀Z hx
  have hIT : I.comap Z.subtype ≤ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    Submodule.comap_mono le_sup_right
  let N := ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ
  have hsplit : Module.length O (Z ⧸ I.comap Z.subtype) =
      Module.length O N + Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) :=
    Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hQN : Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) =
      Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) :=
    (Submodule.quotientQuotientEquivQuotient _ _ hIT).length_eq
  let q : s₀ → Z ⧸ I.comap Z.subtype := fun x => (I.comap Z.subtype).mkQ ⟨x, hs₀Z' x x.2⟩
  have hNq : N = Submodule.span O (Set.range q) := by
    show ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ = _
    rw [comap_subtype_span_sup_eq_span_range_sup Z I s₀ hs₀Z', Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  let v : s₀ → N := fun x => ⟨q x, by rw [hNq]; exact Submodule.subset_span ⟨x, rfl⟩⟩
  have hv_top : Submodule.span O (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hNq.symm
  have hv_kill : ∀ x, ((ℓ : O) ^ e') • v x = 0 := by
    intro x
    apply Subtype.ext
    show ((ℓ : O) ^ e') • q x = 0
    simp only [q, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e') • (x : M) ∈ I
    have h := hI x (Submodule.subset_span x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hN : Module.length O N ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span v ((ℓ : O) ^ e') hv_top hv_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e'
    calc Module.length O N ≤ (Fintype.card s₀ : ℕ∞) *
          Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e'}) := h1
      _ ≤ (g₀ : ℕ∞) * ((e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs₀) h2
      _ = _ := by ring
  let w : s → Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    fun x => ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⟨x, hsZ x x.2⟩
  have hw_top : Submodule.span O (Set.range w) = ⊤ := by
    have htop : (⊤ : Submodule O Z) = Submodule.span O (Set.range fun x : s => (⟨x, hsZ x x.2⟩ : Z)) ⊔
        I.comap Z.subtype := by
      rw [← comap_subtype_span_sup_eq_span_range_sup Z I s hsZ, hspan, Submodule.comap_subtype_self]
    have hmt : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⊤ = ⊤ := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    have hbot : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ
        (I.comap Z.subtype) = ⊥ :=
      le_bot_iff.1 ((Submodule.map_mono hIT).trans (Submodule.mkQ_map_self _).le)
    rw [← hmt, htop, Submodule.map_sup, hbot, sup_bot_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw_kill : ∀ x, ((ℓ : O) ^ e) • w x = 0 := by
    intro x
    simp only [w, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (x : M) ∈ Submodule.span O (s₀ : Set M) ⊔ I
    have h := hZ x (hsZ x x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hZT : Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) ≤
      (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span w ((ℓ : O) ^ e) hw_top hw_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e
    calc _ ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
      _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs) h2
      _ = _ := by ring
  rw [hsplit, hQN]
  calc _ ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add hN hZT
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end
