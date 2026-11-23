module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle164
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by
  ext a
  have h : (c ^ (j + 1)) a = c ((c ^ j) a) := by
    rw [add_comm, zpow_add, zpow_one, MulAut.mul_apply]
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]
  constructor
  · intro ha
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxa⟩
    rw [← c.injective hxa]
    exact hx

theorem chain_step {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective

theorem chainIndex : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl


open Classical in
theorem emb_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    {e : Fin r → Fin n} {ι : GU σ r →* GU σ n} (he : Function.Injective e) (hι : IsEmb e ι)
    (D : Fin n → L) (s : GU σ r) (hs : mat s = Matrix.diagonal (D ∘ e)) :
    mat (ι s) * Matrix.diagonal (fun a => if a ∈ Set.range e then 1 else D a) = Matrix.diagonal D := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ Set.range e
  · rw [if_pos hb, mul_one]
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rw [(hι s).1, hs]
      simp [Matrix.diagonal_apply, he.eq_iff]
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [(hι s).2 a b (Or.inl ha), Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]
  · rw [if_neg hb, (hι s).2 a b (Or.inr hb)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab, zero_mul]

theorem embTorus : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [if_pos ha, if_pos hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.TorusConjProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) : mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-b i)) := by
  have h : mat s * Matrix.diagonal (fun i => ϖ ^ (-b i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-b i))) := by rw [h, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_zpow_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (d : ℤ) :
    mat (s ^ d) = Matrix.diagonal (fun i => ϖ ^ (d * b i)) := by
  induction d using Int.induction_on with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [zpow_add_one, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring
  | pred k ih =>
    rw [zpow_sub_one, mat_mul, ih, mat_inv_diag hϖ hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj_apply {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (g : GU σ r) (i j : Fin r) :
    mat (s * g * s⁻¹) i j = ϖ ^ (b i - b j) * mat g i j := by
  rw [mat_mul, mat_mul, mat_inv_diag hϖ hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ hϖ]
  ring

theorem torusConj : GlobalTheory.SatakeWeyl.TorusConj := by
  intro L _ _ ϖ σ r γ b b' d s s' g hϖ hb hs hs' hg
  apply mat_injective
  ext i j
  rw [mat_conj_apply hϖ hs', mat_conj_apply hϖ (mat_zpow_diag hϖ hs d)]
  by_cases h : γ i = γ j
  · rw [hb i j h, mul_sub]
  · have h0 : mat g i j = 0 := hg i j h
    rw [h0, mul_zero, mul_zero]

end GlobalTheory.SatakeWeyl.TorusConjProof
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem sum_out_left_translate {A : Type} [Group A] (U : Subgroup A) [Fintype (A ⧸ U)] (F : A → ℂ)
    (hF : ∀ u ∈ U, ∀ a, F (a * u) = F a) (g : A) :
    ∑ y : A ⧸ U, F (g * y.out) = ∑ y : A ⧸ U, F y.out := by
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun y => ?_
  have h1 : (MulAction.toPerm g y : A ⧸ U) = ((g * y.out : A) : A ⧸ U) := by
    rw [MulAction.toPerm_apply, ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (g * y.out)
  rw [h1, hu, hF u u.2]

theorem unimodFin : UnimodFin := by
  intro A _ U V f hU hV hl hr
  haveI : U.FiniteIndex := ⟨hU⟩
  haveI : V.FiniteIndex := ⟨hV⟩
  letI : Fintype (A ⧸ U) := Fintype.ofFinite _
  letI : Fintype (A ⧸ V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have e1 : ∀ x : A ⧸ U, ∑ y : A ⧸ V, f (y.out⁻¹ * x.out) = ∑ y : A ⧸ V, f y.out⁻¹ := by
    intro x
    have := sum_out_left_translate V (fun a => f a⁻¹)
      (fun v hv a => by simp only [mul_inv_rev]; exact hl _ (V.inv_mem hv) _) x.out⁻¹
    simpa [mul_inv_rev] using this
  have e2 : ∀ y : A ⧸ V, ∑ x : A ⧸ U, f (y.out⁻¹ * x.out) = ∑ x : A ⧸ U, f x.out :=
    fun y => sum_out_left_translate U f hr _
  have := Finset.sum_comm (s := (Finset.univ : Finset (A ⧸ U))) (t := (Finset.univ : Finset (A ⧸ V)))
    (f := fun x y => f (y.out⁻¹ * x.out))
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact this

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] at h

theorem intIndex : GlobalTheory.SatakeWeyl.IntIndex := by
  intro L _ _ ϖ σ q hU
  obtain ⟨-, -, -, hϖ, -, -, hcard⟩ := hU
  set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv
  set A := v.valuationSubring
  set O := (intL L).toAddSubgroup
  let e : O →+ A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : O →+ A ⧸ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  have hϖ1 : v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change _ ↔ Ideal.Quotient.mk _ (e x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]
    change _ ↔ v x.1 < 1
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : v y ≤ 1 := hy
      rw [← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]
      calc WithZero.exp (-1 : ℤ) * v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact (lt_one_iff_le_exp_neg_one _).2 le_rfl
    · intro hx
      refine ⟨ϖ⁻¹ * x.1, ?_, ?_⟩
      · show v (ϖ⁻¹ * x.1) ≤ 1
        rw [map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]
        calc WithZero.exp (1 : ℤ) * v x.1 ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
              by gcongr; exact (lt_one_iff_le_exp_neg_one _).1 hx
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [AddMonoidHom.coe_mulLeft]
        show ϖ * (ϖ⁻¹ * x.1) = x.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact hcard

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_quotient_subgroupOf {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by
  have hout : ∀ a : A, F (QuotientGroup.mk a : A ⧸ W).out = F a := by
    intro a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W a
    rw [hw, hF w w.2]
  let e : Γ ⧸ W.subgroupOf Γ → A ⧸ W := fun y => QuotientGroup.mk ((y.out : Γ) : A)
  have hinj : Function.Injective e := by
    intro y z h
    have h1 : ((y.out : Γ) : A)⁻¹ * ((z.out : Γ) : A) ∈ W := QuotientGroup.eq.1 h
    have h2 : (QuotientGroup.mk y.out : Γ ⧸ W.subgroupOf Γ) = QuotientGroup.mk z.out :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h1))
    simpa using h2
  have hsupp : (Function.support fun y : A ⧸ W => F y.out) ⊆ Set.range e := by
    intro y hy
    have hm : y.out ∈ Γ := hΓ _ hy
    refine ⟨QuotientGroup.mk ⟨y.out, hm⟩, ?_⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (W.subgroupOf Γ) ⟨y.out, hm⟩
    have hw' : ((w : Γ) : A) ∈ W := Subgroup.mem_subgroupOf.1 w.2
    show (QuotientGroup.mk _ : A ⧸ W) = y
    rw [hw, Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem _ hw']
    exact QuotientGroup.out_eq' y
  calc ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y ∈ Set.range e, F y.out := by
        rw [← finsum_mem_univ]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
    _ = ∑ᶠ y, F (e y).out := finsum_mem_range hinj
    _ = _ := finsum_congr fun y => hout _

theorem unimod_of_unimodFin : UnimodFin → Unimod := by
  intro H A _ Γ U V f _ _ hUi hVi hΓ hfV hfU
  have h := H Γ (U.subgroupOf Γ) (V.subgroupOf Γ) (fun a => f a) hUi hVi
    (fun v hv a => hfV _ (Subgroup.mem_subgroupOf.1 hv) _)
    (fun u hu a => hfU _ (Subgroup.mem_subgroupOf.1 hu) _)
  rw [finsum_quotient_subgroupOf Γ U f hΓ hfU,
    finsum_quotient_subgroupOf Γ V (fun a => f a⁻¹) (fun a ha => (inv_mem_iff.1 (hΓ _ ha)))
      (fun w hw a => by rw [mul_inv_rev, hfV _ (inv_mem hw)])]
  exact h

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem levi_mul_rad_apply {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n}
    (hm : ∀ i j, β i ≠ β j → mat m i j = 0)
    (hu : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j) {i l : Fin n} (h : β l ≤ β i) :
    mat (m * u) i l = mat m i l := by
  rw [mat_mul, Matrix.mul_apply]
  have key : ∀ k, mat m i k * mat u k l = mat m i k * (1 : Matrix (Fin n) (Fin n) L) k l := by
    intro k
    by_cases hk : β i = β k
    · rw [hu k l (by rw [← hk]; exact h)]
    · rw [hm i k hk, zero_mul, zero_mul]
  simp_rw [key]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem leviRad : LeviRad := by
  intro L _ _ σ n β hσ m hm u hu
  refine ⟨?_, fun hmu => ?_⟩
  · show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
    intro i l h
    have hmi : m⁻¹ ∈ leviU σ β := inv_mem hm
    rw [mat_mul, Matrix.mul_apply]
    have key : ∀ k, mat (m * u) i k * mat m⁻¹ k l = mat m i k * mat m⁻¹ k l := by
      intro k
      by_cases hk : β k = β l
      · rw [levi_mul_rad_apply hm hu (by rw [hk]; exact h)]
      · rw [hmi k l hk, mul_zero, mul_zero]
    simp_rw [key]
    rw [← Matrix.mul_apply, ← mat_mul, mul_inv_cancel, mat_one]
  · rw [mem_KU_iff hσ] at hmu ⊢
    intro i l
    by_cases hk : β i = β l
    · rw [← levi_mul_rad_apply hm hu (le_of_eq hk.symm)]
      exact hmu i l
    · rw [hm i l hk]
      exact zero_mem _

end GlobalTheory.SatakeWeyl
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  first | (exact @GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (exact GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (intros; apply GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq  <;> assumption)
end

section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ → ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  first | exact @GlobalTheory.HeckePoisson.lat_isZLattice | exact GlobalTheory.HeckePoisson.lat_isZLattice | (intros; apply GlobalTheory.HeckePoisson.lat_isZLattice <;> assumption)
end

end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq : GlobalTheory.SatakeWeyl.IntIndex := by
  first | exact @GlobalTheory.SatakeWeyl.intIndex | exact GlobalTheory.SatakeWeyl.intIndex | (intros; apply GlobalTheory.SatakeWeyl.intIndex <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.contracting_automorphism_subgroup_chain_index : GlobalTheory.SatakeWeyl.ChainIndex := by
  first | exact @GlobalTheory.SatakeWeyl.chainIndex | exact GlobalTheory.SatakeWeyl.chainIndex | (intros; apply GlobalTheory.SatakeWeyl.chainIndex <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.finite_index_left_right_coset_sums_eq : GlobalTheory.SatakeWeyl.UnimodFin := by
  first | exact @GlobalTheory.SatakeWeyl.unimodFin | exact GlobalTheory.SatakeWeyl.unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimodFin <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex : GlobalTheory.SatakeWeyl.UnimodFin → GlobalTheory.SatakeWeyl.Unimod := by
  first | exact @GlobalTheory.SatakeWeyl.unimod_of_unimodFin | exact GlobalTheory.SatakeWeyl.unimod_of_unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimod_of_unimodFin <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts : GlobalTheory.SatakeWeyl.EmbMem := by
  first | exact @GlobalTheory.SatakeWeyl.embMem | exact GlobalTheory.SatakeWeyl.embMem | (intros; apply GlobalTheory.SatakeWeyl.embMem <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitary_diagonal_factorization_along_embedding : GlobalTheory.SatakeWeyl.EmbTorus := by
  first | exact @GlobalTheory.SatakeWeyl.embTorus | exact GlobalTheory.SatakeWeyl.embTorus | (intros; apply GlobalTheory.SatakeWeyl.embTorus <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq : GlobalTheory.SatakeWeyl.TorusConj := by
  first | exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | exact GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | (intros; apply GlobalTheory.SatakeWeyl.TorusConjProof.torusConj <;> assumption)

end
end

section

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitary_levi_normalizes_unipotent_radical : GlobalTheory.SatakeWeyl.LeviRad := by
  first | exact @GlobalTheory.SatakeWeyl.leviRad | exact GlobalTheory.SatakeWeyl.leviRad | (intros; apply GlobalTheory.SatakeWeyl.leviRad <;> assumption)

end
end
