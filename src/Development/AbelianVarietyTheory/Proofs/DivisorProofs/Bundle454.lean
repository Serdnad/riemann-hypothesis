module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle140
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
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
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.SubstCalc

variable {R : Type} [CommRing R]

theorem constantCoeff_subst_of_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem hasSubst_elim {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {d : ℕ} {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_rules_alt : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  intro R _ d τ τ' _ u v hu hv
  have hs := hasSubst_elim hu hv
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold at2 inL
    rw [subst_comp_subst_apply hX hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro f
    unfold at2 inR
    rw [subst_comp_subst_apply hY hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro c c'
    unfold at2
    exact ⟨subst_add hs _ _, subst_sub hs _ _⟩
  · intro c
    unfold at2
    exact constantCoeff_subst_of_zero (fun s => by cases s <;> simp [hu, hv]) c
  · intro c
    have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inl i))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
    unfold swap at2
    rw [subst_comp_subst_apply hW hs]
    congr 1
    funext s
    cases s <;> simp [subst_X hs]
  · intro e μ hμ f
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hs]
  · intro a ha c
    exact subst_powerSeriesEvalTwoGroups hu hv ha c
  · intro c hc
    set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim u v) with hw
    have hw0 : ∀ t, constantCoeff (w t) = 0 := fun t => by
      rcases t with t | t | t <;> simp [hw, hu, hv]
    have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
      unfold x1; rw [subst_X hsw]; rfl
    have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = u i := fun i => by
      unfold x2; rw [subst_X hsw]; rfl
    have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = v i := fun i => by
      unfold x3; rw [subst_X hsw]; rfl
    have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        op (addLaw R d) a b = a + b := by
      intro a b ha hb
      funext i
      unfold op addLaw at2
      have := hasSubst_elim ha hb
      rw [subst_add this, subst_X this, subst_X this]
      rfl
    have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        ∀ i, constantCoeff ((a + b) i) = 0 := by
      intro a b ha hb i; simp [ha, hb]
    have key := congrArg (subst w) hc
    unfold cob2 at key
    rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
    rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
      subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
      subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
    have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
      intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
    rw [e, e] at key
    simp only [h1, h2, h3] at key
    have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
      simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
    rw [e0] at key
    convert key using 2

end GlobalTheory.Katz.SubstCalc
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace Katz
namespace WittHaus

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha' : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h1 := constantCoeff_subst_eq_zero ha ha' (f := f - C (constantCoeff f)) (by simp)
  have h2 : subst a (C (constantCoeff f) : MvPowerSeries σ R) = C (constantCoeff f) := by
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes (constantCoeff f)
  rw [← coe_substAlgHom ha, map_sub, coe_substAlgHom ha, h2, map_sub, constantCoeff_C] at h1
  exact sub_eq_zero.mp h1

theorem isUnit_natCast_of_not_dvd (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (u : ℕ)
    (hu : ¬ p ∣ u) : IsUnit (u : WittVector p k) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have : (WittVector.constantCoeff (u : WittVector p k)) = 0 := h0
  rw [map_natCast, CharP.cast_eq_zero_iff k p] at this
  exact hu this

theorem constantCoeff_int (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) {f : MvPowerSeries (Fin d) (Fr p k)}
    (hf : f ∈ quasiLog p h) :
    ∃ w : WittVector p k, coeff 0 f = algebraMap _ (Fr p k) w := by
  obtain ⟨w, hw⟩ := hf.2 0
  have hμ : HasSubst (fun i => lift p (μ i)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (h.const i)
  have hX : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hc : coeff 0 (cob1 (fun i => lift p (μ i)) f) = - coeff 0 f := by
    simp only [coeff_zero_eq_constantCoeff_apply]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_of_zero' hμ (fun i => constantCoeff_lift p (h.const i)),
      constantCoeff_subst_of_zero' hX (fun _ => constantCoeff_X _),
      constantCoeff_subst_of_zero' hY (fun _ => constantCoeff_X _)]
    ring
  refine ⟨-(1 * w), ?_⟩
  rw [map_neg, ← hw, hc, neg_neg]

theorem haus : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    IsHausdorff (Ideal.span {(p : WittVector p k)}) (Mod p h) := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have key : ∀ n : ℕ, ∃ g : quasiLog p h,
      (f : MvPowerSeries (Fin d) (Fr p k)) - ((p : WittVector p k) ^ n) • (g : MvPowerSeries (Fin d) (Fr p k))
        ∈ intBy p k (Fin d) 1 := by
    intro n
    have h1 := (SModEq.sub_mem.mp (hx n))
    rw [sub_zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, -, hb⟩ := h1
    induction b using Submodule.Quotient.induction_on with | _ g => ?_
    refine ⟨g, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at hb
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hb
    have := neg_mem hb
    simpa [neg_sub] using this
  rw [Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  intro α
  by_cases hα : α = 0
  · subst hα
    obtain ⟨w, hw⟩ := constantCoeff_int p h f.2
    exact ⟨w, by rw [one_mul]; exact hw⟩
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra! hc
    exact hα (Finsupp.ext hc)
  obtain ⟨v, u, hu, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Nat.Prime.ne_one Fact.out)
  obtain ⟨g, hg⟩ := key v
  obtain ⟨w₁, hw₁⟩ := hg α
  obtain ⟨w₂, hw₂⟩ := g.2.1 α i
  obtain ⟨U, hU⟩ := isUnit_natCast_of_not_dvd p k u hu
  refine ⟨w₁ + ↑U⁻¹ * w₂, ?_⟩
  have hsm : coeff α (((p : WittVector p k) ^ v) • (g : MvPowerSeries (Fin d) (Fr p k))) =
      algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) := by
    rw [← algebraMap_smul (Fr p k), LinearMap.map_smul, smul_eq_mul]
  have hα' : ((α i : ℕ) : Fr p k) = algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * algebraMap _ (Fr p k) (U : WittVector p k) := by
    rw [hU, ← map_mul, hm]; push_cast; rfl
  rw [map_sub, hsm] at hw₁
  have e2 : algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) =
      algebraMap _ (Fr p k) (↑U⁻¹ * w₂) := by
    rw [map_mul, ← hw₂, hα']
    have : algebraMap _ (Fr p k) (↑U⁻¹ : WittVector p k) * algebraMap _ (Fr p k) (U : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)))) * this
  rw [one_mul, map_add (f := _), ← e2]
  rw [one_mul] at hw₁
  linear_combination hw₁

end WittHaus
end Katz
end GlobalTheory
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.RedRules

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (σ : Type)

theorem inj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
  IsFractionRing.injective _ _

theorem coeff_smul' (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (α : σ →₀ ℕ) :
    coeff α (r • f) = algebraMap _ (Fr p k) r * coeff α f := by
  change r • coeff α f = _
  rw [Algebra.smul_def]

theorem intBy_one_iff (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨fun α => WittVector.constantCoeff (w α), fun α => ⟨w α, ?_, rfl⟩⟩
    rw [hw α, one_mul]
  · rintro ⟨g, hg⟩ α
    obtain ⟨w, hw, -⟩ := hg α
    exact ⟨w, by rw [one_mul, hw]⟩

theorem red_unique (f : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f g') : g = g' := by
  ext α
  obtain ⟨w, hw, hg⟩ := h α
  obtain ⟨w', hw', hg'⟩ := h' α
  have : w = w' := inj p k (hw.symm.trans hw')
  rw [← hg, ← hg', this]

theorem red_lift (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := fun α =>
  ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

theorem red_add_sub (f f' : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f' g') : Red p (f + f') (g + g') ∧ Red p (f - f') (g - g') := by
  constructor
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w + w', by rw [map_add (f := _), map_add (f := _), hw, hw'], by rw [map_add (f := _), map_add (f := _), hg, hg']⟩
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w - w', by rw [map_sub, map_sub, hw, hw'], by rw [map_sub, map_sub, hg, hg']⟩

theorem red_smul (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k)
    (h : Red p f g) : Red p (r • f) (WittVector.constantCoeff r • g) := by
  intro α
  obtain ⟨w, hw, hg⟩ := h α
  refine ⟨r * w, ?_, ?_⟩
  · rw [coeff_smul', hw, map_mul]
  · rw [map_mul, hg, MvPowerSeries.coeff_smul]

theorem constantCoeff_p_mul (v : WittVector p k) :
    WittVector.constantCoeff ((p : WittVector p k) * v) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem exists_p_mul [PerfectRing k p] (w : WittVector p k) (hw : WittVector.constantCoeff w = 0) :
    ∃ v, w = (p : WittVector p k) * v := by
  by_cases h0 : w = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  cases m with
  | zero =>
    rw [pow_zero, one_mul, WittVector.constantCoeff_apply] at hw
    exact absurd hw hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ, mul_comm _ (p : WittVector p k), mul_assoc]⟩

theorem intBy_p_iff [PerfectRing k p] (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ p ↔ Red p f 0 := by
  constructor
  · intro hf α
    obtain ⟨v, hv⟩ := hf α
    exact ⟨_, hv, by rw [constantCoeff_p_mul, map_zero]⟩
  · intro hf α
    obtain ⟨w, hw, h0⟩ := hf α
    rw [map_zero] at h0
    obtain ⟨v, rfl⟩ := exists_p_mul p k w h0
    exact ⟨v, hw⟩

theorem intBy_iff (c : WittVector p k) (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨(fun α => algebraMap _ (Fr p k) (w α) : MvPowerSeries σ (Fr p k)), fun α => ⟨w α, by rw [one_mul]; rfl⟩, ?_⟩
    ext α
    rw [hw α, map_mul]
    exact (coeff_smul' p k σ c (fun α => algebraMap _ (Fr p k) (w α)) α).symm
  · rintro ⟨g, hg, rfl⟩ α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨w, by rw [coeff_smul', hw, one_mul, map_mul]⟩

end GlobalTheory.Katz.RedRules

open GlobalTheory.Katz.RedRules in
theorem GlobalTheory.Katz.red_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  intro p _ k _ _ _ σ
  exact ⟨intBy_one_iff p k σ, red_unique p k σ, red_lift p k σ, red_add_sub p k σ, red_smul p k σ,
    intBy_p_iff p k σ, intBy_iff p k σ⟩
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.CobLead

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
private lemma subst_constantCoeff_zero_and_linear_coeff_eq {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    (w : Fin d ⊕ Fin d → MvPowerSeries τ R) (hw : ∀ s, constantCoeff (w s) = 0)
    (F G : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hFG : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≤ 1 → coeff α F = coeff α G)
    (hG : constantCoeff G = 0) :
    constantCoeff (subst w F) = 0 ∧ constantCoeff (subst w G) = 0 ∧
      ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ (subst w F) = coeff γ (subst w G) := by
  have hlow : ∀ H : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α H = 0) →
      constantCoeff (subst w H) = 0 := by
    intro H hH
    have h := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 1 H hw hw (fun _ _ _ => rfl) hH 0).1
      (by simp)
    rwa [coeff_zero_eq_constantCoeff_apply] at h
  have hG0 : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α G = 0 := by
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hG]
  refine ⟨hlow F (fun α hα => by rw [hFG α hα.le]; exact hG0 α hα), hlow G hG0, ?_⟩
  intro γ hγ
  have hdiff := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 2 (F - G) hw hw (fun _ _ _ => rfl)
    (fun α hα => by rw [map_sub, hFG α (by omega), sub_self]) γ).1 (by omega)
  rw [subst_sub (hasSubst_of_constantCoeff_zero hw), map_sub, sub_eq_zero] at hdiff
  exact hdiff

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.CobLead.cob_eq_additive_lead : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (_root_.GlobalTheory.Katz.addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = coeff γ (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.Katz.addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob2 μ c) = coeff γ (_root_.GlobalTheory.Katz.cob2 (_root_.GlobalTheory.Katz.addLaw R d) c) := by
  intro R _ d μ N hμ
  have hadd0 : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
    intro i
    simp [_root_.GlobalTheory.Katz.addLaw]
  have hμ0 : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hμ i 0 (by simp), coeff_zero_eq_constantCoeff_apply, hadd0]
  have hX : ∀ {ι κ : Type} (e : ι → κ) (s : ι), constantCoeff (X (e s) : MvPowerSeries κ R) = 0 :=
    fun _ _ => by simp
  refine ⟨fun f hf γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun c hc γ hγ => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    rw [map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ μ N f hμ0 hμ0 (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inl) (hX Sum.inl)
        (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inr) (hX Sum.inr)
        (fun _ _ _ => rfl) hf γ).1 hγ]
    simp
  · unfold _root_.GlobalTheory.Katz.cob1
    rw [map_sub, map_sub, map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ (_root_.GlobalTheory.Katz.addLaw R d) N f hμ0 hadd0
        (fun i γ' hγ' => hμ i γ' hγ'.le) hf γ).2 hγ]
  · have hpts : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) →
        (∀ s, constantCoeff (b s) = 0) → ∀ i,
          constantCoeff (_root_.GlobalTheory.Katz.op μ a b i) = 0 ∧
          constantCoeff (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) = 0 ∧
          ∀ γ' : τ →₀ ℕ, γ'.degree = 1 → coeff γ' (_root_.GlobalTheory.Katz.op μ a b i) =
            coeff γ' (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) := by
      intro τ a b ha hb i
      exact subst_constantCoeff_zero_and_linear_coeff_eq (Sum.elim a b) (fun s => by cases s <;> simp [ha, hb])
        (μ i) (_root_.GlobalTheory.Katz.addLaw R d i) (hμ i) (hadd0 i)
    have hs1 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x1]
    have hs2 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x2]
    have hs3 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x3]
    have h12 := hpts _ _ hs1 hs2
    have h23 := hpts _ _ hs2 hs3
    unfold _root_.GlobalTheory.Katz.cob2 _root_.GlobalTheory.Katz.at2
    rw [map_sub, map_add (f := _), map_sub, map_sub, map_add (f := _), map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
          _root_.GlobalTheory.Katz.x3)
        (Sum.elim (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) _root_.GlobalTheory.Katz.x1
          _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3) N c
        (fun s => by rcases s with s | s; exacts [(h12 s).1, hs3 s])
        (fun s => by rcases s with s | s; exacts [(h12 s).2.1, hs3 s])
        (fun s γ' hγ' => by rcases s with s | s; exacts [(h12 s).2.2 γ' hγ', rfl]) hc γ).2 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim _root_.GlobalTheory.Katz.x1
          (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3))
        (Sum.elim _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d)
          _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) N c
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).1])
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).2.1])
        (fun s γ' hγ' => by rcases s with s | s; exacts [rfl, (h23 s).2.2 γ' hγ']) hc γ).2 hγ]

end GlobalTheory.CobLead
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  first | (exact @GlobalTheory.genFibre_prime_meets_polynomial) | (exact GlobalTheory.genFibre_prime_meets_polynomial) | (intros; apply GlobalTheory.genFibre_prime_meets_polynomial  <;> assumption)
end
