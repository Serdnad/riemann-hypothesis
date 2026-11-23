module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.PointSumConj

theorem exists_conj_iff {G : Type} [Group G] (K : Subgroup G) (a m : G) :
    (∃ k ∈ K, a * k * a⁻¹ = m) ↔ a⁻¹ * m * a ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rw [this]; exact hk
  · intro h
    exact ⟨a⁻¹ * m * a, h, by group⟩

theorem mem_stab {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) (z : Γ) :
    z ∈ stab ι₁ ι₂ K₁ K₂ x ↔ x.1⁻¹ * ι₁ z * x.1 ∈ K₁ ∧ x.2⁻¹ * ι₂ z * x.2 ∈ K₂ := by
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, exists_conj_iff]

theorem finsum_dc_translate {G : Type} [Group G] (H H' K : Subgroup G) (a : G)
    (hH : ∀ h ∈ H, a * h * a⁻¹ ∈ H') (hH' : ∀ h ∈ H', a⁻¹ * h * a ∈ H) (F F' : G → ℂ)
    (hF : ∀ h ∈ H, ∀ k ∈ K, ∀ x, F (h * x * k) = F x) (hF' : ∀ x, F' (a * x) = F x) :
    ∑ᶠ q : DoubleCoset.Quotient (H' : Set G) (K : Set G), F' (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G), F (Quotient.out q) := by
  have key : ∀ x, F' (Quotient.out (DoubleCoset.mk H' K (a * x))) = F x := by
    intro x
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H' K (a * x))).symm
    rw [he]
    have : h' * (a * x) * k = a * ((a⁻¹ * h' * a) * x * k) := by group
    rw [this, hF', hF _ (hH' _ hh') _ hk]
  refine (finsum_eq_of_bijective (fun q : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    DoubleCoset.mk H' K (a * Quotient.out q)) ⟨?_, ?_⟩ (fun q => (key _).symm)).symm
  · intro q₁ q₂ h
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1 h
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    refine (@DoubleCoset.eq _ _ H K _ _).2 ⟨a⁻¹ * h' * a, hH' _ hh', k, hk, ?_⟩
    have : Quotient.out q₂ = a⁻¹ * (a * Quotient.out q₂) := by group
    rw [this, he]; group
  · intro q'
    refine ⟨DoubleCoset.mk H K (a⁻¹ * Quotient.out q'), ?_⟩
    obtain ⟨h, hh, k, hk, he⟩ := (@DoubleCoset.eq _ _ H K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H K (a⁻¹ * Quotient.out q'))).symm
    simp only
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' q']
    exact (@DoubleCoset.eq _ _ H' K _ _).2 ⟨(a * h * a⁻¹)⁻¹, H'.inv_mem (hH _ hh), k⁻¹, K.inv_mem hk, by group⟩

end GlobalTheory.PointSumConj

namespace GlobalTheory.PointSumConj

theorem conj_mem_iff {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) (m : G) :
    k⁻¹ * m * k ∈ K ↔ m ∈ K := by
  rw [Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk)]

theorem card_stab_translate {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (y : Γ) (x k : G₁ × G₂) (hk : k ∈ K₁.prod K₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ ((ι₁ y, ι₂ y) * x * k)) = Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
  rw [Subgroup.mem_prod] at hk
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj y).toEquiv fun z => ?_)).symm
  simp only [SetLike.mem_coe, mem_stab, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    Prod.fst_mul, Prod.snd_mul, map_mul, map_inv]
  have e1 : (ι₁ y * x.1 * k.1)⁻¹ * (ι₁ y * ι₁ z * (ι₁ y)⁻¹) * (ι₁ y * x.1 * k.1) =
      k.1⁻¹ * (x.1⁻¹ * ι₁ z * x.1) * k.1 := by group
  have e2 : (ι₂ y * x.2 * k.2)⁻¹ * (ι₂ y * ι₂ z * (ι₂ y)⁻¹) * (ι₂ y * x.2 * k.2) =
      k.2⁻¹ * (x.2⁻¹ * ι₂ z * x.2) * k.2 := by group
  rw [e1, e2, conj_mem_iff K₁ hk.1, conj_mem_iff K₂ hk.2]

theorem stab_conj {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (g₁ : G₁) (g₂ : G₂) (x : G₁ × G₂) :
    stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) K₁ K₂
      ((g₁⁻¹, g₂⁻¹) * x) = stab ι₁ ι₂ K₁ K₂ x := by
  ext z
  simp only [mem_stab, Prod.fst_mul, Prod.snd_mul, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (g₁⁻¹ * x.1)⁻¹ * (g₁⁻¹ * ι₁ z * g₁⁻¹⁻¹) * (g₁⁻¹ * x.1) = x.1⁻¹ * ι₁ z * x.1 := by group
  have e2 : (g₂⁻¹ * x.2)⁻¹ * (g₂⁻¹ * ι₂ z * g₂⁻¹⁻¹) * (g₂⁻¹ * x.2) = x.2⁻¹ * ι₂ z * x.2 := by group
  rw [e1, e2]

theorem pointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ g₁ δ g₂ f φ hf hφ hγ hδ
  unfold pointSum
  refine finsum_dc_translate (ι₁.prod ι₂).range
    (((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁).prod ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)).range
    (K₁.prod K₂) (g₁⁻¹, g₂⁻¹) ?_ ?_
    (fun x => ((Nat.card (stab ι₁ ι₂ K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)))
    (fun x => ((Nat.card (stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)
      K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * (g₁⁻¹ * γ * g₁) * x.1) * φ (x.2⁻¹ * (g₂⁻¹ * δ * θ g₂) * θ x.2))) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply] <;> group
  · rintro _ ⟨y, rfl⟩ k hk x
    have hk' := (Subgroup.mem_prod).1 hk
    simp only [MonoidHom.prod_apply] at *
    rw [card_stab_translate ι₁ ι₂ K₁ K₂ y x k hk]
    congr 2
    · have e : ((ι₁ y, ι₂ y) * x * k).1⁻¹ * γ * ((ι₁ y, ι₂ y) * x * k).1 =
          k.1⁻¹ * (x.1⁻¹ * ((ι₁ y)⁻¹ * γ * ι₁ y) * x.1) * k.1 := by simp only [Prod.fst_mul]; group
      have e' : (ι₁ y)⁻¹ * γ * ι₁ y = γ := by rw [mul_assoc, ← hγ y]; group
      rw [e, e', hf _ hk'.1]
    · have e : ((ι₁ y, ι₂ y) * x * k).2⁻¹ * δ * θ ((ι₁ y, ι₂ y) * x * k).2 =
          k.2⁻¹ * (x.2⁻¹ * ((ι₂ y)⁻¹ * δ * θ (ι₂ y)) * θ x.2) * θ k.2 := by
        simp only [Prod.snd_mul, map_mul]; group
      have e' : (ι₂ y)⁻¹ * δ * θ (ι₂ y) = δ := by rw [mul_assoc, ← hδ y]; group
      rw [e, e', hφ _ hk'.2]
  · intro x
    rw [stab_conj]
    congr 2
    · congr 1; simp only [Prod.fst_mul]; group
    · congr 1; simp only [Prod.snd_mul, map_mul, map_inv]; group

end GlobalTheory.PointSumConj
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ Γ' G₁ G₂ _ _ _ _ e ι₁ ι₂ θ K₁ K₂ γ δ f φ
  have hprod : (ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom) = (ι₁.prod ι₂).comp e.toMonoidHom := by
    ext x <;> rfl
  have hR : ((ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom)).range = (ι₁.prod ι₂).range := by
    rw [hprod, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  have hS : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
    intro x
    have h : stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁ ι₂ K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [h]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun a => by simp [Subgroup.mem_comap]))
  unfold pointSum
  simp only [hS]
  rw [hR]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKLoc.IntFin

theorem finite_intK_quot_pow : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  intro p _ L hL m
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Euler.card_OK_quot_natCast p L hL (pow_ne_zero m hp)
  have hf : Finite (ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L ⧸ Ideal.span {((p ^ m : ℕ) : ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L)}) :=
    Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  push_cast at hf
  exact hf

end GlobalTheory.LKLoc.IntFin
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.orbit_sum_local_parts : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  first | exact @GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | exact GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | (intros; apply GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit <;> assumption)
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem sig_iterate_apply (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r k : ℕ)
    (g : GL (Fin n) (Kn p K r)) (i j : Fin n) :
    (((⇑(sig p K n r))^[k] g : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j
      = (⇑(frobR p K r))^[k] ((g : Matrix (Fin n) (Fin n) (Kn p K r)) i j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sig_iterate_r : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (Kn p K r),
    (⇑(sig p K n r))^[r] g = g := by
  intro p _ K hK n r hr g
  ext i j
  rw [sig_iterate_apply]
  rw [GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self p K hK r hr]

end GlobalTheory.LKLoc
end

section

open GlobalTheory.LKCount

noncomputable section
open scoped Classical

namespace GlobalTheory.LKCountPoint

section Gen
variable {G : Type} [Group G]

theorem mem_map_conj {K : Subgroup G} {a z : G} :
    z ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * z * a ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  ext z
  simp only [mem_map_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inf_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) (K : Subgroup G) :
    (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K.map (MulAut.conj t).toMonoidHom := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht, h2⟩

theorem relIndex_inf_inf_ne_zero (H : Subgroup G) {U K : Subgroup G} (h : U.relIndex K ≠ 0) :
    (H ⊓ U).relIndex (H ⊓ K) ≠ 0 := by
  have := Subgroup.relIndex_inter_ne_zero h H
  rwa [inf_comm U H, inf_comm K H] at this

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem prod_map_conj (A : Subgroup G₁) (B : Subgroup G₂) (x : G₁ × G₂) :
    (A.prod B).map (MulAut.conj x).toMonoidHom =
      (A.map (MulAut.conj x.1).toMonoidHom).prod (B.map (MulAut.conj x.2).toMonoidHom) := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

theorem twCent_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (a : G₁) (b : G₂) :
    GlobalTheory.BCT.twCent (θ₁.prodMap θ₂) (a, b) = (GlobalTheory.BCT.twCent θ₁ a).prod (GlobalTheory.BCT.twCent θ₂ b) := by
  ext z
  rw [Subgroup.mem_prod]
  show z * (a, b) = (a, b) * (θ₁.prodMap θ₂) z ↔ z.1 * a = a * θ₁ z.1 ∧ z.2 * b = b * θ₂ z.2
  rw [Prod.ext_iff]
  exact Iff.rfl

theorem relIndex_prod (A C : Subgroup G₁) (B D : Subgroup G₂) :
    (A.prod B).relIndex (C.prod D) = A.relIndex C * B.relIndex D := by
  have e : (A.prod B).subgroupOf (C.prod D) =
      ((A.subgroupOf C).prod (B.subgroupOf D)).comap (Subgroup.prodEquiv C D).toMonoidHom := by
    ext z
    exact Iff.rfl
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv C D).surjective,
    Subgroup.index_prod]
  rfl

theorem vol_prod (C₁ H₁ : Subgroup G₁) (C₂ H₂ : Subgroup G₂) :
    vol (C₁.prod C₂) (H₁.prod H₂) = vol C₁ H₁ * vol C₂ H₂ := by
  unfold vol
  rw [relIndex_prod, relIndex_prod]
  push_cast
  rw [div_mul_div_comm]

theorem stab_eq {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).comap (ι₁.prod ι₂) := by
  rw [prod_map_conj]
  ext g
  exact Iff.rfl

theorem card_stab {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (hι : Function.Injective (ι₁.prod ι₂)) (x : G₁ × G₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ x) =
      Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) := by
  rw [stab_eq, ← Subgroup.map_comap_eq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv

theorem finite_inter {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) (h : Finite (stab ι₁ ι₂ K₁ K₂ x)) :
    (((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) :
      Set (G₁ × G₂)).Finite := by
  rw [← Subgroup.map_comap_eq, ← stab_eq, Subgroup.coe_map]
  exact Set.Finite.image _ (Set.toFinite _)

end Prod

section Core
variable {G : Type} [Group G]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  simp [mem_map_conj]

theorem vol_self (A : Subgroup G) : vol A A = 1 := by
  simp [vol, Subgroup.relIndex_self]

theorem fold_sum (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
        ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) :=
  GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup Γ' T K F hΓT hF hfin hsupp

theorem massC_ne_zero_of_ne (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 :=
  GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support Γ' T K F hΓT hF hfin hsupp y hy

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Core

end GlobalTheory.LKCountPoint
end
end

section

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.SmallPf

theorem exists_dim (F : Type) [Field F] {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Sp F) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨d, h₁, -⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem main : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  intro F _ Y W j hj
  have hp := W.proj
  have hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str) := by
    obtain ⟨N, i, hi, hcomp⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    rw [← hcomp]; infer_instance
  obtain ⟨d, hd⟩ := exists_dim F (W.p₁ ≫ Y.str)
  have hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn)) := by
    have h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ :=
      specMap_functionFieldMap W.p₁
    rw [← Category.assoc, ← h1, Category.assoc, hY]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm
  have t₁ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY
  have t₂ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ
  have t₃ := @GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra
    (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁
  rw [t₂] at t₃
  have : d ≤ Y.dim + 1 := by exact_mod_cast t₃
  unfold Dbl.Small
  rw [hd]
  exact_mod_cast this

end GlobalTheory.FlagPush.SmallPf
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.discrepancy_sub_qCartier_coeff_nonpos : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ)
    (Δ D : X → ℚ) (η : RatForms p n) (x : X) (m mD : ℕ) (gG fD : X.functionFieldˣ) (δ : ℚ),
    IsEffQDiv Δ → IsQCart D → δ ≤ 1 → 0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) →
    ∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing x) → discrep E η m gG - (1 - δ) * (E.ord fD / mD) ≤ 0 := by
  first | exact @GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart | exact GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart | (intros; apply GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart <;> assumption)
end
