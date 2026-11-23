module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle995
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle009
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.GlobalFields.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

section

noncomputable section

open GlobalTheory.Cong MvPolynomial

namespace UpperTheory.Gal.Gen

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

private theorem polyApprox_cut {η : J → k} {T : Set (J → k)} {Q : MvPolynomial J ℤ} (hQ : aeval η Q ≠ 0)
    (h : PolyApprox η T) : PolyApprox η {x | x ∈ T ∧ aeval x Q ≠ 0} := by
  classical
  intro ε hε
  have hq : 0 < ‖aeval η Q‖ := norm_pos_iff.2 hQ
  obtain ⟨s, c, hs, hc⟩ := h (ε * ‖aeval η Q‖) (mul_pos hε hq)
  refine ⟨s.filter (fun x => aeval x Q ≠ 0), fun x => c x * aeval x Q / aeval η Q, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact ⟨hs hx.1, hx.2⟩
  · intro P
    have e1 : ∑ x ∈ s.filter (fun x => aeval x Q ≠ 0), c x * aeval x Q / aeval η Q * aeval x P
        = (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [Finset.sum_filter_of_ne, Finset.sum_div]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_mul]
        ring
      · intro x _ hx hQx
        apply hx
        simp [hQx]
    rw [e1]
    have e2 : aeval η P - (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q
        = (aeval η (P * Q) - ∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [map_mul, sub_div, mul_div_assoc, div_self hQ, mul_one]
    rw [e2, norm_div, div_le_iff₀ hq]
    exact hc (P * Q)

private theorem polyApprox_trans {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hS : ∀ η ∈ S, PolyApprox η T) : PolyApprox θ T := by
  classical
  intro ε hε
  obtain ⟨s, c, hs, hc⟩ := h (ε / 2) (by positivity)
  have hM0 : 0 ≤ ∑ η ∈ s, ‖c η‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε2 : 0 < ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) := by positivity
  have hT : ∀ η ∈ S, ∃ (t : Finset (J → k)) (d : (J → k) → k), (↑t : Set (J → k)) ⊆ T ∧
      ∀ P : MvPolynomial J ℤ, ‖aeval η P - ∑ ζ ∈ t, d ζ * aeval ζ P‖
        ≤ ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) :=
    fun η hη => hS η hη _ hε2
  choose! t d ht hd using hT
  refine ⟨s.biUnion t, fun ζ => ∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0), ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hζ
    obtain ⟨η, hη, hζ⟩ := hζ
    exact ht η (hs hη) hζ
  · intro P
    have hsum : ∑ ζ ∈ s.biUnion t, (∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0)) * aeval ζ P
        = ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η hη => ?_
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_biUnion_of_mem t hη)
      · intro ζ hζ
        rw [if_neg (Finset.mem_sdiff.1 hζ).2]
        ring
      · intro ζ hζ
        rw [if_pos hζ]
        ring
    rw [hsum]
    have split : aeval θ P - ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P
        = (aeval θ P - ∑ η ∈ s, c η * aeval η P)
          + ∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [split]
    calc _ ≤ ‖aeval θ P - ∑ η ∈ s, c η * aeval η P‖
          + ‖∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ∑ η ∈ s, ‖c η‖ * (ε / (2 * (∑ η ∈ s, ‖c η‖ + 1))) := by
          gcongr
          · exact hc P
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η hη => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hd η (hs hη) P) (norm_nonneg _)
      _ ≤ ε := by
          rw [← Finset.sum_mul]
          generalize ∑ η ∈ s, ‖c η‖ = M at hM0 ⊢
          have h1 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          have h2 : M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
            field_simp
          have h3 : ε / 2 * (M / (M + 1)) ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h1
          linarith

theorem combine_pf : Combine := by
  intro k _ _ J θ S T Q hθ h
  exact polyApprox_trans hθ fun η hη => polyApprox_cut (h η hη).1 (h η hη).2

end UpperTheory.Gal.Gen

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem finset_sup_finrank_le {ι M : Type*} [AddCommGroup M] [Module ℂ M] (S : Finset ι)
    (A : ι → Submodule ℂ M) (r : ℝ)
    (h : ∀ i ∈ S, FiniteDimensional ℂ (A i) ∧ (Module.finrank ℂ (A i) : ℝ) ≤ r) :
    FiniteDimensional ℂ (S.sup A : Submodule ℂ M) ∧
      (Module.finrank ℂ (S.sup A : Submodule ℂ M) : ℝ) ≤ S.card * r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact ⟨inferInstance, by simp⟩
  | insert i S hi ih =>
    obtain ⟨hfd, hle⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfi, hli⟩ := h i (Finset.mem_insert_self i S)
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hi]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    have h1 : (Module.finrank ℂ (A i ⊔ S.sup A : Submodule ℂ M) : ℝ) ≤
        (Module.finrank ℂ (A i) : ℝ) + Module.finrank ℂ (S.sup A : Submodule ℂ M) := by
      exact_mod_cast Submodule.finrank_add_le_finrank_add_finrank (A i) (S.sup A)
    push_cast
    linarith

private theorem part_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a)
    (C : Subgroup (UA E a)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ) :
    part W C (fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ≤
      S.sup fun w => part W C fun U => ¬ GenAt w (Φ w) U := by
  refine iSup₂_le fun π hπ => ?_
  push_neg at hπ
  obtain ⟨w, hw, hg⟩ := hπ
  refine le_trans ?_ (Finset.le_sup (f := fun w => part W C fun U => ¬ GenAt w (Φ w) U) hw)
  exact le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : ¬ GenAt w (Φ w) π.V) => π.finPart W ⊓ fixedBy W C) π hg le_rfl

theorem UpperTheory.Gal.Gen.countGen_pf :
    UpperTheory.Gal.Gen.Count → UpperTheory.Gal.Gen.NeglAt → UpperTheory.Gal.Gen.CountGen := by
  classical
  intro hC hN E _ _ _ a w₀ hw₀ K hK J hJ W S Φ hD
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * ((S.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have key : ∀ w, ∃ n₀ : ℕ, w ∈ S → ∀ n, n₀ ≤ n →
      FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n₀, h⟩ := hC E a w₀ hw₀ K hK J hJ W _
        (hN E a K w₀ w (hD.split w hw) (hD.apart w hw) (hD.hyp w hw) (Φ w) (hD.ne w hw)) ε hεpos
      exact ⟨n₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose n₀ hn₀ using key
  refine ⟨S.sup n₀, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = S.sup n₀ := ⟨_, rfl⟩
  rw [← hn]
  have hall : ∀ w ∈ S, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := fun w hw =>
    hn₀ w hw n (hn ▸ Finset.le_sup (f := n₀) hw)
  obtain ⟨hfd, hle⟩ := finset_sup_finrank_le S
    (fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) _ hall
  have hsub := part_le_sup W (lev K w₀ (J n)) S Φ
  refine ⟨Submodule.finiteDimensional_of_le hsub, ?_⟩
  have hmono := Submodule.finrank_mono hsub
  have hmono' : (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Module.finrank ℂ (S.sup fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U :
        Submodule ℂ (algForms W)) := by
    exact_mod_cast hmono
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := ⟨_, rfl⟩
  rw [← hNdef] at hle
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hfin : 2 * ((S.card : ℝ) * (ε * N)) ≤ N := by
    have h2 : 2 * ((S.card : ℝ) * (ε * N)) = (S.card : ℝ) / ((S.card : ℝ) + 1) * N := by
      rw [hε]; field_simp
    rw [h2]
    have h3 : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hc]; linarith
    nlinarith
  have : (2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    rw [← hNdef]; linarith
  exact_mod_cast this
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.restrict_pf :
    UpperTheory.Gal.Gen.Restrict := by
  classical
  intro k _ _ J J' i θ S h ε hε
  obtain ⟨s, c, hs, hc⟩ := h ε hε
  refine ⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ
    obtain ⟨η, hη, rfl⟩ := hζ
    exact ⟨η, hs hη, rfl⟩
  · intro P
    have key : ∀ η : J' → k,
        MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P) := by
      intro η
      rw [MvPolynomial.aeval_rename]
    calc _ = ‖MvPolynomial.aeval θ (MvPolynomial.rename i P)
          - ∑ η ∈ s, c η * MvPolynomial.aeval η (MvPolynomial.rename i P)‖ := by
          congr 2
          · exact key θ
          · rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i))
              (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun η hη => ?_
            rw [← (Finset.mem_filter.1 hη).2, key]
      _ ≤ ε := hc _
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ellGrp_pf :
    UpperTheory.Gal.Gen.EllGrp := by
  classical
  intro G H _ _ Γ C lam hyp
  have key : ∀ (r γ₁ γ₂ : G), γ₁ ∈ Γ → γ₂ ∈ Γ → ∀ c₁ c₂ : C,
      γ₁ * r * c₁ = γ₂ * r * c₂ → lam c₁ = lam c₂ := by
    intro r γ₁ γ₂ h1 h2 c₁ c₂ h
    have h' : γ₂⁻¹ * γ₁ * r = r * ((c₂ * c₁⁻¹ : C) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc γ₂⁻¹ * γ₁ * r = γ₂⁻¹ * (γ₁ * r * c₁) * (c₁ : G)⁻¹ := by group
        _ = γ₂⁻¹ * (γ₂ * r * c₂) * (c₁ : G)⁻¹ := by rw [h]
        _ = r * ((c₂ : G) * (c₁ : G)⁻¹) := by group
    have h3 := hyp r _ (Γ.mul_mem (Γ.inv_mem h2) h1) _ h'
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3.symm
  obtain ⟨R, hR⟩ : ∃ R : G → Set G, ∀ g x, x ∈ R g ↔ ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c :=
    ⟨fun g => {x | ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c}, fun _ _ => Iff.rfl⟩
  have hself : ∀ g, g ∈ R g := fun g => (hR g g).2 ⟨1, Γ.one_mem, 1, by simp⟩
  have hsub : ∀ g g', g' ∈ R g → R g' ⊆ R g := by
    intro g g' hg x hx
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    obtain ⟨γ', hγ', c', e'⟩ := (hR g' x).1 hx
    exact (hR g x).2 ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by rw [e', e, Subgroup.coe_mul]; group⟩
  have hsymm : ∀ g g', g' ∈ R g → g ∈ R g' := by
    intro g g' hg
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    exact (hR g' g).2 ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by rw [e, Subgroup.coe_inv]; group⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : G → G, ∀ g, rep g = Classical.epsilon (· ∈ R g) :=
    ⟨_, fun _ => rfl⟩
  have hrepR : ∀ g g', g' ∈ R g → rep g' = rep g := by
    intro g g' hg
    have hRR : R g' = R g := Set.Subset.antisymm (hsub g g' hg) (hsub g' g (hsymm g g' hg))
    rw [hrep, hrep, hRR]
  have hdec : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    have hm : rep g ∈ R g := by
      rw [hrep]
      exact Classical.epsilon_spec ⟨g, hself g⟩
    obtain ⟨γ, hγ, c, e⟩ := (hR g _).1 hm
    exact ⟨c⁻¹, γ⁻¹, Γ.inv_mem hγ, by rw [e, Subgroup.coe_inv]; group⟩
  let ℓ : G → H := fun g => lam (Classical.choose (hdec g))
  have hℓ : ∀ g γ, γ ∈ Γ → ∀ c : C, g = γ * rep g * c → ℓ g = lam c := by
    intro g γ hγ c e
    obtain ⟨γ0, h0, e0⟩ := Classical.choose_spec (hdec g)
    exact key (rep g) γ0 γ h0 hγ _ _ (e0.symm.trans e)
  refine ⟨ℓ, ?_, ?_⟩
  · intro γ hγ g
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (γ * g) = rep g := hrepR g _ ((hR g _).2 ⟨γ, hγ, 1, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0]
    apply hℓ (γ * g) (γ * γ0) (Γ.mul_mem hγ h0) c0
    rw [hr]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
  · intro g c
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (g * c) = rep g := hrepR g _ ((hR g _).2 ⟨1, Γ.one_mem, c, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0, ← map_mul]
    apply hℓ (g * c) γ0 h0 (c0 * c)
    rw [hr, Subgroup.coe_mul]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact inv_lt_one_of_one_lt₀ h2

theorem UpperTheory.Gal.Gen.denseGen_pf :
    UpperTheory.Gal.Gen.Step → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.DenseGen := by
  intro hStep hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf ε hε
  have hl1 := norm_l_lt_one l
  have hr0 : 0 ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ := Real.sqrt_nonneg _
  have hr1 : Real.sqrt ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hl1
  have key : ∀ m : ℕ, ∀ f ∈ fixedBy W K,
      ∃ G ∈ part W K (fun U => ∀ w ∈ S, GenAt w (Φ w) U), ∃ e : UA E a → ℂ,
        (∀ g, ‖ι.symm (e g)‖ ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ ^ m) ∧
        ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g := by
    intro m
    induction m with
    | zero =>
      intro f _
      refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun g => ?_, fun v g => ?_⟩
      · simp
      · simp
    | succ m ih =>
      intro f hf
      obtain ⟨G, hG, e, he, hfe⟩ := ih f hf
      have hGf : G ∈ fixedBy W K := (hPF E a W K _).2.1 hG
      obtain ⟨G', hG', e', he', hfe'⟩ :=
        hStep E l ι a ha w₀ hl hs K hK W S Φ hS (f - G) (Submodule.sub_mem _ hf hGf)
      refine ⟨G + G', Submodule.add_mem _ hG hG', fun g => e' g * e g, fun g => ?_, fun v g => ?_⟩
      · rw [map_mul, norm_mul, pow_succ, mul_comm]
        exact mul_le_mul (he g) (Real.le_sqrt_of_sq_le (he' g)) (norm_nonneg _) (pow_nonneg hr0 _)
      · have h1 := hfe' v g
        have h2 := hfe v g
        have h3 : (f - G).1 v g = f.1 v g - G.1 v g := by simp
        have h4 : (G + G').1 v g = G.1 v g + G'.1 v g := by simp
        rw [h3] at h1
        rw [h4, mul_assoc, ← h2, ← h1]
        ring
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hr1
  obtain ⟨G, hG, e, he, hfe⟩ := key m f hf
  exact ⟨G, hG, e, fun g => (he g).trans hm.le, hfe⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem eig_of_hasSat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) {v : V} (hv : v ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := a))) (hv0 : v ≠ 0)
    (l : Module.Dual ℂ V) : UpperTheory.V.Af.Smo.Eig w B fun g => l (ρ g v) := by
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, mul_apply_eq_comp, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  · have he := (hB.2 v hv hv0).2.2.2 ϖ hϖ j hj
    let ev : V →+ ℂ :=
      { toFun := fun ψ => l (ρ y ψ)
        map_zero' := by simp
        map_add' := fun _ _ => by simp }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ v)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg ev he).trans ?_))
    · simp [ev, map_mul]
    · simp [ev]

private theorem eigen_top {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    [MeasurableSpace (GL (Fin a) (w.adicCompletion E))] [BorelSpace (GL (Fin a) (w.adicCompletion E))]
    (μ : Measure (GL (Fin a) (w.adicCompletion E))) [μ.IsHaarMeasure] (z : Fin a → ℂˣ)
    {f : GL (Fin a) (w.adicCompletion E) → ℂ} (hE : UpperTheory.V.Af.Smo.Eig w (Finset.univ.val.map z) f)
    (hf : ∀ g, ∀ k ∈ GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a, f (g * k) = f g) :
    eigenSubalgebra μ z f hf = ⊤ := by
  obtain ⟨hKeq, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict E a w
  have hTj : UpperTheory.V.Af.Smo.TjSet := UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict
  have hT : ∀ r ≤ a, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
    intro r hr
    refine GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_
    rw [hKeq, ← hTj E a w r hr, hE.eig _ hu r hr g, hq r hr,
      GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]
  exact eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT a le_rfl))

end UpperTheory.Gal.Gen

open GroundTheory.Automorphic in
theorem UpperTheory.Gal.Gen.locOp_pf :
    UpperTheory.Gal.Gen.RepsEx → UpperTheory.Gal.Gen.Planch → UpperTheory.Gal.Gen.LocOp := by
  intro hR hP E _ _ w a
  classical
  borelize (GL (Fin a) (w.adicCompletion E))
  let μ : Measure (GL (Fin a) (w.adicCompletion E)) := Measure.haar
  obtain ⟨C0, hC0⟩ := hP (w.adicCompletion E) a μ
  have hKeq := (UpperTheory.V.Af.Smo.sphDict E a w).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (GLnLocal.integralGL (w.adicCompletion E) a : Set (GL (Fin a) (w.adicCompletion E))) := ⟨_, rfl⟩
  refine ⟨m ^ 2 * C0, fun p hp => ?_⟩
  rw [← range_satakeTransform (μ := μ) (F := w.adicCompletion E) (n := a)] at hp
  obtain ⟨H, rfl⟩ := (AlgHom.mem_range _).1 hp
  obtain ⟨T, hT⟩ := hR (w.adicCompletion E) a μ H
  let h : GL (Fin a) (w.adicCompletion E) →₀ ℂ :=
    Finsupp.onFinset T (fun g => if g ∈ T then (m : ℂ) * (H : HeckeAlgebra μ) g else 0) (fun g hg => by
      by_contra hgT
      simp [hgT] at hg)
  have hsupp : h.support ⊆ T := Finsupp.support_onFinset_subset
  have hval : ∀ g ∈ T, h g = (m : ℂ) * (H : HeckeAlgebra μ) g := fun g hg => by
    simp [h, hg]
  refine ⟨h, fun g hg g' hg' hk => hT.1 g (hsupp hg) g' (hsupp hg') (hKeq ▸ hk), ?_, ?_⟩
  · calc ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ ∑ g ∈ T, ‖h g‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ => by positivity
      _ = m ^ 2 * ∑ g ∈ T, ‖(H : HeckeAlgebra μ) g‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [hval g hg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ m ^ 2 * (C0 * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) (satakeTransform μ H)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hC0 H T hT) (by positivity)
      _ = _ := by ring
  · intro σ z hz v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [opOf]
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    have hE := eig_of_hasSat w σ.ρ hz hv hv0 l
    have hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) a, l (σ.ρ (g * k) v) = l (σ.ρ g v) := by
      rw [hKeq]
      exact hE.inv
    have h1 : H ∈ eigenSubalgebra μ z (fun g => l (σ.ρ g v)) hf := eigen_top w μ z hE hf ▸ Algebra.mem_top
    have h2 := h1 1
    simp only [one_mul, map_one, one_apply_eq_self] at h2
    have h3 := hT.2 (fun g => l (σ.ρ g v)) hf
    have h4 : l (opOf σ.ρ h v) = (m : ℂ) * ∑ g ∈ T, (H : HeckeAlgebra μ) g * l (σ.ρ g v) := by

      rw [opOf, Finsupp.sum_of_support_subset h hsupp _ (by simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smul, hval g hg, smul_eq_mul, mul_assoc]
    rw [map_sub, map_smul, smul_eq_mul, h4, hm, ← h3, h2, sub_self]
end
