module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle016
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Mathlib.RepresentationTheory.Character
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isCMExt_conj_fixed_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧
      (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧
      (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧
      (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hval : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E) := fun o => rfl
  have hmoved : ∃ θ : E, σ θ ≠ θ := by
    by_contra hc
    push_neg at hc
    have hc' := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have := h.2.2.2 τ y
    rw [hc y] at this
    simpa using this.symm
  refine ⟨hinv, ?_, hval, ?_⟩
  · intro x hx
    by_contra hne
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
    have hli : LinearIndependent F ![(1 : E), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        refine ⟨?_, rfl⟩
        simpa using hst
      · exfalso
        apply hne
        refine ⟨-s / t, ?_⟩
        have h1 : algebraMap F E s + algebraMap F E t * x = 0 := by
          simpa [Algebra.smul_def] using hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg, div_eq_iff ht']
        linear_combination -h1
    have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [h.2.2.1]; simp)
    have hid : σ.toLinearMap = LinearMap.id := by
      refine LinearMap.ext_on_range hspan ?_
      intro i
      fin_cases i
      · simp
      · simpa using hx
    obtain ⟨θ, hθ⟩ := hmoved
    exact hθ (by simpa using LinearMap.congr_fun hid θ)
  · intro I
    have hs : ∀ o : 𝓞 E, sO σ (sO σ o) = o := by
      intro o
      apply RingOfIntegers.ext
      rw [hval, hval, hinv]
    let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sO σ) (sO σ)
      (RingHom.ext hs) (RingHom.ext hs)
    exact GlobalTheory.absNorm_map_ringEquiv_self e I

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspSum

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem blk_unip (b : ι → Fin s) (c : Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    Formalism.IrreducibleCountingLemmas.TYPES.blk K b c (g : Matrix ι ι K) = 1 := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply, Subtype.mk.injEq]
  exact hg.2 i l (hi.trans hl.symm)


omit [Fintype K] [DecidableEq K] [Fintype ι] in
theorem entry_of_blk (b : ι → Fin s) {M : Matrix ι ι K}
    (h : ∀ c, Formalism.IrreducibleCountingLemmas.TYPES.blk K b c M = 1) (i j : ι) (hij : b i = b j) :
    M i j = if i = j then 1 else 0 := by
  have := congrFun (congrFun (h (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  simpa only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.mk.injEq] using this

theorem unip_mul_mem (b : ι → Fin s) {g h : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) (hh : h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    g * h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨mul_mem hg.1 hh.1, entry_of_blk b fun c => ?_⟩
  rw [Units.val_mul, Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.1 hh.1.1, blk_unip b c hg, blk_unip b c hh,
    one_mul]

theorem unip_inv_mem (b : ι → Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) : g⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨inv_mem hg.1, entry_of_blk b fun c => ?_⟩
  have h := Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.2 hg.1.1
  rw [Units.inv_mul, blk_unip b c hg, mul_one] at h
  rw [← h]
  exact Matrix.submatrix_one _ Subtype.val_injective

open Classical in
theorem sum_rho_unip (τ : FDRep ℂ (GL ι K)) (hc : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ)
    (b : ι → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s) :
    (∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0) = 0 := by
  set P : Module.End ℂ τ := ∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0
    with hP
  have hfix : ∀ a ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b, τ.ρ a * P = P := by
    intro a ha
    rw [hP, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft a)
      (fun v : GL ι K => if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : a * v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b ↔ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
      refine ⟨fun h => ?_, unip_mul_mem b ha⟩
      simpa using unip_mul_mem b (unip_inv_mem b ha) h
    simp only [Equiv.coe_mulLeft, hiff]
    split_ifs
    · rw [map_mul]
    · rw [mul_zero]
  refine LinearMap.ext fun w => ?_
  exact hc s b hb hs (P w) fun a ha => LinearMap.congr_fun (hfix a ha) w

theorem twoBlock_surjective {d j : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    Function.Surjective (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
  intro c
  fin_cases c
  · exact ⟨⟨0, by omega⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]; omega⟩
  · exact ⟨⟨j, hjd⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]⟩

theorem sum_character_translate :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  intro K _ _ _ d j τ hj hjd hc u
  classical
  have h0 := sum_rho_unip τ hc (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) (twoBlock_surjective hj hjd) le_rfl
  have h1 : LinearMap.trace ℂ τ (τ.ρ u * ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.ρ v else 0) = 0 := by
    rw [h0, mul_zero, map_zero]

  rw [Finset.mul_sum, map_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h1
  split_ifs
  · rw [FDRep.character, map_mul]
  · rw [mul_zero, map_zero]

end GlobalTheory.CompanionTheory.TyFin.CuspSum
end
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.UnitRoot

open Polynomial

theorem coeff_prod_mem {S : Type} [CommRing S] (m : Ideal S) (s : Multiset S)
    (h : ∀ b ∈ s, b ∈ m) :
    ∀ k < Multiset.card s, ((s.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
  induction s using Multiset.induction_on with
  | empty => intro k hk; simp at hk
  | cons a s ih =>
    intro k hk
    have ha : a ∈ m := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
    rw [Multiset.card_cons] at hk
    cases k with
    | zero =>
      simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
      exact m.neg_mem (m.mul_mem_right _ ha)
    | succ k =>
      simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
      exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)

theorem exists_root : ∀ {S : Type} [CommRing S] , Aic (S := S) →
    (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
    ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
      ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd]; rfl
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  have hcard : Multiset.card s = Q.natDegree := by
    rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
  have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
    rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
    congr 1
    omega
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    letI : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    have hall : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal S := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hmem := coeff_prod_mem (IsLocalRing.maximalIdeal S) s hall (Q.natDegree - i)
      (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.CompanionTheory.UnitRoot
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open Polynomial in

theorem _root_.GlobalTheory.T.absolutely_closed_unit_coefficient_root :
    ∀ {S : Type} [CommRing S], Aic (S := S) →
      (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
      ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
        ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd, Nat.sub_zero]
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    let : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    let m := IsLocalRing.maximalIdeal S
    have coeff_prod_mem (t : Multiset S) (ht : ∀ b ∈ t, b ∈ m) :
        ∀ k < t.card, ((t.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
      induction t using Multiset.induction_on with
      | empty => intro k hk; simp at hk
      | cons a t ih =>
        intro k hk
        have ha := ht a (Multiset.mem_cons_self a t)
        have ih' := ih fun b hb => ht b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
        rw [Multiset.card_cons] at hk
        cases k with
        | zero =>
          simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
          exact m.neg_mem (m.mul_mem_right _ ha)
        | succ k =>
          simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
          exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)
    have hall : ∀ b ∈ s, b ∈ m := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hcard : s.card = Q.natDegree := by
      rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
    have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
      rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
      congr 1
      omega
    have hmem := coeff_prod_mem s hall (Q.natDegree - i) (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

variable {S : Type} [CommRing S]

theorem mul_eval_eq (Q : Polynomial S) {e z w : S} (h : e * (z - w) = 0) :
    e * Q.eval z = e * Q.eval w := by
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub z w Q
  linear_combination e * hc + c * h

theorem mul_pow_eq (d : ℕ) {e z w : S} (h : e * (z - w) = 0) :
    e * z ^ d = e * w ^ d := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow z w d
  linear_combination e * hc + c * h

theorem step_of_forall_maximal (ϖ : S)
    (H : ∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) : Step ϖ := by
  intro Q n hQ hd h0
  have key := GlobalTheory.T.idempotent_local_induction (S := S)
    (fun e => ∃ z, ϖ ^ (n + 1) ∣ e * Q.eval z ∧ ϖ ^ n ∣ e * z ^ Q.natDegree) ?_ ?_ ?_ ?_
  · obtain ⟨z, h1, h2⟩ := key
    exact ⟨z, by simpa using h1, by simpa using h2⟩
  · exact ⟨0, by simp, by simp⟩
  · rintro e e' _ _ ⟨z, h1, h2⟩
    refine ⟨z, ?_, ?_⟩
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h1 e'
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h2 e'
  · rintro e e' he he' hee ⟨z1, a1, b1⟩ ⟨z2, a2, b2⟩
    have he1 : e * e = e := he
    have he2 : e' * e' = e' := he'
    have hz1 : e * (e * z1 + e' * z2 - z1) = 0 := by
      linear_combination z1 * he1 + z2 * hee
    have hz2 : e' * (e * z1 + e' * z2 - z2) = 0 := by
      linear_combination z1 * hee + z2 * he2
    refine ⟨e * z1 + e' * z2, ?_, ?_⟩
    · rw [add_mul, mul_eval_eq Q hz1, mul_eval_eq Q hz2]
      exact dvd_add a1 a2
    · rw [add_mul, mul_pow_eq _ hz1, mul_pow_eq _ hz2]
      exact dvd_add b1 b2
  · intro m hm
    have hle : compI m ≤ m := Ideal.span_le.2 (fun e he => he.2)
    have hne : compI m ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ hle))
    have : Nontrivial (S ⧸ compI m) := Ideal.Quotient.nontrivial_iff.2 hne
    have hdeg : (Q.map (Ideal.Quotient.mk (compI m))).natDegree = Q.natDegree :=
      hQ.natDegree_map _
    have h0' : (Ideal.Quotient.mk (compI m) ϖ) ^ n ∣
        (Q.map (Ideal.Quotient.mk (compI m))).eval 0 := by
      rw [Polynomial.eval_zero_map, ← map_pow]
      exact map_dvd _ h0
    obtain ⟨z', h1, h2⟩ := H m hm (Q.map (Ideal.Quotient.mk (compI m))) n
      (hQ.map _) (hdeg ▸ hd) h0'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z'
    obtain ⟨a', ha⟩ := h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', hb⟩ := h2
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hdeg] at hb
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, ← map_pow, ← map_mul] at ha
    rw [← map_pow, ← map_pow, ← map_mul] at hb
    obtain ⟨e1, i1, n1, E1⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 ha)
    obtain ⟨e2, i2, n2, E2⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 hb)
    have i1' : e1 * e1 = e1 := i1
    have i2' : e2 * e2 = e2 := i2
    refine ⟨e1 * e2, ?_, ?_, z, ⟨e1 * e2 * a, ?_⟩, ⟨e1 * e2 * b, ?_⟩⟩
    · change e1 * e2 * (e1 * e2) = e1 * e2
      linear_combination (e2 * e2) * i1' + e1 * i2'
    · intro h
      exact (hm.isPrime.mem_or_mem h).elim n1 n2
    · linear_combination e2 * E1
    · linear_combination e1 * E2

end GlobalTheory.CompanionTheory.NewtonStep
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

end Res

end GlobalTheory.CompanionTheory.ConeCech
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

theorem _root_.GlobalTheory.T.initial_object_augmented_resolution : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀), (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  first | exact @GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | exact GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | (intros; apply GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one <;> assumption)
end
