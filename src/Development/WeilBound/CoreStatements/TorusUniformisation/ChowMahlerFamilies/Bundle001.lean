module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

open MvPolynomial

namespace PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem contDiff_eval (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

end PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem PositivityTheory.Xgn.polynomial_norm_square_smooth : ∀ (σ : Type) [Fintype σ] (s : MvPolynomial σ ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) s)‖ ^ 2) := by
  intro σ _ s
  exact (PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ
end

section

open MvPolynomial

theorem PositivityTheory.Xgn.finite_nonvanishing_selection : ∀ (σ : Type) [Finite σ] (F : Set (MvPolynomial σ ℤ)), ∃ T : Finset (MvPolynomial σ ℤ), (T : Set (MvPolynomial σ ℤ)) ⊆ F ∧ ∀ z : σ → ℂ, (∃ s ∈ F, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0) → ∃ s ∈ T, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro σ _ F
  have hfg : (Submodule.span (MvPolynomial σ ℤ) F).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTF, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset F).1 hfg
  refine ⟨T, hTF, fun z hz => ?_⟩
  obtain ⟨s, hsF, hs⟩ := hz
  by_contra hall
  push_neg at hall
  let φ : MvPolynomial σ ℤ →+* ℂ := (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : Ideal.span (T : Set (MvPolynomial σ ℤ)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro t ht
    exact RingHom.mem_ker.2 (hall t ht)
  have hsT : s ∈ Submodule.span (MvPolynomial σ ℤ) (T : Set (MvPolynomial σ ℤ)) := by
    rw [← hT]
    exact Submodule.subset_span hsF
  exact hs (RingHom.mem_ker.1 (hle hsT))
end

section

open MvPolynomial

theorem PositivityTheory.Xgn.polynomial_eval_complex_conjugate : ∀ (σ : Type) (s : MvPolynomial σ ℤ) (z : σ → ℂ), eval (fun p => (starRingEnd ℂ) (z p)) (MvPolynomial.map (Int.castRingHom ℂ) s) = (starRingEnd ℂ) (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) := by
  intro σ s z
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end

section

open NumberField IsDedekindDomain

namespace PositivityTheory.Xgn.FixedFieldAutomorphism

open scoped Cardinal

theorem exists_equiv {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] [Algebra R K] [Algebra R L] [FaithfulSMul R K]
    [FaithfulSMul R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ g : K ≃+* L, ∀ r, g (algebraMap R K r) = algebraMap R L r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR
    (hKL ▸ hK)
  have h3 : #s = #t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : t → L))) L]
  congr 1
  exact e'.commutes r

theorem exists_aut {R : Type} [CommRing R] [IsDomain R] (hR : #R ≤ ℵ₀) (i j : R →+* ℂ)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ g : ℂ ≃+* ℂ, ∀ r, g (i r) = j r := by
  have hC : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  exact @exists_equiv R ℂ ℂ _ _ _ _ _ _ i.toAlgebra j.toAlgebra
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ i.toAlgebra).2 hi)
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ j.toAlgebra).2 hj) hR hC rfl

end PositivityTheory.Xgn.FixedFieldAutomorphism

theorem PositivityTheory.Xgn.mem_of_fixed_by_automorphisms : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  have hFc : Cardinal.mk F ≤ Cardinal.aleph0 := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
    simpa using this
  by_cases hc : IsAlgebraic F c
  · have hint : IsIntegral F c := hc.isIntegral
    haveI : FiniteDimensional F (IntermediateField.adjoin F {c}) :=
      IntermediateField.adjoin.finiteDimensional hint
    set_option synthInstance.maxHeartbeats 200000 in
    have hE : Cardinal.mk (IntermediateField.adjoin F {c}) ≤ Cardinal.aleph0 := by
      refine (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le hFc le_rfl)
    have key : ∀ φ : IntermediateField.adjoin F {c} →ₐ[F] ℂ,
        φ = (IntermediateField.adjoin F {c}).val := by
      intro φ
      obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hE
        (IntermediateField.adjoin F {c}).val.toRingHom φ.toRingHom
        (RingHom.injective _) (RingHom.injective _)
      have h1 : g c = c := h g fun a ha => by
        have := hg (algebraMap F _ ⟨a, ha⟩)
        simpa using this
      have h2 := hg (IntermediateField.AdjoinSimple.gen F c)
      refine (IntermediateField.adjoin.powerBasis hint).algHom_ext ?_
      rw [IntermediateField.adjoin.powerBasis_gen]
      exact h2.symm.trans h1
    have hcard := AlgHom.card F (IntermediateField.adjoin F {c}) ℂ
    have h1 : Module.finrank F (IntermediateField.adjoin F {c}) = 1 := by
      rw [← hcard, Fintype.card_eq_one_iff]
      exact ⟨_, key⟩
    have h2 : c ∈ (⊥ : IntermediateField F ℂ) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 h2
    exact a.2
  · exfalso
    have hc' : ¬ IsAlgebraic F (c + 1) := fun h' => hc (by
      have := h'.isIntegral.sub (isIntegral_one (R := F))
      simpa using this.isAlgebraic)
    have hP : Cardinal.mk (Polynomial F) ≤ Cardinal.aleph0 :=
      Polynomial.cardinalMk_le_max.trans (max_le hFc le_rfl)
    obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hP
      (Polynomial.aeval (R := F) c).toRingHom (Polynomial.aeval (R := F) (c + 1)).toRingHom
      (transcendental_iff_injective.1 hc) (transcendental_iff_injective.1 hc')
    have h1 : g c = c := h g fun a ha => by
      have := hg (Polynomial.C ⟨a, ha⟩)
      simpa using this
    have h2 := hg Polynomial.X
    simp [h1] at h2
end

section

namespace PositivityTheory.Xgn.JordanBasis

theorem exists_span_sup_range {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (π : Module.End k W) (r : ℕ)
    (h : Module.finrank k (LinearMap.ker π) ≤ r) :
    ∃ x : Fin r → W, ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u := by
  classical
  have hd : Module.finrank k (W ⧸ LinearMap.range π) ≤ r := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range π)
    have h2 := LinearMap.finrank_range_add_finrank_ker π
    omega
  obtain ⟨g, hg⟩ : ∃ g : W ⧸ LinearMap.range π → W, ∀ q, (LinearMap.range π).mkQ (g q) = q :=
    ⟨_, Function.surjInv_eq (LinearMap.range π).mkQ_surjective⟩
  let b := Module.finBasis k (W ⧸ LinearMap.range π)
  let x : Fin r → W := fun i =>
    if h : (i : ℕ) < Module.finrank k (W ⧸ LinearMap.range π) then g (b ⟨i, h⟩) else 0
  have hspan : ∀ j, g (b j) ∈ Submodule.span k (Set.range x) := by
    intro j
    apply Submodule.subset_span
    refine ⟨⟨j, lt_of_lt_of_le j.2 hd⟩, ?_⟩
    simp [x, j.2]
  refine ⟨x, fun v => ?_⟩
  refine ⟨∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j), ?_⟩
  have hq : (LinearMap.range π).mkQ
      (v - ∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j)) = 0 := by

    rw [map_sub, map_sum]
    simp only [map_smul, hg]
    rw [b.sum_repr, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hq
  exact ⟨u, by rw [hu]; abel⟩

theorem span_eq_top {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (π : Module.End k W) (e r : ℕ) (hπ : π ^ e = 0) (x : Fin r → W)
    (hx : ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u) :
    Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) = ⊤ := by
  classical
  set S := Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) with hS
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [pow_zero] at hπ
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = 0 := by simpa using LinearMap.congr_fun hπ v
    rw [hv]
    exact S.zero_mem
  have hinv : ∀ s ∈ S, π s ∈ S := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => π s ∈ S) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      by_cases hj : (j : ℕ) + 1 < e
      · apply Submodule.subset_span
        refine ⟨(i, ⟨(j : ℕ) + 1, hj⟩), ?_⟩
        simp [pow_succ', Module.End.mul_apply]
      · have hje : (j : ℕ) + 1 = e := by omega
        have h0 : π ((π ^ (j : ℕ)) (x i)) = 0 := by
          have h1 : (π ^ ((j : ℕ) + 1)) (x i) = π ((π ^ (j : ℕ)) (x i)) := by
            rw [pow_succ', Module.End.mul_apply]
          rw [← h1, hje, hπ, LinearMap.zero_apply]
        show π ((π ^ (j : ℕ)) (x i)) ∈ S
        rw [h0]
        exact S.zero_mem
    · simp
    · intro a c _ _ ha hc
      rw [map_add (f := _)]
      exact S.add_mem ha hc
    · intro c a _ ha
      rw [map_smul]
      exact S.smul_mem c ha
  have hxS : ∀ a ∈ Submodule.span k (Set.range x), a ∈ S := by
    intro a ha
    refine Submodule.span_le.2 ?_ ha
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨(i, ⟨0, he⟩), by simp⟩
  have hpow : ∀ n : ℕ, ∀ s ∈ S, (π ^ n) s ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hinv _ (ih s hs)
  have key : ∀ n : ℕ, ∀ v : W, ∃ s ∈ S, ∃ u : W, v = s + (π ^ n) u := by
    intro n
    induction n with
    | zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩
    | succ n ih =>
      intro v
      obtain ⟨s, hs, u, rfl⟩ := ih v
      obtain ⟨a, ha, u', rfl⟩ := hx u
      refine ⟨s + (π ^ n) a, S.add_mem hs (hpow n a (hxS a ha)), u', ?_⟩
      rw [map_add (f := _), pow_succ, Module.End.mul_apply, add_assoc]
  refine Submodule.eq_top_iff'.2 fun v => ?_
  obtain ⟨s, hs, u, rfl⟩ := key e v
  rw [hπ, LinearMap.zero_apply, add_zero]
  exact hs

end PositivityTheory.Xgn.JordanBasis
end

section

namespace PositivityTheory.Xgn.PrimeOfDimensionOne

open IsLocalRing

theorem dim_eq_one (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    (f : B) (hf : f ≠ 0) (hm : f ∈ maximalIdeal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → f ∈ Q) : ringKrullDim B = 1 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {f})
  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (↑hfin.toFinset : Set (Ideal B)), (id P : Set B) := by
    intro g hg
    simp only [Set.mem_iUnion, Set.Finite.coe_toFinset, id, SetLike.mem_coe, exists_prop]
    have hne : Ideal.span {g} ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal g).1 hg)
    obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hne
    have hQp := hQ.1.1
    have hgQ : g ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self g)
    by_cases hg0 : g = 0
    · obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
        (Ideal.span_singleton_ne_top ((mem_maximalIdeal f).1 hm))
      exact ⟨P, hP, hg0 ▸ P.zero_mem⟩
    have hQ0 : Q ≠ ⊥ := fun hb => hg0 (by rw [hb] at hgQ; exact (Submodule.mem_bot B).1 hgQ)
    have hfQ : Ideal.span {f} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).2 (h Q hQp hQ0)
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hfQ
    have hPp := hP.1.1
    have hP0 : P ≠ ⊥ := fun hb => hf (by
      have := hP.1.2 (Ideal.mem_span_singleton_self f)
      rw [hb] at this
      exact (Submodule.mem_bot B).1 this)
    have hQ1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) Q hQ
    have hPeq : P = Q := by
      by_contra hne'
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPQ hne')
      have h1 : 1 ≤ P.height := Order.one_le_iff_ne_zero.2 (fun h0 => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := (by gcongr : (1 : ℕ∞) + 1 ≤ P.height + 1).trans (hlt.trans hQ1)
      norm_num at h2
    exact ⟨P, hP, hPeq ▸ hgQ⟩
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).1 hP).1.1)).1 hcover
  have hPmem := (Set.Finite.mem_toFinset hfin).1 hP
  have hPp := hPmem.1.1
  have hPm : P = maximalIdeal B := le_antisymm (le_maximalIdeal hPp.ne_top) hmP
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) P hPmem
  have hge : 1 ≤ (maximalIdeal B).height := Order.one_le_iff_ne_zero.2 (fun h0 =>
    hf ((Submodule.mem_bot B).1 (Ideal.height_eq_zero_iff_eq_bot.1 h0 ▸ hm)))
  rw [le_antisymm (hPm ▸ hle) hge]
  rfl

theorem of_mem (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ≠ 0) (hm : f ∈ maximalIdeal A) :
    ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  obtain ⟨P, ⟨hPp, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance
    {P : Ideal A | P.IsPrime ∧ f ∉ P}
    ⟨⊥, Ideal.isPrime_bot, fun h => hf ((Submodule.mem_bot A).1 h)⟩
  refine ⟨P, hPp, hfP, ?_⟩
  have := hPp
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  refine dim_eq_one (A ⧸ P) (Ideal.Quotient.mk P f)
    (fun h0 => hfP (Ideal.Quotient.eq_zero_iff_mem.1 h0)) ?_ ?_
  · refine (mem_maximalIdeal _).2 fun hu => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ P)ˣ).val
    have h1 : Ideal.Quotient.mk P (f * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, map_one, sub_eq_zero]
      exact hu.mul_val_inv
    have h2 : f * y - 1 ∈ maximalIdeal A :=
      le_maximalIdeal hPp.ne_top (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 : (1 : A) ∈ maximalIdeal A := by
      simpa using sub_mem ((maximalIdeal A).mul_mem_right y hm) h2
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · intro Q hQ hQ0
    by_contra hfQ
    refine hmax (Q.comap (Ideal.Quotient.mk P)) ⟨Ideal.comap_isPrime _ _, hfQ⟩
      (lt_of_le_of_ne (fun a ha => ?_) fun hPQ => hQ0 ?_)
    · show Ideal.Quotient.mk P a ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact Q.zero_mem
    · rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hPQ,
        Ideal.map_quotient_self]

end PositivityTheory.Xgn.PrimeOfDimensionOne

theorem PositivityTheory.Xgn.exists_prime_dim_one_avoiding : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (f : A), f ≠ 0 → ¬ IsField A → ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  intro A _ _ _ _ f hf hA
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    fun h => hA (IsLocalRing.isField_iff_maximalIdeal_eq.2 h)
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hP, hfgP, hdim⟩ := PositivityTheory.Xgn.PrimeOfDimensionOne.of_mem A (f * g) (mul_ne_zero hf hg0)
    ((IsLocalRing.maximalIdeal A).mul_mem_left f hg)
  exact ⟨P, hP, fun hfP => hfgP (P.mul_mem_right g hfP), hdim⟩
end
