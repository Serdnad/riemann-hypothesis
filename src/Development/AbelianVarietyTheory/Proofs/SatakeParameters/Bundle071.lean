module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCards
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle063
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.LongWindow

theorem thick_inTranslate {R : Ranks} (H : Host R) (g : R.GG) (hg : Thick H g) :
    R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv g.2) := by
  unfold Thick Host.thickPlaces at hg
  obtain ⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    simpa [Finset.mem_image] using hg
  refine ⟨s, hs, ?_⟩
  have e2 : (plc g).2 = g.2 := UpperTheory.KStar.Words.placeOf_snd g
  rw [← e2, ← e]
  rfl

theorem letter_snd {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) (k : ℕ) :
    fr.iotaInv (letter τ φ (i + k)).2 = fr.iotaInv τ.2 + (((i.val + k : ℕ) : ℤ)) • fr.iotaInv φ.2 := by
  unfold letter
  rw [UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]
  rfl

open Classical in
theorem main : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 →
    WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  intro R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩
  have hO := ((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1
    (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))
  have mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) →
      ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro k hk ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩
    rw [← letter_snd]
    exact thick_inTranslate H _ ht
  have hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆
      (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem a (by omega) ha
    · exact mem b (by omega) hb
    · exact mem c hcL hc
  have h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push_cast; omega
  have := Finset.card_le_card hsub
  omega

end GlobalTheory.HTW.LongWindow
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.TraceOrigin


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ev_eq_trace_quot : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  intro k _ _ F K _ _ _ _ _ _ d x hc ev hker h a ha
  haveI : Module.IsTorsionFree (rA k x {0}) (integralClosure (rA k x {0}) K) := inferInstance
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {0}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI := hc.fin
  haveI : Module.Finite (rA k x {0}) (integralClosure (rA k x {0}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {0} (Finset.singleton_nonempty 0)).1
  haveI := GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hc 0
  haveI : IsIntegrallyClosed (integralClosure (rA k x {0}) K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  have hsurj : Function.Surjective ev := fun c => ⟨algebraMap k _ c, ev.commutes c⟩
  haveI hmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let h' : integralClosure (rA k x {0}) K := ⟨h.1, h.2⟩
  have hint : a = Algebra.intTrace (rA k x {0}) (integralClosure (rA k x {0}) K) h' := by
    apply Subtype.ext
    exact ha.trans (Algebra.algebraMap_intTrace (A := rA k x {0}) (K := F) (L := K) h').symm
  have key := GlobalTheory.trace_quotient_eq_of_projective (rA k x {0}) (integralClosure (rA k x {0}) K) (RingHom.ker ev) h'
  set p := RingHom.ker ev with hp
  let e₁ : (rA k x {0}) ⧸ p ≃+* k := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
  have he₁ : ∀ y, e₁ (Ideal.Quotient.mk p y) = ev y := fun y => rfl
  let φ : integralClosure (rA k x {0}) K ≃+* rB k K x {0} :=
    { toFun := fun b => ⟨b.1, b.2⟩, invFun := fun b => ⟨b.1, b.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJdef
  have hJ : J = (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))).map φ := by
    rw [hker, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  let e₂ := Ideal.quotientEquiv (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))) J φ hJ
  have hcomm : (algebraMap k (rB k K x {0} ⧸ J)).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap _ _) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
    change Ideal.Quotient.mk J (algebraMap k _ (ev y)) = Ideal.Quotient.mk J (φ (algebraMap _ _ y))
    rw [Ideal.Quotient.eq]
    have hmem : y - algebraMap k _ (ev y) ∈ p := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h3 : φ (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K) (y - algebraMap k _ (ev y))) ∈ J :=
      hJ ▸ Ideal.mem_map_of_mem φ (Ideal.mem_map_of_mem _ hmem)
    convert J.neg_mem h3 using 1
    rw [map_sub, map_sub, neg_sub]
    congr 1
    apply Subtype.ext
    change algebraMap k K (ev y) = algebraMap F K (algebraMap k F (ev y))
    exact IsScalarTower.algebraMap_apply k F K _
  have htr := Algebra.trace_eq_of_equiv_equiv e₁ e₂ hcomm (Ideal.Quotient.mk _ h')
  rw [key] at htr
  have h2 : e₂ (Ideal.Quotient.mk _ h') = Ideal.Quotient.mk J h := rfl
  have := congrArg e₁ htr
  rw [RingEquiv.apply_symm_apply, h2, he₁] at this
  rw [hint, this]

end GlobalTheory.PD.TraceOrigin
end
end

section

noncomputable section

namespace GlobalTheory.SatBcZero

section Weyl

open Formalism.UG GlobalTheory.SatakeWeyl

theorem weyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) (α : Fin m → ℂ)
    (h : GU σ n → ℂ) (hh : h ∈ Hecke ℂ (KU σ n)) :
    (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      ∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α := by
  have hex := fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  choose T hT using hex
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem coeff_symm : CoeffSwap ∧ CoeffNeg := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact ⟨GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets,
    GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht)⟩

end Weyl

theorem eq_of_invariant (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (hf : ∀ α : Fin m → ℂ, (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧
      ∀ i, f (Function.update α i (α i)⁻¹) = f α) (α α' : Fin m → ℂ)
    (h : Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) =
      Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹)) : f α = f α' := by
  classical
  have h2 := congrArg (Multiset.map (fun x : ℂ => s(x, x⁻¹))) h
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => s((γ i)⁻¹, γ i)) = fun i => s(γ i, (γ i)⁻¹) :=
    fun γ => funext fun i => Sym2.eq_swap
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => s(α i, (α i)⁻¹))
      = Finset.univ.val.map (fun i => s(α' i, (α' i)⁻¹)) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := GlobalTheory.exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    rcases Sym2.eq_iff.1 (hπ i) with h4 | h4
    · exact Or.inl h4.1.symm
    · exact Or.inr h4.2.symm
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf (fun i => if i ∈ s then α' i else (α ∘ π) i)).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α).1 π, ← this]

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ,
      Formalism.MainNotions.N.ubc n (Finset.univ.val.map α) = Formalism.MainNotions.N.ubc n (Finset.univ.val.map α') →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  intro K _ _ _ ϖ σ q n hU α α' e φ hφ
  unfold Formalism.MainNotions.N.ubc at e
  have e1 := add_right_cancel e
  refine eq_of_invariant _ (Formalism.UG.SatU ϖ q φ)
    (fun γ => weyl_of_coeff coeff_symm.1 coeff_symm.2 K ϖ σ q n (n / 2) hU (by omega) (by omega) γ φ hφ) _ _ ?_
  simpa only [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBcZero

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeConjLev

theorem ideleMap_mem_levT (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (T : Set (HeightOneSpectrum (𝓞 K))) (T' : Set (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ w ∈ T', w.under (𝓞 K) ∈ T) (N : ℕ) (y : Ideles K) (hy : y ∈ levT K T N) :
    ideleMap K L y ∈ levT L T' N := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · show Valued.v ((ideleMap K L y).val.2 w) = 1
    have h : Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := hy.1 _
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, h, one_pow]
  · show Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L)
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap]
    exact pow_le_pow_left₀ zero_le (hy.2 _ (hT w hw)) _

theorem under_under (F K L : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra K L] [Algebra F L]
    (h : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (h x).symm
  exact HeightOneSpectrum.ext (Ideal.under_under w.asIdeal)

theorem ideleConj_mem_levT (E : Type) [Field E] [NumberField E] [IsCMField E]
    (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E) (hu : u ∈ levT E T N) :
    ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N :=
  @ideleMap_mem_levT E E _ _ _ _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra T
    {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
    (fun w hw => hw _ (@under_under (maximalRealSubfield E) E E _ _ _ _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra _
      (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x) w)) N u hu

end GlobalTheory.HeckeConjLev
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
end
end

section

namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertNotType

theorem main : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  intro D l k h heq
  subst heq
  have h1 := D.ntypes.g_cond k
  have hdvd : 4 * D.host.d ∣ D.host.QS * D.host.q * D.host.d :=
    Nat.mul_dvd_mul_right (((by decide : 4 ∣ 16).trans D.host.sixteen_dvd_QS).mul_right _) _
  have hd1 : D.host.g k % (4 * D.host.d) = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) hdvd, h1]
    exact Nat.mod_eq_of_lt (by have := D.host.hyp.2.1.two_le; omega)
  have h21 : D.host.g k % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) (⟨2 * D.host.d, by ring⟩ : 2 ∣ 4 * D.host.d), hd1]
  have hodd : Odd (D.host.g k) := Nat.odd_iff.2 h21
  have hJ : jacobiSym (-(D.host.d : ℤ)) (D.host.g k) = 1 := by
    rw [jacobiSym.mod_right _ hodd]
    have : (-(D.host.d : ℤ)).natAbs = D.host.d := by simp
    rw [this, hd1, jacobiSym.one_right]
  unfold TwistedPlaces.InertK Host.cls primeClass at h
  split_ifs at h <;> simp_all

end GlobalTheory.InertNotType
end

section

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.continuous_iotaOQ' : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  first | exact @GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | exact GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | (intros; apply GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data <;> assumption)
end
