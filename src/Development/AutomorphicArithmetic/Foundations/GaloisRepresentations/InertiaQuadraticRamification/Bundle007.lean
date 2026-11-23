module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle434
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ExistsCompletionEquivOfHe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle116
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_notMem_sq {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) (w : HeightOneSpectrum (𝓞 K)) : (p : 𝓞 K) ∉ w.asIdeal ^ 2 := by
  intro h
  have hv : (p : 𝓞 K) ∈ w.asIdeal := Ideal.pow_le_self two_ne_zero h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem unrLarge : UnrLarge := by
  intro K _ _
  refine ⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩
  have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp hd
  have h2 : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  exact absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.sqrtFix :
    SqrtFix := by
  intro F Ω _ _ _ _ A x a hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsq : ∀ g : G F Ω, g x = x ∨ g x = -x := by
    intro g
    have hgx : (g x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have h0 : (g x - x) * (g x + x) = 0 := by linear_combination hgx
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k => by
    exact_mod_cast A.valuation_le_one (k : A)
  refine ⟨?_, ?_⟩
  · intro t _ hvt hdiv g hg
    rcases hsq g with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hdiv
      have hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω) := by
        have hc := congrArg (fun z : ℤ => (z : Ω)) hk
        push_cast at hc
        linear_combination hc
      set y : Ω := (x - 1) / 2 with hy
      set y' : Ω := (-x - 1) / 2 with hy'
      have hgy : g y = y' := by
        rw [hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]
      have hsum : y + y' = -1 := by
        rw [hy, hy']
        ring
      have hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω) := by
        rw [hy, hy']
        push_cast
        linear_combination (-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'
      have hvp : A.valuation (y * y') < 1 := by
        rw [hprod, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt
      have hvs : A.valuation (y + y') = 1 := by
        rw [hsum, Valuation.map_neg, Valuation.map_one]
      have hiff := valuation_apply_lt_one_iff hg y
      rw [hgy] at hiff
      by_cases hyl : A.valuation y < 1
      · have hs := Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)
        rw [hvs] at hs
        exact lt_irrefl _ hs
      · have hyl' : ¬ A.valuation y' < 1 := fun h' => hyl (hiff.1 h')
        push_neg at hyl hyl'
        have hge : 1 ≤ A.valuation (y * y') := by
          rw [map_mul]
          exact one_le_mul hyl hyl'
        exact absurd hvp (not_lt.2 hge)
  · intro h2a τ hτ
    obtain ⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧
        ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1 := hτ
    rcases hsq τ with h | h
    · exact h
    · exfalso
      have hv2 : A.valuation (2 : Ω) ≤ 1 := by simpa using hint 2
      have hva : A.valuation (a : Ω) ≤ 1 := hint a
      have e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1 := by
        rw [← map_mul]
        push_cast at h2a
        exact h2a
      have hv2' : A.valuation (2 : Ω) = 1 :=
        le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)
      have hva' : A.valuation (a : Ω) = 1 :=
        le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)
      have hvx2 : A.valuation x ^ 2 = 1 := by
        rw [← Valuation.map_pow, hx, hva']
      have hvx : A.valuation x = 1 := by
        rcases lt_trichotomy (A.valuation x) 1 with hl | he | hg
        · exact absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))
        · exact he
        · exact absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))
      have key := hI x hvx.le
      rw [h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul] at key
      exact lt_irrefl _ key
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem isOpen_fixGrp (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra K Ω] [Algebra F K]
    [IsScalarTower F K Ω] [FiniteDimensional F K] : IsOpen (fixGrp F Ω K : Set (G F Ω)) := by
  let φ := IsScalarTower.toAlgHom F K Ω
  haveI : FiniteDimensional F φ.fieldRange := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  refine Subgroup.isOpen_mono (fun g hg x => ?_) φ.fieldRange.fixingSubgroup_isOpen
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem isAlgClosure_plus : IsAlgClosure (maximalRealSubfield E) Ω :=
  ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

theorem cuts_base : Cuts (Fld.base E Ω) ⊤ := fun g => ⟨fun _ => trivial, fun _ x => g.commutes x⟩

end

theorem noSelfTwist_of (h : NormRam) : NoSelfTwist :=
  fun K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp A v hA hτ a ha π B hB η hη =>
    GlobalTheory.TwistRamified.twist_ne K a ha π η v B hB (h K M Ω hp η hη A v hA hτ)

theorem quadraticCharTwist_of_exists_of_infinity (h1 : Quad0Ex) (h2 : InfOf) : Quad0 := by
  intro E Ω _ _ _ _ _ _ T hT
  refine h2 E Ω _ fun S hS => ?_
  obtain ⟨Q, ⟨δ, hδ, h3⟩, h4, u, hu, h5⟩ := h1 E Ω (T ∪ S) (hT.union hS)
  exact ⟨Q, ⟨⟨δ, hδ, fun t ht => h3 t (Or.inl ht)⟩, fun t ht => h4 t (Or.inl ht), u, fun h => hu (Or.inl h), h5⟩,
    u, fun h => hu (Or.inr h), h5⟩

theorem splitIso_holds : SplitIso := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ A v w hv hw h
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
  obtain ⟨i, h1, -, h2, h3⟩ := PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift.exists_completionEquiv_of_he hv hw (fun σ => h _ (GlobalTheory.WeilDeligne.Weil_le_Dec hv σ.2))
    (GlobalTheory.InertFixVal.ramificationIdx_eq_one A v w hv hw fun σ hσ => h σ (Ine_le_Dec A hσ)).2
  exact ⟨i, h1, h2, h3⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.infOf :
    InfOf := by
  intro F Ω _ _ _ _ _ P hP hfin
  have hopen : ∀ Q : QCM F Ω, IsOpen ((Q.K.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro Q
    haveI : FiniteDimensional F ↥Q.K :=
      Module.finite_of_finrank_pos (by rw [Q.two]; exact two_pos)
    exact IntermediateField.fixingSubgroup_isOpen Q.K
  have hS : (⋃ Q ∈ {Q | P Q}, {u : HeightOneSpectrum (𝓞 F) | ∃ A : ValuationSubring Ω,
      IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ Q.K.fixingSubgroup}).Finite :=
    Set.Finite.biUnion hfin fun Q _ => GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F Q.K.fixingSubgroup (hopen Q)
  obtain ⟨Q, hQ, u, hu, A, hA, τ, hτ, hfix⟩ := hP _ hS
  refine hu (Set.mem_biUnion (show Q ∈ {Q | P Q} from hQ) ⟨A, hA, fun hle => hfix ?_⟩)
  intro x
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hτ) _ x.2
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_prime_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∀ n : ℕ, n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ A.valuation (r : Ω) < 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hv
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hv
    have hp := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    by_cases h : A.valuation ((n.minFac : ℕ) : Ω) < 1
    · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
    · have h1 : A.valuation ((n.minFac : ℕ) : Ω) = 1 :=
        le_antisymm (ReciprocityTheory.Gal.valuation_natCast_le_one A _) (not_lt.1 h)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hp.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        nlinarith [hm]
      have hvm : A.valuation (m : Ω) < 1 := by
        have e : A.valuation ((n : ℕ) : Ω) = A.valuation ((n.minFac : ℕ) : Ω) * A.valuation (m : Ω) := by
          rw [← map_mul, ← Nat.cast_mul, ← hm]
        rwa [e, h1, one_mul] at hv
      obtain ⟨r, hr, hrm, hrv⟩ := ih m hlt hm0 hvm
      exact ⟨r, hr, hrm.trans ⟨n.minFac, by rw [mul_comm]; exact hm⟩, hrv⟩

private theorem normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  haveI : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
  exact Nat.card_pos

private theorem normV_mem {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  simpa [normV, nsmul_eq_mul] using card_nsmul_eq_zero' (G := 𝓞 F ⧸ t.asIdeal) (x := 1)

private theorem exists_place_of_prime {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal := by
  have hne : Ideal.span {((q : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at h2
    exact (Nat.prime_iff_prime_int.1 hq).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hq0 : ((q : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hmem := hle (Ideal.mem_span_singleton_self ((q : ℕ) : 𝓞 K))
  exact ⟨⟨M, hM.isPrime, fun h => hq0 (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

private theorem exists_moves {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {q : ℕ} (hq : q.Prime) (h2 : 2 < q) (hB : ∀ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2)
    {x : Ω} (hx : x ^ 2 = ((q : ℕ) : Ω)) :
    ∃ (u : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal ∧ IsPlaceOver A u ∧
      ∃ σ ∈ Ine (F := K) A, σ x = -x := by
  obtain ⟨u, hu⟩ := exists_place_of_prime (K := K) hq
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨σ, hσ, h⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj K Ω A u hA q hu (hB u) 2 two_pos
    (fun hd => by have := Nat.le_of_dvd two_pos hd; omega) x (-1) hx (by norm_num)
  exact ⟨u, A, hu, hA, σ, hσ, by rw [h]; ring⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.quad0Ex :
    SqrtFix → MkQ → UnrLarge → Quad0Ex := by
  intro hS hM hU E Ω _ _ _ _ _ _ T hT
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  obtain ⟨E', hfin, hE'⟩ : ∃ E' : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧
      ∀ (j : E →+* Ω) (y : E), j y ∈ E' :=
    ⟨IntermediateField.normalClosure ℚ E Ω, inferInstance,
      fun j y => AlgHom.fieldRange_le_normalClosure j.toRatAlgHom ⟨y, rfl⟩⟩
  haveI : NumberField E' := { }
  haveI : IsAlgClosure E' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  obtain ⟨B1, hB1⟩ := hU E
  obtain ⟨B2, hB2⟩ := hU E'
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ∏ t ∈ hT.toFinset, normV t := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Finset.prod_pos fun t _ => normV_pos' t
  have hcd : ∀ t ∈ T, normV t ∣ c := fun t ht => hc ▸ Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)
  obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 8 * c) (max (max B1 B2) (max c 2)) (by omega)
  simp only [max_lt_iff] at hgt
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hgt
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : Ω) two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((q : ℕ) : Ω) = 0 := by rw [← hx]; simp
    exact hq.ne_zero (Nat.cast_eq_zero.1 this)
  have hneg : -x ≠ x := fun h => hx0 (by
    have : (2 : Ω) * x = 0 := by linear_combination -h
    simpa using this)
  obtain ⟨u', A', _, _, σ', hσ', hσ'x⟩ := exists_moves (K := E') hq h4 (hB2 q hq h2) hx
  obtain ⟨u, A, huq, hA, τ, hτ, hτx⟩ := exists_moves (K := E) hq h4 (hB1 q hq h1) hx
  have hxZ : x ^ 2 = (((q : ℕ) : ℤ) : Ω) := by rw [hx]; simp
  obtain ⟨Q, hxQ, hspan, hfix⟩ := hM E Ω x (q : ℤ) hxZ ⟨τ, by rw [hτx]; exact hneg⟩
  have hfixT : ∀ (F : Type) [Field F] [NumberField F] [Algebra F Ω], ∀ t ∈ T, ∀ A : ValuationSubring Ω,
      IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, g x = x := by
    intro F _ _ _ t ht A hA g hg
    have hv : A.valuation ((normV t : ℕ) : Ω) < 1 := by
      have := (hA _).2 (normV_mem t)
      simpa using this
    obtain ⟨r, hr, hrd, hrv⟩ := exists_prime_val A _ (normV_pos' t).ne' hv
    refine (hS F Ω A x q hxZ).1 r hr hrv ?_ g hg
    have h8 : 8 * r ∣ 8 * c := Nat.mul_dvd_mul_left 8 (hrd.trans (hcd t ht))
    exact (Int.natCast_dvd_natCast.2 h8).trans (Nat.modEq_iff_dvd.1 hmod.symm)
  have hs1 : ∀ (j : E →+* Ω) (y : E), σ'.toRingEquiv (j y) = j y := fun j y => by
    simpa using σ'.commutes (⟨j y, hE' j y⟩ : E')
  have huT : u ∉ T := by
    intro ht
    have hle : normV u ≤ c := Nat.le_of_dvd hc0 (hcd u ht)
    have hcop : Nat.Coprime q (normV u) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => by
        have := Nat.le_of_dvd (normV_pos' u) hd
        omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((normV u : ℕ) : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hmem : (1 : 𝓞 E) ∈ u.asIdeal := by
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ huq) (Ideal.mul_mem_left _ _ (normV_mem u))
    exact (Ideal.ne_top_iff_one _).1 u.isPrime.ne_top hmem
  refine ⟨Q, ⟨⟨x, hxQ⟩, ⟨⟨q, hq.pos, ?_⟩, hspan, σ'.toRingEquiv, hs1, hσ'x⟩, ?_⟩, ?_, u, huT, A, hA, τ, hτ, ?_⟩
  · apply Subtype.ext
    simpa using hx
  · intro t ht A hA g hg
    exact hfixT _ t ht A hA g hg
  · intro t ht A hA g hg
    exact hfix E g (fun y => g.commutes y) (hfixT E t ht A hA g hg)
  · intro hf
    have := hf ⟨x, hxQ⟩
    exact hneg (hτx.symm.trans this)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open Polynomial
open scoped IntermediateField

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

private theorem sq_parts (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) :
    z.re ^ 2 - z.im ^ 2 = a ∧ z.re * z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

private theorem conj_of_sq_nonneg (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : 0 ≤ a) :
    z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have him : z.im = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    · exact h3
  exact (Complex.conj_eq_iff_im.mpr him).symm

private theorem conj_of_sq_nonpos (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : a ≤ 0) :
    -z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.mkQ :
    MkQ := by
  intro Y Ω _ _ _ _ _ _ x a hx ⟨g, hg⟩
  have hxa : x ^ 2 = algebraMap Y Ω (a : Y) := by rw [hx, map_intCast]
  have heval : aeval x (X ^ 2 - C (a : Y) : Y[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hxa, sub_self]
  have hint : IsIntegral Y x := ⟨X ^ 2 - C (a : Y), monic_X_pow_sub_C _ two_ne_zero, heval⟩
  have hirr : Irreducible (X ^ 2 - C (a : Y) : Y[X]) := by
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hg ?_)
    have h2 : x ^ 2 = (algebraMap Y Ω b) ^ 2 := by rw [hxa, ← map_pow, hb]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · rw [h]; exact g.commutes b
    · rw [h, map_neg]; congr 1; exact g.commutes b
  have hmin : minpoly Y x = X ^ 2 - C (a : Y) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C _ two_ne_zero)).symm
  have hdeg : (minpoly Y x).natDegree = 2 := by rw [hmin, natDegree_X_pow_sub_C _]
  have hfin : Module.finrank Y Y⟮x⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField Y⟮x⟯ := NumberField.of_module_finite Y _
  have hconj : x ∈ GlobalTheory.CMSub.conjStable Ω := by
    have hφ : ∀ φ : Ω →+* ℂ, (φ x) ^ 2 = (a : ℂ) := fun φ => by rw [← map_pow, hx, map_intCast]
    rcases le_total 0 a with ha | ha
    · exact ⟨x, fun φ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonneg _ a (hφ φ) ha⟩
    · exact ⟨-x, fun φ => by rw [map_neg]; exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonpos _ a (hφ φ) ha⟩
  have hle : Y⟮x⟯ ≤ GlobalTheory.CMSub.conjField Y Ω := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hconj
  have cm : IsCMField Y⟮x⟯ := GlobalTheory.CMSub.isCMField_of_le _ hle
  have hxK : x ∈ Y⟮x⟯ := IntermediateField.mem_adjoin_simple_self Y x
  have hspan : ∀ y : Y⟮x⟯, ∃ b c : Y, y = algebraMap Y Y⟮x⟯ b + algebraMap Y Y⟮x⟯ c * ⟨x, hxK⟩ := by
    intro y
    obtain ⟨f, hf, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have hf' : f = C (f.coeff 1) * X + C (f.coeff 0) := Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    rw [hf', map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, IntermediateField.adjoin.powerBasis_gen, add_comm]
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, coeff_C_zero, coeff_C_succ, mul_zero, mul_one, zero_add, add_zero]
    rfl
  refine ⟨⟨Y⟮x⟯, nf, cm, hfin⟩, hxK, hspan, ?_⟩
  intro F _ _ h hY hhx y
  obtain ⟨b, c, rfl⟩ := hspan y
  have hb : ∀ e : Y, h (algebraMap Y Ω e) = algebraMap Y Ω e := hY
  show h ((algebraMap Y Ω b) + (algebraMap Y Ω c) * x) = (algebraMap Y Ω b) + (algebraMap Y Ω c) * x
  rw [map_add (f := _), map_mul, hb, hb, hhx]
end
