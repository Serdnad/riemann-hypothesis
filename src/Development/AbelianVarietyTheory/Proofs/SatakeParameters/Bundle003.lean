module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Algebra.Hom.Rat
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem mem_etaleTopology_of_pullback_finite : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  intro Z X f _ _ T hT hE
  let U : X.Opens := ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : IsEmpty (pullback f U.ι : Scheme.{0}) := by
    refine ⟨fun p => ?_⟩
    have h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p := by
      rw [pullback.condition]
    have h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
      have hr := U.range_ι
      exact (Set.ext_iff.1 hr _).1 ⟨_, rfl⟩
    rw [h1, Scheme.Hom.comp_base, TopCat.comp_app] at h2
    exact h2 ⟨_, rfl⟩
  have hTU : T U.ι := hE U.ι hU
  let V : Bool → Scheme.{0} := fun b => Bool.rec U.toScheme Z b
  let j : ∀ b, V b ⟶ X := fun b => match b with
    | true => f
    | false => U.ι
  have hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : x ∈ Set.range f.base
      · obtain ⟨z, rfl⟩ := hx
        exact ⟨true, z, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · cases b
      · change Etale U.ι
        infer_instance
      · change Etale f
        infer_instance
  refine Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_
  rintro W g ⟨Y, h, k, ⟨b⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine Scheme.etaleTopology.pullback_stable h ?_
  cases b
  · change T.pullback U.ι ∈ _
    rw [Sieve.pullback_eq_top_of_mem _ hTU]
    exact Scheme.etaleTopology.top_mem _
  · exact hT

end GlobalTheory.EtC.Tr
end

section

namespace GlobalTheory

theorem continuous_char_units_complex : ∀ ψ : ℂˣ →* ℂˣ, Continuous ψ → ∃ (s : ℂ) (n : ℤ), ∀ z : ℂˣ,
    (ψ z : ℂ) = Complex.exp (s * Real.log ‖(z : ℂ)‖) * ((z : ℂ) / ‖(z : ℂ)‖) ^ n := by
  intro ψ hψ
  let E : ℂ → ℂˣ := fun w => Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)
  have hE : Continuous E := by
    refine Units.continuous_iff.2 ⟨Complex.continuous_exp, ?_⟩
    have : (fun w => ((E w)⁻¹ : ℂˣ).val) = fun w => (Complex.exp w)⁻¹ := by
      funext w; simp [E]
    rw [this]
    exact Complex.continuous_exp.inv₀ Complex.exp_ne_zero
  have hEadd : ∀ x y, E (x + y) = E x * E y := fun x y => Units.ext (Complex.exp_add x y)
  have hE0 : E 0 = 1 := Units.ext Complex.exp_zero
  let f : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun w => ⟨(ψ (E w) : ℂ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp hE)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, hE0]))
  have hF' : ∀ w, Complex.exp (F w) = (ψ (E w) : ℂ) := fun w => congrArg Subtype.val (congrFun hF w)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', hEadd, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  let L : ℂ →L[ℝ] ℂ := (AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous
  have hL : ∀ w, (ψ (E w) : ℂ) = Complex.exp (L w) := fun w => (hF' w).symm

  have hper : Complex.exp (L (2 * Real.pi * Complex.I)) = 1 := by
    rw [← hL]
    have : E (2 * Real.pi * Complex.I) = 1 := Units.ext Complex.exp_two_pi_mul_I
    rw [this, map_one, Units.val_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hper
  have hLI : L Complex.I = n * Complex.I := by
    have e : L (2 * Real.pi * Complex.I) = (2 * Real.pi : ℝ) • L Complex.I := by
      rw [← map_smul, Complex.real_smul]; push_cast; ring_nf
    rw [e, Complex.real_smul] at hn
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    push_cast at hn
    have : (2 * Real.pi : ℂ) * L Complex.I = (2 * Real.pi : ℂ) * (n * Complex.I) := by rw [hn]; ring
    exact mul_left_cancel₀ hpi this
  refine ⟨L 1, n, fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hnz : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hEz : E (Complex.log z) = z := Units.ext (Complex.exp_log hz)
  have hlog : Complex.log z = (Real.log ‖(z : ℂ)‖ : ℝ) • (1 : ℂ) + (Complex.arg z : ℝ) • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; rfl
  have hunit : (z : ℂ) / ‖(z : ℂ)‖ = Complex.exp (Complex.arg z * Complex.I) := by
    rw [div_eq_iff hnz, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
  rw [← hEz, hL, hEz, hunit, ← Complex.exp_int_mul, ← Complex.exp_add, hlog, map_add (f := _), map_smul, map_smul,
    hLI, Complex.real_smul, Complex.real_smul]
  congr 1
  ring

end GlobalTheory
end

section

namespace GlobalTheory.NormSumLt

universe u_1

theorem norm_sum_lt {K : Type u_1} [NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K)
    {r : ℝ} (hr : (0 : ℝ) < r) (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < r := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i ∈ s, f i‖ < r := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K) {r : ℝ}, (0 : ℝ) < r → (∀ i ∈ s, ‖f i‖ < r) → ‖∑ i ∈ s, f i‖ < r :=
  by
  intro K _ _ s f r hr h
  exact norm_sum_lt s f hr h

end GlobalTheory.NormSumLt
end

section

namespace GlobalTheory

open IntermediateField

theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
end

section

namespace GlobalTheory

theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

end GlobalTheory
end

section

namespace GlobalTheory

theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
end

section

namespace GlobalTheory.BijectiveIntertwining

theorem bijective_of_intertwining {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (h : Representation.IsIrreducible ρ) (h' : Representation.IsIrreducible ρ')
    (F : V →ₗ[ℂ] V') (hF : ∀ (g : G) (v : V), F (ρ g v) = ρ' g (F v)) (h0 : F ≠ 0) :
    Function.Bijective F := by
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker F
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hF, hv, map_zero] }
  let R : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range F
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, rfl⟩
        exact ⟨ρ g v, hF g v⟩ }
  constructor
  · rcases h.eq_bot_or_eq_top K with hK | hK
    · rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hK
    · exact absurd (LinearMap.ker_eq_top.mp (congrArg Subrepresentation.toSubmodule hK)) h0
  · rcases h'.eq_bot_or_eq_top R with hR | hR
    · exact absurd (LinearMap.range_eq_bot.mp (congrArg Subrepresentation.toSubmodule hR)) h0
    · rw [← LinearMap.range_eq_top]
      exact congrArg Subrepresentation.toSubmodule hR

end GlobalTheory.BijectiveIntertwining
end

section

namespace GlobalTheory.ClosedSubgroupCriterion

theorem main : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by
  intro n j a ha h01 hj i
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      have := ha hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 k with h | h
      · rw [h, hi] at this; norm_num at this
      · exact h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hj] at this
    omega
  · intro hi
    rcases h01 i with h | h
    · exfalso
      have hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        have := ha hle
        rw [h, hk] at this; norm_num at this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio, hj] at this
      omega
    · exact h

end GlobalTheory.ClosedSubgroupCriterion
end

section

open Polynomial

namespace GlobalTheory.AlgClosedResidueField

theorem isAlgClosed_residueField {K : Type} [Field K] (O : ValuationSubring K) [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue O) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hqp, hdeg, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : (q.map (algebraMap O K)).degree ≠ 0 := by
    rw [hq.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hx' : q.eval₂ (algebraMap O K) x = 0 := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
  have hint : IsIntegral O x := ⟨q, hq, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    rw [Polynomial.eval₂_at_apply] at hx'
    exact (IsFractionRing.injective O K) (by rw [hx', map_zero])
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end GlobalTheory.AlgClosedResidueField
end

section

namespace GlobalTheory

open Matrix

theorem bilinForm_injective_exists_mul_mem_range (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La)
    (hEF : Function.Injective EF) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ La
  let b : Module.Basis ι ℤ La := Module.Free.chooseBasis ℤ La
  let A : Matrix ι ι ℤ := fun i j => EF (b i) (b j)

  have key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j := by
    intro c j

    simp [map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0
    have hx : EF (∑ i, v i • b i) = 0 := by
      refine b.ext fun j => ?_
      rw [key, hvA]; simp
    have : (∑ i, v i • b i) = 0 := hEF (by rw [hx, map_zero])
    apply hv
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v this i
  set d := A.det
  refine ⟨d.natAbs * d.natAbs, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.2 hdet
    positivity
  · intro f
    let w : ι → ℤ := fun j => f (b j)
    refine ⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩
    refine b.ext fun j => ?_
    rw [key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    have hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' d
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]
    rw [← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]
    ring

end GlobalTheory
end
