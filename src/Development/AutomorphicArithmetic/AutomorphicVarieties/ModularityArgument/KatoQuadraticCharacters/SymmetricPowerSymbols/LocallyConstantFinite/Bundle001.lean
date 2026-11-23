module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.lcFin :
    UpperTheory.V.Z.Kato.Sym.PE.LcFin := by
  classical
  intro F E A _ _ _ _ U hU η hη
  have hS : ∀ g : U, IsOpen {x : Gal(E/F) | x ∈ U ∧ η x = η g} := by
    intro g
    have := hU.isOpenMap_subtype_val _ (hη.isOpen_fiber (η g))
    convert this using 1
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      exact ⟨⟨x, hx⟩, hxg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have hN : ∀ g : U, ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      (L.fixingSubgroup : Set Gal(E/F)) ⊆
        {y | (g : Gal(E/F)) * y ∈ U ∧ η ((g : Gal(E/F)) * y) = η g} := by
    intro g
    rw [← krullTopology_mem_nhds_one_iff]
    refine IsOpen.mem_nhds ((hS g).preimage (continuous_const.mul continuous_id)) ?_
    simp [g.2]
  choose L hLfd hLsub using hN
  have hfg : ∀ g : U, ∃ s : Finset E,
      Submodule.span F (s : Set E) = Subalgebra.toSubmodule (L g).toSubalgebra := by
    intro g
    haveI := hLfd g
    exact (Submodule.fg_iff_finiteDimensional _).2 (inferInstanceAs (FiniteDimensional F (L g)))
  choose s hs using hfg
  have hcpt : IsCompact (U : Set Gal(E/F)) := (Subgroup.isClosed_of_isOpen U hU).isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun g : U => {x : Gal(E/F) | (g : Gal(E/F))⁻¹ * x ∈ (L g).fixingSubgroup})
    (fun g => by
      haveI := hLfd g
      exact (IntermediateField.fixingSubgroup_isOpen (L g)).preimage
        (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [one_mem]⟩)
  refine ⟨t.biUnion s, ?_⟩
  intro h hh h' hh' hag
  obtain ⟨g, hgt, hg⟩ := Set.mem_iUnion₂.1 (ht hh)
  have hg0 : (g : Gal(E/F))⁻¹ * h ∈ (L g).fixingSubgroup := hg
  have hsame : ∀ x ∈ L g, h x = h' x := by
    intro x hx
    have hx' : x ∈ Submodule.span F (s g : Set E) := by
      rw [hs g]
      exact hx
    exact LinearMap.eqOn_span' (f := h.toLinearMap) (g := h'.toLinearMap)
      (fun b hb => hag b (Finset.mem_biUnion.2 ⟨g, hgt, hb⟩)) hx'
  have hg' : (g : Gal(E/F))⁻¹ * h' ∈ (L g).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg0 ⊢
    intro x hx
    rw [AlgEquiv.mul_apply, ← hsame x hx, ← AlgEquiv.mul_apply]
    exact hg0 x hx
  have e1 := (hLsub g hg0).2
  have e2 := (hLsub g hg').2
  simp only [mul_inv_cancel_left] at e1 e2
  rw [e1, e2]
end

section

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.integ :
    UpperTheory.V.Z.Kato.Sym.PE.Integ := by
  intro Ω _ _ _ ε X m hm u z hu hz
  have key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w) := by
    intro w hw
    let φ : Polynomial Ω →+* X.K := (aeval X.jK).toRingHom
    have hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      have hov : X.OverY V := ⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩
      exact (V.valuation_le_one_iff w).1 (hw.2 V hov).le
    obtain ⟨p, hp, hpw⟩ := hmem
    have hle : Subring.closure (φ.range : Set X.K) ≤ φ.range := Subring.closure_le.2 subset_rfl
    have hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact RingHom.mem_range.1 (hle (p.coeff n).2)
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift (hp.map _)
    refine ⟨Q, hQm, ?_⟩
    show eval₂ ((io X).comp φ) (io X w) Q = 0
    rw [← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]
  have hu0 : io X u ≠ 0 := (_root_.map_ne_zero _).2 hu.1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact hu0 hz.symm
  have hinv : IsU X u⁻¹ := ⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩
  refine ⟨hz0, ?_, ?_⟩
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [hz]
    exact key u hu
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [inv_pow, hz, ← map_inv₀]
    exact key _ hinv
end

section

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.alg :
    UpperTheory.V.Z.Kato.Sym.PE.Alg := by
  intro Ω _ _ _ ε X
  have hinj : Function.Injective (pj X) :=
    (io X).injective.comp (transcendental_iff_injective.1 (jK_transcendental X))
  let φ : RatFunc Ω →+* Kb X := IsFractionRing.lift hinj
  have hφ : ∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p := fun p => IsFractionRing.lift_algebraMap hinj p
  refine ⟨φ, hφ, ?_⟩
  have hinj0 : Function.Injective (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := transcendental_iff_injective.1 (jK_transcendental X)
  let ψ : RatFunc Ω →+* X.K := IsFractionRing.lift hinj0
  have hψ : ∀ p : Polynomial Ω, ψ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = aeval X.jK p := fun p => IsFractionRing.lift_algebraMap hinj0 p
  letI : Algebra (RatFunc Ω) X.K := ψ.toAlgebra
  have hc : φ = algebraMap (RatFunc Ω) (Kb X) := RingHom.ext fun z => by
    change φ z = io X (ψ z)
    rw [← RatFunc.num_div_denom z, map_div₀, map_div₀, map_div₀, hφ, hφ, hψ, hψ]
    rfl
  have hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, y ∈ ψ.fieldRange := fun y hy => by
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff Ω y).1 hy
    exact ⟨algebraMap _ _ r / algebraMap _ _ s, by rw [map_div₀, hψ, hψ]⟩
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun f => by
    obtain ⟨p, hp, he⟩ := X.alg_j f
    have hl : p.map (algebraMap _ X.K) ∈ lifts ψ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact hle _ (p.coeff n).2
    obtain ⟨q, hq⟩ := (mem_lifts _).1 hl
    refine ⟨q, ?_, ?_⟩
    · rintro rfl
      rw [Polynomial.map_zero] at hq
      exact hp ((Polynomial.map_eq_zero _).1 hq.symm)
    · change eval₂ ψ f q = 0
      rw [← eval_map, hq, eval_map]
      exact he⟩
  have hA := Algebra.IsAlgebraic.trans (RatFunc Ω) X.K (Kb X)
  refine @Algebra.IsAlgebraic.mk _ _ _ _ φ.toAlgebra fun z => ?_
  obtain ⟨p, hp, he⟩ := hA.isAlgebraic z
  refine ⟨p, hp, ?_⟩
  change eval₂ φ z p = 0
  rw [hc]
  exact he
end
