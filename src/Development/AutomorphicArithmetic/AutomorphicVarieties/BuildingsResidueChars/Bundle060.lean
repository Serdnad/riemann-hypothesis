module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

theorem UpperTheory.cm_inertia_restriction_holds : UpperTheory.V.Af.Cr.IneRes := by
  intro F₀ F Ω _ _ _ _ _ _ _ _ _ _
  classical
  unfold Ine IsPlaceOver Inertia
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω), IsIntegral ℤ x → A.valuation x ≤ 1 := by
    intro A x h
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h.tower_top : IsIntegral A x)
    exact A.valuation_le_one y
  obtain ⟨α₁, hα₁⟩ := Field.exists_primitive_element F₀ F
  have hα₁alg : IsAlgebraic ℤ α₁ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (.of_finite ℚ α₁)
  obtain ⟨m, hm0, hmint⟩ := hα₁alg.exists_integral_multiple
  set α : F := m • α₁ with hαdef
  set g : Polynomial ℤ := minpoly ℤ α with hgdef
  set f : Polynomial F₀ := g.map (algebraMap ℤ F₀) with hfdef
  have hgmonic : g.Monic := minpoly.monic hmint
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hfdef, Polynomial.aeval_map_algebraMap, hgdef, minpoly.aeval]
  have hfsep : f.Separable := by
    have h1 : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
    have h2 := h1.map (f := algebraMap ℚ F₀)
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hmint, Polynomial.map_map] at h2
    have h3 : (algebraMap ℚ F₀).comp (algebraMap ℤ ℚ) = algebraMap ℤ F₀ := RingHom.ext_int _ _
    rw [h3] at h2
    exact h2
  set c : F := Polynomial.aeval α (Polynomial.derivative f) with hcdef
  have hc0 : c ≠ 0 := hfsep.aeval_derivative_ne_zero hfα
  have hcint : IsIntegral ℤ c := by
    have h1 : c = Polynomial.aeval α (Polynomial.derivative g) := by
      rw [hcdef, hfdef, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    have key := Polynomial.aeval_algHom_apply (integralClosure ℤ F).val
      (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)
    rw [h1]
    refine key ▸ ?_
    exact (Polynomial.aeval (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)).2
  set d : F₀ := Algebra.norm F₀ c with hddef
  have hdint : IsIntegral ℤ d := Algebra.isIntegral_norm F₀ hcint
  have hd0 : d ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc0
  set D : 𝓞 F₀ := ⟨d, hdint⟩ with hDdef
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    exact congrArg (fun x : 𝓞 F₀ => (x : F₀)) h
  have hspan : Ideal.span {D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hD0
  refine Filter.eventually_cofinite.mpr ((Ideal.finite_factors hspan).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hDv
  apply hv
  intro A hA σ hσ
  have hσ2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
  set α₀ : Ω := algebraMap F Ω α with hα₀def
  have h0 : Polynomial.aeval α₀ f = 0 := by
    rw [hα₀def, Polynomial.aeval_algebraMap_apply, hfα, map_zero]
  have hfix : σ α₀ = α₀ := by
    by_contra hne
    set fΩ : Polynomial Ω := f.map (algebraMap F₀ Ω) with hfΩ
    have hfΩ_monic : fΩ.Monic := (hgmonic.map _).map _
    have hfΩ0 : fΩ ≠ 0 := hfΩ_monic.ne_zero
    have hroot : ∀ y : Ω, Polynomial.aeval y f = 0 → y ∈ fΩ.roots := by
      intro y hy
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, Polynomial.eval_map_algebraMap]
      exact hy
    have hα₀root : α₀ ∈ fΩ.roots := hroot _ h0
    have hβroot : σ α₀ ∈ fΩ.roots := by
      apply hroot
      have := Polynomial.aeval_algHom_apply (σ : Ω ≃ₐ[F₀] Ω).toAlgHom α₀ f
      rw [h0, map_zero] at this
      exact this
    have hrootint : ∀ y ∈ fΩ.roots, IsIntegral ℤ y := by
      intro y hy
      refine ⟨g, hgmonic, ?_⟩
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, hfdef, Polynomial.map_map,
        ← Polynomial.eval₂_eq_eval_map] at hy
      have hZ : algebraMap ℤ Ω = (algebraMap F₀ Ω).comp (algebraMap ℤ F₀) := RingHom.ext_int _ _
      rw [hZ]
      exact hy
    have hder : algebraMap F Ω c = ((fΩ.roots.erase α₀).map (α₀ - ·)).prod := by
      rw [← (IsAlgClosed.splits fΩ).eval_root_derivative hfΩ_monic hα₀root]
      rw [hfΩ, Polynomial.derivative_map, Polynomial.eval_map_algebraMap, hcdef, hα₀def,
        Polynomial.aeval_algebraMap_apply]
    have hβmem : σ α₀ ∈ fΩ.roots.erase α₀ := (Multiset.mem_erase_of_ne hne).mpr hβroot
    have hcv : A.valuation (algebraMap F Ω c) < 1 := by
      rw [hder, ← Multiset.cons_erase hβmem, Multiset.map_cons, Multiset.prod_cons, Valuation.map_mul]
      have h1 : A.valuation (α₀ - σ α₀) < 1 := by
        rw [Valuation.map_sub_swap]
        exact hσ2 α₀ (hint A α₀ (hrootint α₀ hα₀root))
      have h2 : A.valuation (((fΩ.roots.erase α₀).erase (σ α₀)).map (α₀ - ·)).prod ≤ 1 := by
        apply hint
        apply IsIntegral.multiset_prod
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
        exact (hrootint α₀ hα₀root).sub
          (hrootint y (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hy)))
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) h1
    have hnorm := Algebra.norm_eq_prod_embeddings F₀ Ω c
    set φ₀ : F →ₐ[F₀] Ω := IsScalarTower.toAlgHom F₀ F Ω with hφ₀
    rw [← Finset.mul_prod_erase Finset.univ (fun φ : F →ₐ[F₀] Ω => φ c) (Finset.mem_univ φ₀)] at hnorm
    have hdv : A.valuation (algebraMap F₀ Ω d) < 1 := by
      rw [hddef, hnorm, Valuation.map_mul]
      have h2 : A.valuation (∏ φ ∈ Finset.univ.erase φ₀, φ c) ≤ 1 := by
        apply hint
        apply IsIntegral.prod
        intro φ _
        exact hcint.map φ.toRingHom.toIntAlgHom
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hcv
    exact hDv ((hA D).mp hdv)
  have hfix1 : σ (algebraMap F Ω α₁) = algebraMap F Ω α₁ := by
    have h : σ (algebraMap F Ω α) = algebraMap F Ω α := hfix
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    simp only [hαdef, zsmul_eq_mul, map_mul, map_intCast] at h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hm0) h
  have hφ : ((σ : Ω ≃ₐ[F₀] Ω).toAlgHom).comp (IsScalarTower.toAlgHom F₀ F Ω) =
      IsScalarTower.toAlgHom F₀ F Ω := by
    have hadj : Algebra.adjoin F₀ {α₁} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α₁), hα₁, IntermediateField.top_toSubalgebra]
    refine AlgHom.ext_of_adjoin_eq_top hadj ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hfix1
  have hcomm : ∀ y : F, σ (algebraMap F Ω y) = algebraMap F Ω y := fun y => DFunLike.congr_fun hφ y
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[F₀] Ω).toRingEquiv) hcomm, ?_⟩
  ext x
  rfl
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem UpperTheory.V.Af.Cr.semisimple_restriction_normal {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K Γ V) (N : Subgroup Γ) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  have hmul : ∀ (a b : Γ) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; rw [map_mul]; rfl
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hCs, hC⟩ := hss (⨅ g : Γ, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases hC0 : C = ⊥
  · have hU := hC.sup_eq_top
    rw [hC0, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hCs g v hv, hC0, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : Γ, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  have : s ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => key g s hs
  exact this

theorem UpperTheory.semisimple_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Cr.SSRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  let ρ : Representation k Γ (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
      map_one' := by simp; rfl
      map_mul' := fun a b => by rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl }
  obtain ⟨W', h1, h2⟩ := UpperTheory.V.Af.Cr.semisimple_restriction_normal ρ φ.range hN (fun U hU => hss U hU) W (by
    rintro _ ⟨g, rfl⟩ v hv
    exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

theorem UpperTheory.exists_quadratic_of_inertia :
    UpperTheory.V.Af.Cr.QuadCM → UpperTheory.V.Af.Cr.ImagGen → UpperTheory.V.Af.Cr.IneRes → UpperTheory.V.Af.Cr.ExQuadR := by
  intro hQ hI hR F Ω _ _ _ _ _ _ l _ h2 S hS
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hT : {v | ¬ S v}.Finite := Filter.eventually_cofinite.1 hS
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      v ∉ (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ℚ)) '' {v | ¬ S v} :=
    (hT.image _).eventually_cofinite_notMem
  obtain ⟨K₀, _, _, _, _, _, _, hK₀, hl, v₀, A, ⟨hv1, hv2⟩, hA, s, hs, hsn⟩ :=
    Cq.exQuad Ω l h2 _ (h1.and (hR ℚ F Ω))
  obtain ⟨d, y₀, hd, hy₀, hgen⟩ := hI K₀ hK₀
  obtain ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, y, hy, hgenK⟩ := hQ F Ω (d : F) (algebraMap K₀ Ω y₀)
    (by rw [← map_pow, hy₀, map_ratCast, map_ratCast]) (fun φ => by rw [map_ratCast]; exact_mod_cast hd)
  obtain ⟨w, hw, hwv⟩ := place_between (L := F) hA
  obtain ⟨t, rfl⟩ := hv2 A hA hs
  refine ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, fun j L hL x => ?_, w, A, ?_, hw, t, hs, ?_⟩
  · obtain ⟨a, b, rfl⟩ := hgenK x
    obtain ⟨z, hz⟩ := Cq.embPadic K₀ hK₀ l hl (j.comp (algebraMap K₀ Ω)) y₀
    rw [map_add (f := _), map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul]
    refine add_mem (hL a) (mul_mem (hL b) ?_)
    rw [RingHom.comp_apply] at hz
    rw [← hz]
    exact L.1.algebraMap_mem z
  · by_contra h
    exact hv1 ⟨w, h, hwv⟩
  · rintro ⟨u, rfl⟩
    have hu : u (algebraMap K₀ Ω y₀) = algebraMap K₀ Ω y₀ := by rw [← hy]; exact u.commutes y
    refine hsn ⟨{ u.toRingEquiv with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
    obtain ⟨a, b, rfl⟩ := hgen x
    show u _ = _
    simp only [map_add (f := _), map_mul, map_ratCast, hu]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.teichmuller_character_spec :
    UpperTheory.V.Sd.S3.Teich := by
  intro l _ c x m hcop hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hnd : ¬ l ∣ m := fun h =>
    (Nat.Prime.one_lt (Fact.out : l.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hm := hunit m hnd
  have hX : (x : c.O) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, hX, sub_self]
  have hres' : residue c.O (∑ i ∈ Finset.range m, (x : c.O) ^ i) = residue c.O (m : c.O) := by

    simp [map_sum, map_pow, hres]
  have hS : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    rw [← isUnit_map_iff (residue c.O), hres', isUnit_map_iff]
    exact hm
  have h0 : (x : c.O) - 1 = 0 := hS.mul_right_eq_zero.mp hgeom
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hv := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hA (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem open_kernel_killing_roots_of_unity {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) {C : Type} [Group C]
    (θ : G ℚ Ω →* C) (hk : KillsMu w θ) : IsOpen (θ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ w = 1}.Finite := by
    refine (nthRoots w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRoots (Nat.pos_of_ne_zero hw)).2 hζ
  haveI : Finite {ζ : Ω | ζ ^ w = 1} := hfin
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  refine hk g fun ζ hζ => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.theta_unramified_of_kills_roots_of_unity :
    UpperTheory.V.Sd.S3.ThetaUnr := by
  intro Ω _ _ _ l hl w hw θ hθ hk
  have h1 : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker := fun A hA g hg =>
    hk g fun ζ hζ => inertia_fixes_prime_to_roots A hw.ne_zero (hA w (Finset.mem_singleton_self w)) hg hζ
  refine ⟨h1, fun F hF => ?_⟩
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI : NeZero (l : Qbar l) := ⟨Nat.cast_ne_zero.2 hl.out.ne_zero⟩
  have hc : Nat.card (rootsOfUnity l (Qbar l)) = Nat.card (Multiplicative (ZMod l)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]; simp
  let e := mulEquivOfCyclicCardEq hc
  have hm : ∀ g, θ g ∈ rootsOfUnity l (Qbar l) := fun g => by
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hθ g
  have hker : (e.toMonoidHom.comp (θ.codRestrict _ hm)).ker = θ.ker := by
    ext g
    simp [MonoidHom.mem_ker, Subtype.ext_iff]
  have := hF (e.toMonoidHom.comp (θ.codRestrict _ hm))
  rw [hker] at this
  exact this (open_kernel_killing_roots_of_unity hw.ne_zero θ hk) h1
end
