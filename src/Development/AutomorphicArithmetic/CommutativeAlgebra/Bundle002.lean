module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

private theorem restrict_comm {N Y : Scheme.{0}} (m : N ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (m ⁻¹ᵁ V)) (hle : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ V) :
    (m ∣_ V) ≫ hV.isoSpec.hom = hW.isoSpec.hom ≫ Spec.map (m.appLE V (m ⁻¹ᵁ V) hle) := by
  rw [← cancel_epi hW.isoSpec.inv, ← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc,
    IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec m hV hW hle, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]

private theorem prop_restrict (Q : MorphismProperty Scheme.{0}) [Q.RespectsIso]
    {N Y : Scheme.{0}} (m : N ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (m ⁻¹ᵁ V)) (hle : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ V)
    (h : Q (Spec.map (m.appLE V (m ⁻¹ᵁ V) hle))) : Q (m ∣_ V) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso Q _ hV.isoSpec.hom,
    restrict_comm m V hV hW hle, MorphismProperty.cancel_left_of_respectsIso Q]
  exact h

theorem UpperTheory.mono_flat_of_affine_appLE_flat_epi :
    ∀ {N Y P : Scheme.{0}} (f : Y ⟶ P) [IsAffineHom f] (f' : N ⟶ P) [IsAffineHom f']
        (m : N ⟶ Y), m ≫ f = f' →
        (∀ (U : P.Opens), IsAffineOpen U → ∀ hle : f' ⁻¹ᵁ U ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U),
          (m.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ U) hle).hom.Flat ∧ Epi (m.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ U) hle)) →
        Mono m ∧ Flat m := by
  intro N Y P f _ f' _ m hm H
  subst hm
  have hcov : ⨆ U : P.affineOpens, f ⁻¹ᵁ (U : P.Opens) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine ⟨?_, ?_⟩
  · change MorphismProperty.monomorphisms Scheme m
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.monomorphisms Scheme) _ hcov]
    intro U
    obtain ⟨-, hep⟩ := H U.1 U.2 le_rfl
    refine prop_restrict (MorphismProperty.monomorphisms Scheme) m _ (U.2.preimage f)
      (U.2.preimage (m ≫ f)) le_rfl ?_
    haveI : Epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl) := hep
    haveI := op_mono_of_epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)
    exact Functor.map_mono Scheme.Spec (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl).op
  · haveI : IsZariskiLocalAtTarget @Flat.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0}) (Q := RingHom.Flat)
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ hcov]
    intro U
    obtain ⟨hfl, -⟩ := H U.1 U.2 le_rfl
    have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
    have hW : IsAffineOpen (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) := U.2.preimage (m ≫ f)
    have e := restrict_comm m _ hV hW le_rfl
    haveI : Flat (Spec.map (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)) :=
      HasRingHomProperty.Spec_iff.mpr hfl
    have e' : m ∣_ (f ⁻¹ᵁ U.1) =
        hW.isoSpec.hom ≫ Spec.map (m.appLE _ _ le_rfl) ≫ hV.isoSpec.inv := by
      rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e']
    infer_instance
end

section

open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_dual_basis_of_parameters :
    ∀ {R : Type} [CommRing R] [Algebra ℂ R] (ev : R →ₐ[ℂ] ℂ) {d : ℕ} (t : Fin d → R) (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev b • ψ ω) → Function.Surjective ψ → (∀ l, ev (t l) = 0) → (∀ u : R, ev u = 0 → ∃ (c : R) (g : Fin d → R), ev c ≠ 0 ∧ c * u = ∑ l, g l * t l) → ∃ φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), φ (b • ω) = ev b • φ ω) ∧ (∀ l, φ (D ℂ R (t l)) = Pi.single l 1) ∧ (∀ ω, φ ω = 0 → ψ ω = 0) ∧ ∀ (u c : R) (g : Fin d → R), ev u = 0 → ev c ≠ 0 → c * u = ∑ l, g l * t l → ∀ l, ev (g l) = ev c * φ (D ℂ R u) l := by
  intro R _ _ ev d t ψ hψ hsurj ht hloc
  have key : ∀ χ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), χ (b • ω) = ev b • χ ω) →
      ∀ (u c : R) (g : Fin d → R), ev u = 0 → c * u = ∑ l, g l * t l →
      ev c • χ (D ℂ R u) = ∑ l, ev (g l) • χ (D ℂ R (t l)) := by
    intro χ hχ u c g hu hcu
    have h := congrArg (fun x => χ (D ℂ R x)) hcu

    simp only [Derivation.leibniz, map_sum, map_add (f := _), hχ, hu, ht, zero_smul, add_zero] at h
    exact h
  set v : Fin d → (Fin d → ℂ) := fun l => ψ (D ℂ R (t l)) with hvdef
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro y hy
    clear hy
    obtain ⟨ω, rfl⟩ := hsurj y
    have hω : ω ∈ Submodule.span R (Set.range (D ℂ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      set u' := u - algebraMap ℂ R (ev u) with hu'
      have hDu : D ℂ R u = D ℂ R u' := by
        rw [hu', map_sub, Derivation.map_algebraMap, sub_zero]
      have hev : ev u' = 0 := by
        rw [hu', map_sub, AlgHom.commutes]
        simp
      obtain ⟨c, g, hc, hcu⟩ := hloc u' hev
      have h := key ψ hψ u' c g hev hcu
      rw [hDu]
      have : ψ (D ℂ R u') = (ev c)⁻¹ • ∑ l, ev (g l) • v l := by
        rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro l _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [hψ]
      exact Submodule.smul_mem _ _ hx
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  set bs := Module.Basis.mk hli hspan with hbs
  have hbv : ∀ l, ψ (D ℂ R (t l)) = bs l := by
    intro l
    rw [hbs, Module.Basis.mk_apply]
  have h2 : ∀ l, (bs.equivFun.toLinearMap ∘ₗ ψ) (D ℂ R (t l)) = Pi.single l 1 := by
    intro l
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hbv]
    ext j
    rw [Module.Basis.equivFun_self]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Pi.single_apply, Ne.symm hlj]
  refine ⟨bs.equivFun.toLinearMap ∘ₗ ψ, ?_, h2, ?_, ?_⟩
  · intro b ω
    simp [hψ]
  · intro ω hω
    simpa using hω
  · intro u c g hu hc hcu l
    have h := key (bs.equivFun.toLinearMap ∘ₗ ψ) (by intro b ω; simp [hψ]) u c g hu hcu
    simp only [h2] at h
    have h3 := congrFun h l
    simp [Finset.sum_apply, Pi.single_apply] at h3
    rw [← h3]
    rfl
end

section

open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_localization_away :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S] (f : R) [IsLocalization.Away f S] (ev : S →+* ℂ) {d : ℕ} (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev (algebraMap R S b) • ψ ω) → (∀ ω : Ω[R⁄ℂ], ψ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]), (∀ i, ev (algebraMap R S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ ψ' : Ω[S⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : S) (ω : Ω[S⁄ℂ]), ψ' (b • ω) = ev b • ψ' ω) ∧ (∀ ω : Ω[R⁄ℂ], ψ' (KaehlerDifferential.map ℂ ℂ R S ω) = ψ ω) ∧ (∀ ω : Ω[S⁄ℂ], ψ' ω = 0 → ∃ (m : ℕ) (b : Fin m → S) (ω' : Fin m → Ω[S⁄ℂ]), (∀ i, ev (b i) = 0) ∧ ω = ∑ i, b i • ω' i) := by
  intro R S _ _ _ _ _ _ f _ ev d ψ h1 h2
  letI : Module R (Fin d → ℂ) := Module.compHom (Fin d → ℂ) (ev.comp (algebraMap R S))
  have hu : ∀ x : Submonoid.powers f, ev (algebraMap R S x) ≠ 0 := fun x =>
    ((IsLocalization.map_units S x).map ev).ne_zero
  have hunit : ∀ x : Submonoid.powers f,
      IsUnit ((algebraMap R (Module.End R (Fin d → ℂ))) x) := by
    intro x
    rw [Module.End.isUnit_iff]
    refine ⟨fun v w hvw => smul_right_injective (Fin d → ℂ) (hu x) hvw,
      fun v => ⟨(ev (algebraMap R S x))⁻¹ • v, ?_⟩⟩
    show ev (algebraMap R S x) • ((ev (algebraMap R S x))⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (hu x), one_smul]
  let g : Ω[R⁄ℂ] →ₗ[R] (Fin d → ℂ) :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun b ω => h1 b ω }
  let L := IsLocalizedModule.lift (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) g hunit
  have hL : ∀ η, L (KaehlerDifferential.map ℂ ℂ R S η) = ψ η := fun η =>
    IsLocalizedModule.lift_apply _ _ _ _ η
  have hLs : ∀ (r : R) (ω : Ω[S⁄ℂ]), L (r • ω) = ev (algebraMap R S r) • L ω :=
    fun r ω => L.map_smul r ω
  have hLS : ∀ (b : S) (ω : Ω[S⁄ℂ]), L (b • ω) = ev b • L ω := by
    intro b ω
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers f) b
    have h := hLs (t : R) (b • ω)
    rw [← algebraMap_smul S (t : R) (b • ω), smul_smul, mul_comm, ht, algebraMap_smul, hLs] at h
    apply smul_right_injective (Fin d → ℂ) (hu t)
    show ev (algebraMap R S t) • L (b • ω) = ev (algebraMap R S t) • ev b • L ω
    rw [← h, ← ht, map_mul, mul_comm, mul_smul]
  have hLC : ∀ (c : ℂ) (ω : Ω[S⁄ℂ]), L (c • ω) = c • L ω := by
    intro c ω
    obtain ⟨⟨η, s⟩, hs⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
    have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
    have e1 : ev (algebraMap R S s) • L ω = ψ η := by rw [← hLs, hs', hL]
    have e2 : ev (algebraMap ℂ S c) • ψ η = c • ψ η := by
      rw [show c • ψ η = ψ (c • η) from (ψ.map_smul c η).symm, ← algebraMap_smul R c η, h1,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul S c ω, hLS]
    apply smul_right_injective (Fin d → ℂ) (hu s)
    show ev (algebraMap R S s) • ev (algebraMap ℂ S c) • L ω = ev (algebraMap R S s) • c • L ω
    rw [smul_comm (ev (algebraMap R S s)) (ev (algebraMap ℂ S c)), e1, e2,
      smul_comm (ev (algebraMap R S s)) c, e1]
  refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := hLC }, hLS, hL, ?_⟩
  intro ω hω
  change L ω = 0 at hω
  obtain ⟨⟨η, s⟩, hs⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
  have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
  have hη : ψ η = 0 := by rw [← hL, ← hs', hLs, hω, smul_zero]
  obtain ⟨m, b, ω', hb, hηeq⟩ := h2 η hη
  let u : S := IsLocalization.mk' S (1 : R) s
  have hu1 : u * algebraMap R S s = 1 := by rw [IsLocalization.mk'_spec, map_one]
  refine ⟨m, fun i => algebraMap R S (b i),
    fun i => u • KaehlerDifferential.map ℂ ℂ R S (ω' i), hb, ?_⟩
  calc ω = u • ((s : R) • ω) := by
        rw [← algebraMap_smul S (s : R) ω, smul_smul, hu1, one_smul]
    _ = u • KaehlerDifferential.map ℂ ℂ R S (∑ i, b i • ω' i) := by rw [hs', hηeq]
    _ = ∑ i, algebraMap R S (b i) • u • KaehlerDifferential.map ℂ ℂ R S (ω' i) := by

        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← algebraMap_smul S (b i), smul_comm]
end

section

private theorem UpperTheory.finite_of_finite_comp_injective_noetherian {P B C : Type*} [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing P] (f : P →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  have hC : Module.Finite P C := h
  let gl : B →ₗ[P] C :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply,
          RingHom.id_apply] }
  haveI : IsNoetherian P C := isNoetherian_of_isNoetherianRing_of_finite P C
  haveI : IsNoetherian P B := isNoetherian_of_injective gl hg
  exact Module.IsNoetherian.finite P B

private theorem UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect (k : Type*) [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
    (ι : Type*) [Finite ι] [ExpChar (MvPolynomial ι k) p] (e : ℕ) :
    (iterateFrobenius (MvPolynomial ι k) p e).Finite := by
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_pos k p).ne')
    · simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have hc : (iterateFrobenius (MvPolynomial ι k) p e).comp MvPolynomial.C
        = MvPolynomial.C.comp (iterateFrobenius k p e) := by
      ext a
      simp [iterateFrobenius_def, map_pow]
    rw [hc]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (bijective_iterateFrobenius k p e).2)

private theorem UpperTheory.module_finite_integralClosure_of_frobenius_finite (P L F : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [Field L] [Algebra P L] [IsFractionRing P L] [Field F] [Algebra P F]
    [Algebra L F] [IsScalarTower P L F] [FiniteDimensional L F] (p : ℕ) [ExpChar P p]
    [ExpChar F p] (hσ : ∀ e, (iterateFrobenius P p e).Finite) :
    Module.Finite P (integralClosure P F) := by
  let E := separableClosure L F
  haveI : FiniteDimensional E F := FiniteDimensional.right L E F
  haveI : IsPurelyInseparable E F := separableClosure.isPurelyInseparable L F
  haveI : ExpChar E p := IntermediateField.expChar' E p
  haveI : IsScalarTower P E F := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply P L E r, ← IsScalarTower.algebraMap_apply L E F,
      IsScalarTower.algebraMap_apply P L F])
  set e := IsPurelyInseparable.exponent E F
  have hpow : ∀ x : F, x ^ p ^ e ∈ E := fun x => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p x
    rw [← hy]
    exact y.2
  haveI : Module.Finite P (integralClosure P E) :=
    IsIntegralClosure.finite P L E (integralClosure P E)
  have hq : p ^ e ≠ 0 := pow_ne_zero _ (expChar_pos F p).ne'
  let fr : integralClosure P F →+* integralClosure P E :=
    { toFun := fun b => ⟨⟨b.1 ^ p ^ e, hpow b.1⟩, by
        rw [mem_integralClosure_iff,
          ← isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) (algebraMap E F).injective]
        exact b.2.pow _⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [mul_pow]
      map_zero' := by
        apply Subtype.ext; apply Subtype.ext; simp [zero_pow hq]
      map_add' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [add_pow_expChar_pow] }
  have hinj : Function.Injective fr := by
    intro a b h
    have h' : a.1 ^ p ^ e = b.1 ^ p ^ e :=
      congrArg (fun y : integralClosure P E => ((y.1 : E) : F)) h
    apply Subtype.ext
    apply (iterateFrobenius F p e).injective
    simpa [iterateFrobenius_def] using h'
  have hcomp : fr.comp (algebraMap P (integralClosure P F)) =
      (algebraMap P (integralClosure P E)).comp (iterateFrobenius P p e) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    simp only [fr, iterateFrobenius_def, map_pow, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    have h1 : ((algebraMap P (integralClosure P F) r : integralClosure P F) : F) =
        algebraMap P F r := rfl
    have h2 : (((algebraMap P (integralClosure P E) r : integralClosure P E) : E) : F) =
        algebraMap P F r := by
      rw [IsScalarTower.algebraMap_apply P E F]
      rfl
    simp only [SubmonoidClass.coe_pow, h1, h2]
  have hf := UpperTheory.finite_of_finite_comp_injective_noetherian (algebraMap P (integralClosure P F)) fr hinj (by
    rw [hcomp]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp (hσ e))
  exact RingHom.finite_algebraMap.mp hf

theorem UpperTheory.module_finite_integralClosure_finiteExt_perfect :
    ∀ (k A K F : Type) [Field k] [PerfectField k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
        [Field K] [Algebra A K] [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
        [FiniteDimensional K F], Module.Finite A (integralClosure A F) := by
  intro k A K F
  intros
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨p, hp⟩ := ExpChar.exists k
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAF : Function.Injective (algebraMap A F) := by
    rw [IsScalarTower.algebraMap_eq A K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective A K)
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hAF
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hginj
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) F :=
    (faithfulSMul_iff_algebraMap_injective _ F).mpr (hAF.comp hginj)
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) F := FractionRing.liftAlgebra _ F
  letI : Algebra (FractionRing A) F := FractionRing.liftAlgebra A F
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    FractionRing.liftAlgebra _ (FractionRing A)
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    inferInstance
  haveI : FiniteDimensional (FractionRing A) F := by
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (RingEquiv.refl F) ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) k))
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) F,
      ← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A),
      IsScalarTower.algebraMap_apply _ A (FractionRing A),
      ← IsScalarTower.algebraMap_apply A (FractionRing A) F,
      ← IsScalarTower.algebraMap_apply _ A F]
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) F :=
    Module.Finite.trans (FractionRing A) F
  haveI : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  haveI : ExpChar F p := expChar_of_injective_algebraMap hAF p
  haveI : ExpChar (MvPolynomial (Fin s) k) p :=
    expChar_of_injective_algebraMap (algebraMap k (MvPolynomial (Fin s) k)).injective p
  have hP := UpperTheory.module_finite_integralClosure_of_frobenius_finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) F p
    (UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect k p (Fin s))
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ A
  let φ : integralClosure (MvPolynomial (Fin s) k) F →ₗ[MvPolynomial (Fin s) k]
      integralClosure A F :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun y =>
    ⟨⟨y.1, isIntegral_trans (R := MvPolynomial (Fin s) k) y.1 y.2⟩, rfl⟩
  haveI : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A F) :=
    Module.Finite.of_surjective φ hφ
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A (integralClosure A F)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_away :
    ∀ {R B L B' : Type} [CommRing R] [CommRing B] [CommRing L] [CommRing B'] (e : R), IsIdempotentElem e →
        ∀ (T : Submonoid R), (∀ s ∈ T, IsIdempotentElem s) →
        ∀ [Algebra R B] [IsLocalization.Away e B] [Algebra R L] [IsLocalization T L] [Algebra L B']
          [IsLocalization.Away (algebraMap R L e) B'] (jB : B →+* B'),
        (∀ r, jB (algebraMap R B r) = algebraMap L B' (algebraMap R L r)) →
        ∃ S : Submonoid B, (∀ s ∈ S, IsIdempotentElem s) ∧ @IsLocalization B _ S B' _ jB.toAlgebra := by
  intro R B L B' _ _ _ _ e he T hT _ _ _ _ _ _ jB hj
  letI : Algebra R B' := ((algebraMap L B').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B B' := jB.toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq (fun r => (hj r).symm)
  have hloc : IsLocalization (T ⊔ Submonoid.powers e) B' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
      have h1 := (IsLocalization.map_units L ⟨y, hy⟩).map (algebraMap L B')
      have h2 := IsLocalization.map_units B'
        (⟨algebraMap R L e ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R L e))
      simp only [IsScalarTower.algebraMap_apply R L B', map_mul, map_pow] at h1 h2 ⊢
      exact h1.mul h2
    · intro z
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h1⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R L e)) z
      obtain ⟨⟨r, t⟩, h2⟩ := IsLocalization.surj T a
      refine ⟨⟨r, ⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩⟩, ?_⟩
      simp only at h1 h2 ⊢
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' r, ← h2]
      simp only [map_mul, map_pow] at h1 ⊢
      linear_combination (algebraMap L B' (algebraMap R L t)) * h1
    · intro x y hxy
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' y] at hxy
      obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R L e)) B').mp hxy
      simp only at hc
      rw [← map_pow, ← map_mul, ← map_mul, IsLocalization.eq_iff_exists T L] at hc
      obtain ⟨t, ht⟩ := hc
      refine ⟨⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩, ?_⟩
      simp only
      linear_combination ht
  have key := IsLocalization.isLocalization_of_submonoid_le B B' (Submonoid.powers e)
    (T ⊔ Submonoid.powers e) le_sup_right
  refine ⟨(T ⊔ Submonoid.powers e).map (algebraMap R B), ?_, key⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
  exact ((hT y hy).mul (he.pow n)).map (algebraMap R B)
end
