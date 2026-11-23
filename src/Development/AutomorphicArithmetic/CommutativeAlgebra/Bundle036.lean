module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Development.EtaleCohomology.EtaleSheaves.Bundle085
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle019
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle035
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle028
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle034
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle015
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle020
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle083
public import Development.EtaleCohomology.EtaleSheaves.Bundle087
public import Development.EtaleCohomology.EtaleSheaves.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

private theorem evalRoot {A : Type} [CommRing A] (q : ℕ) :
    Polynomial.eval (AdjoinRoot.root (Polynomial.cyclotomic q A))
      (Polynomial.cyclotomic q (AdjoinRoot (Polynomial.cyclotomic q A))) = 0 := by
  rw [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
    Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

private theorem unitDeriv {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    IsUnit (AdjoinRoot.mk (Polynomial.cyclotomic q A)
      (Polynomial.derivative (Polynomial.cyclotomic q A))) := by
  rcases subsingleton_or_nontrivial (AdjoinRoot (Polynomial.cyclotomic q A)) with h | h
  · exact isUnit_of_subsingleton _
  · have hq' : IsUnit ((q : ℕ) : AdjoinRoot (Polynomial.cyclotomic q A)) := by
      simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))
    have := LateralTheory.E.LeafClosedSH0PfPrim.derivUnit q _ hq' (evalRoot q)
    rwa [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
      Polynomial.derivative_map, Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq] at this

private theorem injOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at ha
  refine (Polynomial.cyclotomic.monic q A).not_dvd_of_degree_lt
    (Polynomial.C_ne_zero.2 h0) ?_ ha
  rw [Polynomial.degree_cyclotomic, Polynomial.degree_C h0]
  exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)

private theorem surjOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))) := by
  intro p
  have := (Polynomial.cyclotomic.monic q A).finite_adjoinRoot
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := AdjoinRoot (Polynomial.cyclotomic q A)) p.asIdeal ⊥ (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (injOf q)]
      exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩

private noncomputable def rootPrim {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    Prim q (AdjoinRoot (Polynomial.cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))), by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact evalRoot q⟩

theorem UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}), IsUnit ((q : ℕ) : Γ(X, ⊤)) → ∀ x : X, ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (_ : Prim q Γ(V, ⊤)), f y = x := by
  intro q _ X hq x
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨p, hp⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
  have hnt : Nontrivial Γ(X, W) := by
    rcases subsingleton_or_nontrivial Γ(X, W) with h | h
    · exact absurd (Subsingleton.elim _ _) p.2.ne_top
    · exact h
  have hqW : IsUnit ((q : ℕ) : Γ(X, W)) := by
    simpa using hq.map (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  have het : Algebra.Etale Γ(X, W) (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    GlobalTheory.etale_adjoinRoot_of_isUnit_derivative (Polynomial.cyclotomic.monic q _) (unitDeriv q hqW)
  let φ : CommRingCat.of Γ(X, W) ⟶ CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 het)
  obtain ⟨y0, hy0⟩ := surjOf (A := Γ(X, W)) q p
  let y : Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))) := y0
  have hy : Spec.map φ y = p := hy0
  refine ⟨Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))),
    Spec.map φ ≫ hW.fromSpec, inferInstance, y,
    Prim.map (Scheme.ΓSpecIso _).inv.hom (rootPrim q hqW), ?_⟩
  rw [Scheme.Hom.comp_apply, hy, hp]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.DividedPowerChartLift

private theorem iso_incl (E : Spc) {a : Act} (Q : Pred a) (h : ∀ A x, Q.P A x) : IsIso (Sp.map E (incl Q)) := by
  refine UpperTheory.isIso_stackProductMap_of_bijective E (incl Q) (fun A => ⟨?_, ?_⟩) (fun _ => Function.bijective_id)
  · intro x y hxy
    exact Subtype.ext hxy
  · intro y
    exact ⟨⟨y, h A y⟩, rfl⟩

private theorem le_unit {N : ℕ} (i : Fin N) {Q : Pred (XC N)} (h : Q.Le (spanOn ((({i} : Finset (Fin N))) : Set (Fin N)))) :
    Q.Le (unitAt i) := by
  intro A x hx
  have h1 := h A x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_singleton, Set.image_singleton] at h1
  exact Ideal.span_singleton_eq_top.mp h1

private theorem loc_step {N : ℕ} (i : Fin N) (F' : Finset (Fin N)) (hi : i ∉ F') (Q : Pred (XC N))
    (hQ : Q.Le (spanOn ((Finset.cons i F' hi : Finset (Fin N)) : Set (Fin N))))
    (T : Scheme.{0}) (x : (XC N).D.obj Γ(T, ⊤)) (hx : Q.P _ x) :
    Loc T fun V g => (Q.inf (spanOn (F' : Set (Fin N)))).P _ ((XC N).D.map g.appTop x) ∨
      (Q.inf (unitAt i)).P _ ((XC N).D.map g.appTop x) := by
  have hs := hQ _ x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_cons, Set.image_insert_eq] at hs
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert] at hs
  obtain ⟨a, s, hsF, h1⟩ := hs
  let w : Fin 2 → Γ(T, ⊤) := ![x.1 i, s]
  have hw : Ideal.span (Set.range w) = ⊤ := by
    rw [Ideal.eq_top_iff_one, h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ a (Ideal.subset_span ⟨0, rfl⟩)) (Ideal.subset_span ⟨1, rfl⟩)
  obtain ⟨S, hS, hSP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T w hw
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨k, hk⟩ := hSP V g hg
  have hQx : Q.P _ ((XC N).D.map g.appTop x) := Q.map _ _ hx
  fin_cases k
  · right
    exact ⟨hQx, hk⟩
  · left
    refine ⟨hQx, ?_⟩
    apply Ideal.eq_top_of_isUnit_mem _ _ hk
    have hm := Ideal.mem_map_of_mem g.appTop.hom hsF
    rw [Ideal.map_span, ← Set.image_comp] at hm
    exact hm

private theorem all_of_units (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (hE : Inv q E) {c : Act} (π : Act.Hom c (XC N)) {m : ℕ}
    (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
    (H : ∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q)
    {F : Finset (Fin N)} (hF : F.Nonempty) :
    ∀ Q : Pred (XC N), Q.Le (spanOn (F : Set (Fin N))) → LHQ q E π d e cl Q := by
  induction hF using Finset.Nonempty.cons_induction with
  | singleton j =>
    intro Q hQ
    exact H j Q (le_unit j hQ)
  | cons j F' hj hF' ih =>
    intro Q hQ
    refine UpperTheory.leraHirsch_of_local_cover_of_inf q E hE π d e cl Q (Q.inf (spanOn (F' : Set (Fin N)))) (Q.inf (unitAt j))
      (fun A x hx => hx.1) (fun A x hx => hx.1) ?_ ?_ ?_ ?_
    · intro T x hx
      exact loc_step j F' hj Q hQ T x hx
    · exact ih _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2.2)

end UpperTheory.DividedPowerChartLift

theorem UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), 1 ≤ N → Inv q E → ∀ {c : Act} (π : Act.Hom c (XC N)) {m : ℕ} (d e : Fin m → ℤ)
        (cl : ∀ j, Ht q (Sp E c) (d j) (e j)), (∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q) → LH q (Sp.map E π) d e cl := by
  intro q _ N E hN hE c π m d e cl H
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  have hT := UpperTheory.DividedPowerChartLift.all_of_units q N E hE π d e cl H hne (Pred.top _) (fun A x _ => by
    show Ideal.span _ = ⊤
    rw [Finset.coe_univ, Set.image_univ]
    exact x.2)
  have hsq : Sp.map E (π.sub (Pred.top _)) ≫ Sp.map E (incl (Pred.top (XC N))) =
      Sp.map E (incl (Pred.comap π (Pred.top _))) ≫ Sp.map E π := rfl
  haveI : IsIso (Sp.map E (incl (Pred.comap π (Pred.top (XC N))))) :=
    UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  haveI : IsIso (Sp.map E (incl (Pred.top (XC N)))) := UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  have h2 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub (Pred.top _))) (Sp.map E π)
    (inv (Sp.map E (incl (Pred.comap π (Pred.top (XC N)))))) (inv (Sp.map E (incl (Pred.top (XC N)))))
    (by rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, hsq]) d e _ hT
  convert h2 using 1
  funext j
  rw [← GlobalTheory.EtC.pull_comp, IsIso.inv_hom_id, GlobalTheory.EtC.pull_id]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_middle_of_shortExact_acy :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₃, ∃ h : (free ℤ).obj P ⟶ S.X₂, h ≫ S.g = f := by
  intro Q S hS hA P hP f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) 0).2.1
  have hsub := hA P hP (0 + 1) (by norm_num)
  have h0 : HK.ext ℤ (sgl ((free ℤ).obj P)) z 0 (0 + 1) rfl (cl f) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (e (cl f)).1 h0
  obtain ⟨h, rfl⟩ := (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).2 y
  refine ⟨h, (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1 ?_⟩
  rw [← UpperTheory.hypercohomology_post_cl_eq_cl_comp]
  exact hy
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → (∀ U : Scheme.{0}, Q U → Subsingleton (Sec S.X₃ U)) → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₂, ∃ h : (free ℤ).obj P ⟶ S.X₁, h ≫ S.f = f := by
  intro Q S hS hQ P hP f
  have hsub := UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q S.X₃ hQ P hP 0
  have hz : f ≫ S.g = 0 := by
    apply (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1
    exact Subsingleton.elim _ _
  haveI := hS.mono_f
  exact ⟨hS.exact.lift f hz, hS.exact.lift_f f hz⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.Cb.CurveInd

private theorem sp_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B] :
    (∀ m : ℤ, Finite (Ht q (sp B) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := by
  have hH' := hH
  obtain ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩ := hH'
  have hsub : ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := fun m hm => c2 q Ω B hq m i hm
  refine ⟨fun m => ?_, hsub⟩
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · haveI : Subsingleton (Ht q (sp B) m i) := (a9 (ZMod q) (tw q i)).1 (sp B) m hm
    infer_instance
  · obtain ⟨hfin, hbij⟩ := hH0 hH q Ω hq i
    haveI := hfin
    exact Finite.of_surjective _ (hbij (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))).2
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact hB B
    · haveI := hsub m hm2
      infer_instance

private theorem aff_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U)
    {Y : Scheme.{0}} (j : Y ⟶ C) [IsOpenImmersion j] (hj : j.opensRange ≤ U) :
    (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
  by_cases hne : (j.opensRange : Set C).Nonempty
  · have hUne : (U : Set C).Nonempty := hne.mono hj
    have hcur := UpperTheory.isDedekindDomain_affine_sections_of_isCurve Ω c hc
    haveI : IsDedekindDomain (Γ(C, U) : Type) := (hcur.1 U hU hUne).1
    have hWa : IsAffineOpen j.opensRange := by
      have h1 : IsAffineOpen (hU.fromSpec ⁻¹ᵁ j.opensRange) := UpperTheory.dedekind_spec_open_isAffine (Γ(C, U) : Type) _
      have h2 := h1.image_of_isOpenImmersion hU.fromSpec
      rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec,
        inf_eq_right.mpr hj] at h2
    haveI : IsDedekindDomain (Γ(C, j.opensRange) : Type) := (hcur.1 _ hWa hne).1
    have e : j.opensRange ≤ c ⁻¹ᵁ ⊤ := by simp
    letI : Algebra Ω (Γ(C, j.opensRange) : Type) :=
      ((c.appLE ⊤ j.opensRange e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toAlgebra
    haveI : LocallyOfFiniteType c := by
      haveI : IsProper c := hc.2.1
      infer_instance
    haveI : Algebra.FiniteType Ω (Γ(C, j.opensRange) : Type) := by
      have hft := HasRingHomProperty.appLE @LocallyOfFiniteType c inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨j.opensRange, hWa⟩ e
      exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
        (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom x, by simp⟩))
    obtain ⟨h1, h2⟩ := sp_facts hH0 hH q Ω hq i hB (Γ(C, j.opensRange) : Type)
    have iso : Y ≅ Spec (CommRingCat.of (Γ(C, j.opensRange) : Type)) := j.isoOpensRange ≪≫ hWa.isoSpec
    refine ⟨fun m => ?_, fun m hm => ?_⟩
    · haveI := h1 m
      exact Finite.of_equiv _ (CurveCut.isoH (ZMod q) (tw q i) iso m)
    · haveI := h2 m hm
      exact (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
  · have hr : Set.range j.base = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have iso : Y ≅ ((⊥ : C.Opens) : Scheme.{0}) := IsOpenImmersion.isoOfRangeEq j (⊥ : C.Opens).ι (by
      rw [Scheme.Opens.range_ι]
      simpa using hr)
    have hs : ∀ m : ℤ, Subsingleton (Ht q (sch.obj Y) m i) := fun m =>
      haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := C) (tw q i) m
      (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
    refine ⟨fun m => ?_, fun m _ => hs m⟩
    haveI := hs m
    infer_instance

end UpperTheory.Cb.CurveInd

open UpperTheory.Cb.CurveInd in
theorem UpperTheory.leafCurve_of_leafH0 :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.LeafCurve := by
  intro hH0 hH q _ Ω _ _ hq i hB C c hc
  have hMV := UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero hH0
  haveI : IsProper c := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have key : ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j], j.opensRange ≤ ⊤ →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
    refine compact_open_induction_on (P := fun W : C.Opens => ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j],
      j.opensRange ≤ W →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i)) ⊤ ?_ ?_ ?_
    · simpa using (isCompact_univ : IsCompact (Set.univ : Set C))
    · intro Y j _ hj
      obtain ⟨h1, h2⟩ := aff_facts hH0 hH q Ω hq i hB c hc ⊥ (isAffineOpen_bot C) j hj
      exact ⟨h1, fun m hm => h2 m (by omega)⟩
    · intro S _ U ih Y j _ hj
      have hAB : j ⁻¹ᵁ S ⊔ j ⁻¹ᵁ (U : C.Opens) = ⊤ := by
        refine top_le_iff.mp fun y _ => ?_
        have hy : j.base y ∈ S ⊔ (U : C.Opens) := hj ⟨y, rfl⟩
        rcases (TopologicalSpace.Opens.mem_sup).mp hy with h | h
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inl h)
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inr h)
      obtain ⟨fA, sA⟩ := ih (j ⁻¹ᵁ S) ((j ⁻¹ᵁ S).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fB, sB⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2 ((j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fI, sI⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2
        ((j ⁻¹ᵁ S ⊓ j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2.2)
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.finite_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (fI n) (fA (n + 1)) (fB (n + 1))
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.subsingleton_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (sI n (by omega))
          (sA (n + 1) hm) (sB (n + 1) (by omega))
  obtain ⟨h1, h2⟩ := key C (𝟙 C) le_top
  exact ⟨h1 1, h1 2, h2⟩
end

section

open CategoryTheory Limits

namespace UpperTheory.NaturalityElementwise

variable {J : Type} [SmallCategory J]

private lemma sq_el {A B C D : AddCommGrpCat.{1}} {p : A ⟶ B} {q : B ⟶ D} {r : A ⟶ C} {s : C ⟶ D}
    (h : p ≫ q = r ≫ s) (x : A) : q.hom (p.hom x) = s.hom (r.hom x) := by
  have := congrArg (fun g => g.hom x) h
  simpa using this

private lemma nat_el {F G : J ⥤ AddCommGrpCat.{1}} (η : F ⟶ G) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (η.app b).hom ((F.map f).hom x) = (G.map f).hom ((η.app a).hom x) :=
  sq_el (η.naturality f) x

private lemma w_el {F : J ⥤ AddCommGrpCat.{1}} (c : Cocone F) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (c.ι.app b).hom ((F.map f).hom x) = (c.ι.app a).hom x := by
  have := congrArg (fun g => g.hom x) (c.w f)
  simpa using this

private lemma comp_el {F : J ⥤ AddCommGrpCat.{1}} {a b c : J} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
    (F.map (f ≫ g)).hom x = (F.map g).hom ((F.map f).hom x) := by
  simp

end UpperTheory.NaturalityElementwise

open UpperTheory.NaturalityElementwise in
theorem UpperTheory.etaleCohomology_class_killed_on_nbhd_pair :
    LateralTheory.E.NeighbourhoodKilling.PairFive := by
  intro J _ _ T j x hx

  have h0 : (T.cYm.ι.app j).hom ((T.fg.app j).hom x) = 0 := by
    rw [← sq_el (T.fg_w j) x, hx, map_zero]
  obtain ⟨j1, f1, h1⟩ := T.injYm j _ h0

  have h2 : (T.fg.app j1).hom ((T.Rm.map f1).hom x) = 0 := by
    rw [nat_el T.fg f1 x, h1]
  obtain ⟨w, hw⟩ := T.exR j1 _ h2

  have h3 : T.dlL.hom ((T.cWp.ι.app j1).hom w) = 0 := by
    rw [sq_el (T.dl_w j1) w, hw, w_el T.cR f1 x, hx]
  obtain ⟨y, hy⟩ := T.exWL _ h3
  obtain ⟨j2, y', rfl⟩ := T.surYp y

  let a : j1 ⟶ IsFiltered.max j1 j2 := IsFiltered.leftToMax j1 j2
  let b : j2 ⟶ IsFiltered.max j1 j2 := IsFiltered.rightToMax j1 j2
  have h4 : (T.cWp.ι.app _).hom ((T.Wp.map a).hom w - (T.rs.app _).hom ((T.Yp.map b).hom y')) = 0 := by
    rw [map_sub, w_el T.cWp a w, ← sq_el (T.rs_w _) ((T.Yp.map b).hom y'), w_el T.cYp b y', hy,
      sub_self]
  obtain ⟨j4, c, h5⟩ := T.injWp _ _ h4
  refine ⟨j4, f1 ≫ a ≫ c, ?_⟩
  have h6 : (T.Wp.map c).hom ((T.Wp.map a).hom w)
      = (T.rs.app j4).hom ((T.Yp.map c).hom ((T.Yp.map b).hom y')) := by
    rw [map_sub, sub_eq_zero] at h5
    rw [h5, nat_el T.rs c]
  rw [comp_el, ← hw, comp_el, ← nat_el T.dl a w, ← nat_el T.dl c, h6]
  exact T.cx j4 _
end

section

open CategoryTheory GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.E4 LateralTheory.E.LeafGhostCut in
theorem UpperTheory.relativeCohomology_connecting_naturality :
    LateralTheory.E.NeighbourhoodKilling.ObsNat := by
  intro q _ U E U' E' f f' u e comm i m w
  obtain ⟨w, rfl⟩ := w.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]
end
