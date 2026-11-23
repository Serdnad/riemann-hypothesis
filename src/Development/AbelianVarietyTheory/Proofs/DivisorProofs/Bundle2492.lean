module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.QuotDescent

private theorem descent_algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

private theorem descent_fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← descent_algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]


theorem functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  have := Spec.map_injective ((cancel_mono _).mp e)
  exact congrArg CommRingCat.Hom.hom this

theorem fnAct_mul : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ δ : Γ)
    (u : X.functionFieldˣ), fnAct ρ (γ * δ) u = fnAct ρ δ (fnAct ρ γ u) := by
  intro X _ Γ _ ρ γ δ u
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI : IsIso (ρ δ).asIso.hom := Iso.isIso_hom (ρ δ).asIso
  haveI : IsIso (ρ (γ * δ)).asIso.hom := Iso.isIso_hom (ρ (γ * δ)).asIso
  have hc : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by
    rw [map_mul, Aut.mul_asIso]; rfl
  apply Units.ext
  change functionFieldMap (ρ (γ * δ)).asIso.hom (u : X.functionField) =
    functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField))
  have key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom →
      functionFieldMap f (u : X.functionField) =
        functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField)) := by
    rintro f _ rfl
    rw [functionFieldMap_comp]
    rfl
  exact key _ inferInstance hc

theorem descent : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  intro F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR
  obtain ⟨D, c, hcls, hcoc, heq, hin⟩ := hR
  haveI : IsIntegral W := hq.isIntegral
  haveI : Surjective q := hq.surjective
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective
  let σ : Γ → X.functionField →+* X.functionField := fun γ =>
    haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso; functionFieldMap (ρ γ).asIso.hom
  have hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u :=
    fun _ _ => rfl
  have hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a) := by
    intro γ δ a
    by_cases ha : a = 0
    · simp [ha]
    · have := congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))
      rwa [hσu, hσu, hσu] at this
  have hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ := fun γ δ => by
    rw [hcoc, Units.val_mul, hσu]
  have htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1 := by
    intro γ hγ
    have hη : (ρ γ).asIso.hom (genericPoint X) = genericPoint X := by
      haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
      have h1 := (genericPoint_spec X).image (ρ γ).asIso.hom.continuous
      have hs : Function.Surjective (ρ γ).asIso.hom.base := (ρ γ).asIso.hom.surjective
      simp only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1
      exact h1.eq (genericPoint_spec X)
    have hfix := descent_fromSpecResidueField_comp_eq_of_fixes X Γ ρ γ (genericPoint X) hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)
    have h0 := hin γ _ 1 hfix (D.isEqn_genericPoint 1)
    have h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0 := by
      by_contra hne
      exact (zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)
    rw [map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one] at h1
    exact h1
  obtain ⟨f, hf⟩ := GlobalTheory.T.hilbert90_finite_rightAction_charZero_field _ Γ σ hσ c hcoc' htriv
  have hfu : ∀ γ, fnAct ρ γ f = c γ * f := fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)
  set D' := D - CartierDiv.principal f with hD'
  have hD : D' + CartierDiv.principal f = D := sub_add_cancel _ _
  have hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).asIso.hom x) g → D'.IsEqn x (fnAct ρ γ g) := by
    intro γ x g h
    have h1 := heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))
    have h2 := h1.sub (CartierDiv.isEqn_principal f x)
    have e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f := by
      rw [map_mul, hfu]; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h2
  have hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D'.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1) := by
    intro γ x g hx h
    have h1 := hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))
    have e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹ := by
      rw [map_mul, hfu]; simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h1
  have hloc := GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'
  have key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y →
      D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨g, hg, hgx⟩ := hloc x
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg
    refine ⟨b, fun x' hx' => ?_⟩
    obtain ⟨γ, rfl⟩ := (hq.apply_eq_iff x x').1 hx'.symm
    rw [hb]
    have hp : (ρ γ⁻¹).asIso.hom ((ρ γ).asIso.hom x) = x := by
      rw [map_inv]
      exact Scheme.inv_hom_apply _ _
    have := hinv' γ⁻¹ ((ρ γ).asIso.hom x) g (by rw [hp]; exact hgx)
    rwa [hg] at this
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_cartierDivisor_group_quotient_descent X W Γ ρ q hq D' key
  refine ⟨toLB E, isLB_toLB E, ?_⟩
  rw [GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq X W q D' E hE]
  calc cls (toLB D') (isLB_toLB D') = toPic D' := (toPic_apply D').symm
    _ = toPic D := by rw [hD', map_sub, toPic_principal, sub_zero]
    _ = cls L hL := hcls

end GlobalTheory.QuotDescent
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_inc_le_one (inc : E →+* PadicAlgCl l) (r : 𝓞 E) : ‖inc (r : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((RingOfIntegers.isIntegral_coe r).map inc.toIntAlgHom)

theorem norm_natCast_eq_one' {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : PadicAlgCl l)‖ = 1 := by
  have h : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hm

theorem norm_ev_latHat_le_one (inc : E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) (hev : EvOk inc ev) {M : ℕ}
    (L : Set (Fin M → E)) (hL : ∀ x ∈ L, ∀ i, x i ∈ (algebraMap (𝓞 E) E).range)
    (z : Fin M → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (hz : z ∈ StandardLattice.latHat F E L) (a : Fin M) :
    ‖ev (z a)‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    obtain ⟨r, hr⟩ := hL x hx a
    have e : c ⊗ₜ[F] x a = (c ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show ‖ev (c ⊗ₜ[F] x a)‖ ≤ 1
    rw [e, map_mul, norm_mul, hev.1, ← hr]
    exact mul_le_one₀ (hev.2.1 c hc) (norm_nonneg _) (norm_inc_le_one inc r)
  | zero => simp
  | add y w _ _ hy hw =>
    show ‖ev (y a + w a)‖ ≤ 1
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hw)
  | neg y _ hy =>
    show ‖ev (-(y a))‖ ≤ 1
    rwa [map_neg, norm_neg]

end General

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem selfDualLattice_frame_span_integral_coordinates (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    (x : Fin V.rank → D.host.E) (hx : x ∈ StandardLattice.L0c D V) (i : Fin V.rank) :
    x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hx' : ∑ j, x j • V.frame j ∈ V.L0 := hx
  rw [hL0, Submodule.mem_span_range_iff_exists_fun] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hc' : ∑ j, ((c j : D.host.E)) • V.frame j = ∑ j, x j • V.frame j := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    exact (algebraMap_smul D.host.E (c j) (V.frame j))
  have h2 := congrArg (fun v => V.frame.repr v i) hc'
  simp only [Module.Basis.repr_sum_self] at h2
  exact ⟨c i, h2⟩

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem norm_ev_hLat_le_one (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l) (hev : EvOk inc ev)
    (y : Bridge.Gf V) (x : Fin V.rank → D.host.E) (hx : x ∈ Bridge.hLat V y) (a : Fin V.rank) :
    ‖ev (Matrix.mulVec ((y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))⁻¹).val
      (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) a)‖ ≤ 1 := by
  unfold Bridge.hLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' := hx
    simp only [Set.mem_ofPred, Subgroup.coe_inv] at hx'
    exact norm_ev_latHat_le_one inc ev hev (StandardLattice.L0c D V) (fun x hx i => selfDualLattice_frame_span_integral_coordinates V hL0 x hx i) _ hx' a
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero]
    rw [show (fun _ : Fin V.rank => (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) = 0 from rfl]
    simp
  | add x w _ _ hx hw =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (x + w) i) =
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) +
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] w i) := by
      funext i; simp [TensorProduct.tmul_add]
    rw [e, Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hw)
  | smul r x _ hx =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r • x) i) =
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) •
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      congr 1
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1]
    exact mul_le_one₀ (norm_inc_le_one inc r) (norm_nonneg _) hx

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

theorem locBasis_integral : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  intro D V l _ inc ev hev hL0 y B hB a b
  obtain ⟨s, hs, hmem⟩ := (hB (fun k => B.val k b)).2 ⟨1, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), fun c => by
    have e : Matrix.mulVec (B⁻¹).val (fun k => B.val k b) c = ((B⁻¹).val * B.val) c b := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩⟩
  have h := norm_ev_hLat_le_one V hL0 inc ev hev y _ hmem a
  have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((s : D.host.E) • fun k => B.val k b) i)) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) •
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] B.val i b) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1, map_natCast,
    norm_natCast_eq_one' hs, one_mul] at h
  rw [← map_inv, Units.val_mul, Matrix.mul_apply]
  refine le_of_eq_of_le (congrArg norm ?_) h

  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, hev.1]
  rfl

end GlobalTheory.LocBasisInt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelElement_local_coprime_acts_trivially : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  first | exact @GlobalTheory.FrameTriv.triv_of_isLocEnv | exact GlobalTheory.FrameTriv.triv_of_isLocEnv | (intros; apply GlobalTheory.FrameTriv.triv_of_isLocEnv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_finiteAdeleEmbeddingExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, EvOk i ev := by
  first | exact @GlobalTheory.EvExtend.exists_evOk | exact GlobalTheory.EvExtend.exists_evOk | (intros; apply GlobalTheory.EvExtend.exists_evOk <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

theorem _root_.GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  first | exact @GlobalTheory.ShareOn.Reading.rdFun_mem_SS | exact GlobalTheory.ShareOn.Reading.rdFun_mem_SS | (intros; apply GlobalTheory.ShareOn.Reading.rdFun_mem_SS <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

theorem _root_.GlobalTheory.T.modelCuspForms_span_usedRunReadings : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a), 0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka → ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  first | exact @GlobalTheory.ShareOn.Reading.rdFun_onto | exact GlobalTheory.ShareOn.Reading.rdFun_onto | (intros; apply GlobalTheory.ShareOn.Reading.rdFun_onto <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cuspForm_family_linearIndependent : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ) (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  first | exact @GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | exact GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | (intros; apply GlobalTheory.ShareOn.Reading.rdLin_linearIndependent <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.isLevelComponentTransport_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  first | exact @GlobalTheory.ShareOn.isTransp_comp | exact GlobalTheory.ShareOn.isTransp_comp | (intros; apply GlobalTheory.ShareOn.isTransp_comp <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  first | exact @GlobalTheory.ShareOn.transp_reads_const_mul | exact GlobalTheory.ShareOn.transp_reads_const_mul | (intros; apply GlobalTheory.ShareOn.transp_reads_const_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.unique_up_to_target_group : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k₁ a₁ → IsTransp p r i v ψ γ k k₂ a₂ → k₁ = k₂ ∧ a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  first | exact @GlobalTheory.ShareOn.IsTransp.uniq | exact GlobalTheory.ShareOn.IsTransp.uniq | (intros; apply GlobalTheory.ShareOn.IsTransp.uniq <;> assumption)
end

end

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localBasis_integral_relative_adelicPoint : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  first | exact @GlobalTheory.LocBasisInt.locBasis_integral | exact GlobalTheory.LocBasisInt.locBasis_integral | (intros; apply GlobalTheory.LocBasisInt.locBasis_integral <;> assumption)

end
end
