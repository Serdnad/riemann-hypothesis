module

import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.SetTheory.ZFC.PSet
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem mem_range_of_tmul_eq {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (x : Ω)
    (h : x ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] x) : x ∈ (algebraMap L Ω).range := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  let m : Ω ⊗[L] Ω →ₗ[L] Ω := TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id
  have e := congrArg m h
  simp only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1,
    one_smul, LinearEquiv.coe_coe] at e
  exact ⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩

theorem factor_of_epi {O F Ω₀ Ω : Type} [CommRing O] [Field F] [Field Ω₀] [Field Ω]
    (β : O →+* F) (hβ : Epi (CommRingCat.ofHom β)) (a : O →+* Ω₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (h : fn.comp a = cst.comp β) : ∃ a' : F →+* Ω₀, a'.comp β = a := by
  let _ := fn.toAlgebra
  have e : CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) =
      CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst) := by
    ext o
    have ho : cst (β o) = algebraMap Ω₀ Ω (a o) := by
      rw [RingHom.algebraMap_toAlgebra]; exact (RingHom.congr_fun h o).symm
    change cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)
    rw [ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have e2 := hβ.left_cancellation _ _ e
  have key : ∀ u : F, ∃ w : Ω₀, fn w = cst u := by
    intro u
    have hu := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u
    change cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu
    obtain ⟨w, hw⟩ := mem_range_of_tmul_eq (L := Ω₀) (cst u) hu
    exact ⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩
  choose g hg using key
  have inj := fn.injective
  refine ⟨{ toFun := g
            map_one' := inj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := inj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }, ?_⟩
  ext o
  apply inj
  change fn (g (β o)) = fn (a o)
  rw [hg]
  exact (RingHom.congr_fun h o).symm

theorem eq_genPt_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, rfl⟩ := this
  let _ := hf.toField
  have : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

theorem mem_of_dense_of_noGen {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  apply PositivityTheory.HtPt.Ml.mem_of_dense_of_max <;> assumption

theorem noetherianSpace_baseChange {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

theorem gen_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y),
    Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono
  have hepi : Epi (CommRingCat.ofHom β) := by
    have h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := hmono
    have h2 : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h1
    exact unop_epi_of_mono (CommRingCat.ofHom β).op
  let a : O →+* A.Ω₀ := (Spec.preimage (A.ξ₀ ≫ Y.s)).hom
  have ha : spMap a = A.ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : A.fn.comp a = A.cst.comp β := by
    have h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β) := by
      rw [← A.cst_over]
      have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
      calc spMap (A.fn.comp a) = spMap A.fn ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨a', ha'⟩ := factor_of_epi β hepi a A.fn A.cst hfa
  have hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β := by
    rw [← ha, ← ha']
    simp only [spMap, ← Spec.map_comp]; rfl
  let z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β) := pullback.lift A.ξ₀ (spMap a') hsq
  have hz : z ≫ pullback.fst _ _ = A.ξ₀ := pullback.lift_fst _ _ _
  let y0 : ↥(pullback Y.s (spMap β)) := z (IsLocalRing.closedPoint A.Ω₀)
  have hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀ := by
    show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _
    rw [← hz]
    rfl
  have hmax : ∀ y', y' ⤳ y0 → y' = y0 := by
    intro y' hy
    have h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀ := hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous
    have h2 := eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1
    exact (pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)
  have := noetherianSpace_baseChange Y.proj β
  have := Y.jQ_open
  have hy0 : y0 ∈ Set.range Y.jQ :=
    mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax
  have hrange : Set.range z ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint A.Ω₀ := Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _
    rw [this]
    exact hy0
  refine ⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩
  show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hz]

end GlobalTheory.CompanionTheory.Ar.GenOpen
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.residue_model_at_prime : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], HasConstants ℤ A y → ∀ (p : ℕ) [Fact p.Prime] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], (p : A) ∈ m → ∀ fd : ℕ, Nat.card (A ⧸ m) = p ^ fd → ∀ W' : Ideal (MRing ι O), W'.IsPrime → IsMultiHomogIdeal W' → pointIdeal O y ≤ W' → (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W' → ∀ l : List (K → ℤ), intNumL (ZMod p) (extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O)))) l = (fd : ℤ) * vNumL W' l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.intNumL_zmod_eq_residueDegree_mul_vNumL | exact GlobalTheory.CompanionTheory.Ar.Num.intNumL_zmod_eq_residueDegree_mul_vNumL | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.intNumL_zmod_eq_residueDegree_mul_vNumL <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.tower_symmetry_limit_compat : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : GlobalTheory.CompanionTheory.Ar.Top.RootTower Ψ N) (II : IntersectionSystem) (Γ : Subgroup (Equiv.Perm Ψ)), T.Conv II → (∀ τ τ' : Ψ, ∃ s ∈ Γ, s τ = τ') → (∀ s ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∃ π : Equiv.Perm T.Comp, ∀ (c : T.Comp) (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N), Tendsto (fun t => II _ _ (T.M B c).P _ (fun j => (T.M B c).x t (s (w j).1, (w j).2)) / (T.M B c).δ - II _ _ (T.M B (π c)).P _ (fun j => (T.M B (π c)).x t (w j)) / (T.M B (π c)).δ) (𝓝[>] 0) (𝓝 0)) → IsIntersectionSystem II → T.PropA II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.PermInv.propA_of_limits | exact GlobalTheory.CompanionTheory.Ar.Top.PermInv.propA_of_limits | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.PermInv.propA_of_limits <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.continuous_wall_bound_extend : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | exact GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.perturbed_weight_gap_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound | exact GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.remainder_term_summable : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | exact GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.lie_term_flag_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | exact GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.mean_slope_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | exact GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.tower_height_identity_expansion : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm | exact GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.identOnDecomposedForm <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem val_psumExpansion_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] [DecidableEq σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (r k : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) = ∑ μ ∈ G.support, G.coeff μ * (((T.comp e).ck P k (classList (Sum.elim T.x T.x') μ) : ℤ) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ _ _ T P r k e G
  have hcomp : (Sum.elim T.x T.x') ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
    funext s
    cases s <;> rfl
  have hfin : ∀ f g : MRing ι O, (Function.support (ratDiv P f g)).Finite := fun f g =>
    ratDiv_support_finite DivCycleFiniteSupport.full P f g
  have hterm : ∀ (i : σ) (L : List (K → ℤ)),
      cycNum (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x')
        (∑ a ∈ Finset.univ.filter (fun a => e a = i),
          rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) L =
      ∑ a ∈ Finset.univ.filter (fun a => e a = i),
        ((cycEval (fun W => classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k a) L W)
          (ratDiv P (T.f (e a)) (T.g (e a))) : ℤ) : ℝ) := by
    intro i L
    rw [(GlobalTheory.T.cycle_number_linear O K ι (σ ⊕ σ) (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') L).2.2.1]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain rfl : e a = i := (Finset.mem_filter.mp ha).2
    rw [GlobalTheory.T.cycle_number_rename.1 O K ι (Fin r ⊕ Fin r) (σ ⊕ σ) (Sum.map e e) _ (Sum.elim T.x T.x') _ L, hcomp]
    exact (cycNum_int_and_comb O K ι (Fin r ⊕ Fin r) (Sum.elim (T.x ∘ e) (T.x' ∘ e)) L).1 _
      (hfin _ _) _
  have hck : ∀ L : List (K → ℤ), (((T.comp e).ck P k L : ℤ) : ℝ) =
      ∑ i, ∑ a ∈ Finset.univ.filter (fun a => e a = i),
        ((cycEval (fun W => classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k a) L W)
          (ratDiv P (T.f (e a)) (T.g (e a))) : ℤ) : ℝ) := by
    intro L
    rw [Finset.sum_fiberwise]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, Int.cast_sum]
  unfold LocPair.val
  simp only [GlobalTheory.T.cycle_number_mul_expand O K ι (σ ⊕ σ), List.append_nil, hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.mul_sum, hck]

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.tower_theorem_B : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | exact GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmB_functional <;> assumption)
end
