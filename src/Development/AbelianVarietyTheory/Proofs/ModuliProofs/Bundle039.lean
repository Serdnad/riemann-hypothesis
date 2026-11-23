module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.LocalCoord

theorem appLE_resG {X Y : Scheme.{0}} (x : Y ⟶ X) {U U' : X.Opens} (hU : U' ≤ U) {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U')
    (a : Γ(X, U)) : (x.appLE U' V h).hom (resG X hU a) = (x.appLE U V (h.trans (x.preimage_mono hU))).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem resG_appLE {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem res_val_lemma {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := by
  rfl

private theorem res_pullU_val_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : ((res h (pullU f W u) : Γ(Y, V)ˣ) : Γ(Y, V)) = (f.appLE W V h).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_U_le_preimage_U {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) (k : PUnit) :
    (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j k) := by
  intro y hy
  have hy' : y ∈ ⋂ k, f ⁻¹' (M.U (j k) : Set X) := hy
  exact Set.mem_iInter.1 hy' k

private theorem resG_app_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)) : resG Y h ((f.app W).hom u) = (f.appLE W V h).hom u := by
  rfl

private theorem pullU_val_eq_app {X Y : Scheme.{0}} (f : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    ((pullU f W u : Γ(Y, f ⁻¹ᵁ W)ˣ) : Γ(Y, f ⁻¹ᵁ W)) = (f.app W).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_g_lemma_6 {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull f).g j j' : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ) : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')) =
      (f.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp only [Fintype.prod_unique, zpow_one]
  rfl

private theorem resG_eq_presheaf_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG X h a = (X.presheaf.map (homOfLE h).op).hom a := by
  rfl

theorem exists_secCoord_of_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) {I : Type} (th : I → M.Sec)
    {R : Type} [CommRing R] (x : Sp R ⟶ X) (j₀ : M.ι) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U j₀) : ∃ v, SecCoord M th x v := by
  have hV : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U j₀) := by
    intro j y hy
    exact ⟨pull_U_le_preimage_U M x j PUnit.unit hy, h₀ trivial⟩
  let τ : (M.pull x).Gen := ⟨fun j => res (hV j) (pullU x _ (M.g (j PUnit.unit) j₀))⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE (M.U j₀) ⊤ h₀).hom ((th i).f j₀)), τ, ?_, ?_⟩
  · intro j j'
    apply Units.ext
    have hc := congrArg Units.val (hM.cocycle (j PUnit.unit) (j' PUnit.unit) j₀)
    simp only [Units.val_mul, res_val_lemma] at hc
    have hT : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) ⊓ M.U j₀) := by
      intro y hy
      exact ⟨⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩, h₀ trivial⟩
    have hc' := congrArg (x.appLE _ _ hT).hom hc
    rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at hc'
    have hjj : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) := by
      intro y hy
      exact ⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩
    simp only [τ, Units.val_mul, res_val_lemma, pullU_val_eq_app, resG_app_eq_appLE, resG_appLE, pull_g_lemma_6 M x j j' hjj]
    exact hc'.symm
  · intro i j h
    have hf := (th i).compat (j PUnit.unit) j₀
    simp only [τ, res_pullU_val_eq_appLE]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, resG_appLE,
      ← appLE_resG x (inf_le_left : M.U (j PUnit.unit) ⊓ M.U j₀ ≤ _) (hV j), resG_eq_presheaf_map, hf, map_mul,
      ← resG_eq_presheaf_map, appLE_resG, mul_comm]

theorem exists_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) (p : X) : ∃ j, p ∈ M.U j := by
  have hp : p ∈ (⨆ i, M.U i) := by
    rw [hM.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hp

theorem secCoord_local : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  intro X M I th hM
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _ x
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x (IsLocalRing.closedPoint R))
    refine exists_secCoord_of_chart M hM th x j₀ ?_
    intro y _
    exact (IsLocalRing.specializes_closedPoint (R := R) y).mem_open (x ⁻¹ᵁ M.U j₀).isOpen hj
  · intro R _ x p
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x p)
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := (p : PrimeSpectrum R)) hj
        (x ⁻¹ᵁ M.U j₀).isOpen
    refine ⟨f, hpf, exists_secCoord_of_chart M hM th _ j₀ ?_⟩
    intro y _
    have hy : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (show PrimeSpectrum (Localization.Away f) from y) ∈
        ((PrimeSpectrum.basicOpen (f : R) : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) (f : R)]
      exact ⟨_, rfl⟩
    exact hsub hy
  · intro p
    obtain ⟨j₀, hj⟩ := exists_chart M hM p
    obtain ⟨V, hV, hpV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hj
    have hV' : IsAffineOpen V := hV
    obtain ⟨v, hv⟩ := exists_secCoord_of_chart M hM th (R := Γ(X, V)) hV'.fromSpec j₀ (by
      intro y _
      apply hVU
      have h1 : hV'.fromSpec y ∈ Set.range hV'.fromSpec := ⟨y, rfl⟩
      rw [hV'.range_fromSpec] at h1
      exact h1)
    refine ⟨Γ(X, V), inferInstance, hV'.fromSpec, v, inferInstance, ?_, hv⟩
    rw [hV'.range_fromSpec]
    exact hpV

end GlobalTheory.ZM.LocalCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

theorem exists_desc_of_isFinite_of_densePart : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ThickeningIso

theorem bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp

theorem ker_appTop {A C : CommRingCat.{0}} {β : A ⟶ C} (hβ : Function.Surjective β) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Y] :
    RingHom.ker i.appTop.hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (isAffineOpen_top _))
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop
      ((Scheme.ΓSpecIso C).inv ≫ f'.appTop) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · rw [← Scheme.ΓSpecIso_naturality]
      congr 1
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem surjective_fst (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

theorem isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by
  have hs := surjective_fst K
  have h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have h2 : IsClosedImmersion (j ≫ e) := MorphismProperty.of_isPullback h'.flip h1
  have hY : IsAffine Y := isAffine_of_isAffineHom (j ≫ e)
  have hY' : IsAffine Y' := by
    refine AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
      (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']
    exact this
  suffices hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e
  rw [ConcreteCategory.isIso_iff_bijective]
  have k := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h
  have k' := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'
  have hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)
  have hsur : Function.Surjective (j ≫ e).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2
  rw [Scheme.Hom.comp_appTop] at k k' hfl hsur
  exact bijective_of_mod_eps
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom
    hfl hsur k' k

theorem isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance

end GlobalTheory.ThickeningIso
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

theorem exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩

theorem exists_linearEquiv_of_holUnif (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp

end GlobalTheory.LatticeHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem hom_ext_of_geometric_points (S X Z : Scheme.{0}) [IsReduced S] (q : X ⟶ Z)
    [IsSeparated q] (f g : S ⟶ X) (hq : f ≫ q = g ≫ q)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), x ≫ f = x ≫ g) : f = g := by
  have hs : Surjective (equalizer.ι f g) := ⟨fun s => by
    let k := AlgebraicClosure (S.residueField s)
    let x : Sp k ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) ≫ S.fromSpecResidueField s
    have hx := h k x
    let p : Sp k := IsLocalRing.closedPoint k
    refine ⟨equalizer.lift x hx p, ?_⟩
    rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _⟩
  exact ext_of_isDominant_of_isSeparated q hq (equalizer.ι f g) (equalizer.condition _ _)

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_eq_mul_of_valAt'_eq_continuous_mul : ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  first | exact @GlobalTheory.exists_eq_mul_of_continuousOn_quotient | exact GlobalTheory.exists_eq_mul_of_continuousOn_quotient | (intros; apply GlobalTheory.exists_eq_mul_of_continuousOn_quotient <;> assumption)
end
