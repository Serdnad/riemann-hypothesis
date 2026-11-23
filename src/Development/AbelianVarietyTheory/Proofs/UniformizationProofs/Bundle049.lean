module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SecCyclic
open GlobalTheory.AbLaw.Seesaw

theorem coker_equiv {R : Type} [CommRing R] {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v₀ : Fin a → R)
    (k : Fin a) (hk : IsUnit (v₀ k))
    (hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀)) :
    Nonempty (((Fin a → R) ⧸ LinearMap.range D.transpose.mulVecLin) ≃ₗ[R]
      (R ⧸ Ideal.span (Set.range (D.mulVec v₀)))) := by
  classical
  set N := LinearMap.range D.transpose.mulVecLin with hN
  set I := Ideal.span (Set.range (D.mulVec v₀)) with hI
  have hrow : ∀ i, ∑ j, D i j • N.mkQ (Pi.single j 1) = 0 := fun i => by

    simp only [← map_smul, ← map_sum]
    refine (Submodule.Quotient.mk_eq_zero N).2 ⟨Pi.single i 1, ?_⟩
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  obtain ⟨c, hc⟩ := hker (TrivSqZeroExt R ((Fin a → R) ⧸ N)) (TrivSqZeroExt.inlHom R ((Fin a → R) ⧸ N))
    (fun j => TrivSqZeroExt.inr (N.mkQ (Pi.single j 1))) (by
      funext i
      change ∑ j, TrivSqZeroExt.inl (D i j) * TrivSqZeroExt.inr (N.mkQ (Pi.single j 1)) = (0 : TrivSqZeroExt R ((Fin a → R) ⧸ N))
      have := congrArg (TrivSqZeroExt.inrHom R ((Fin a → R) ⧸ N)) (hrow i)

      rw [map_sum, map_zero] at this
      exact (Finset.sum_congr rfl fun j _ => TrivSqZeroExt.inl_mul_inr _ _).trans this)
  have he : ∀ j, N.mkQ (Pi.single j 1) = v₀ j • c.snd := fun j => by
    have := congrArg TrivSqZeroExt.snd (congrFun hc j)
    change _ = (c * TrivSqZeroExt.inl (v₀ j)).snd at this
    rw [_root_.mul_comm, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul] at this
    exact this
  have hx : ∀ x : Fin a → R, N.mkQ x = (x ⬝ᵥ v₀) • c.snd := fun x => by
    have : x = ∑ j, x j • (Pi.single j 1 : Fin a → R) := by
      funext j
      simp [Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [this]

    simp only [map_sum, map_smul, he, smul_smul, dotProduct, Finset.sum_smul]
  have hIq : ∀ r ∈ I, r • c.snd = 0 := fun r hr => by
    refine Submodule.span_induction (p := fun r _ => r • c.snd = 0) ?_ (zero_smul _ _) ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      rw [← hrow i]
      simp only [he, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    · intro x y _ _ h₁ h₂
      rw [add_smul, h₁, h₂, add_zero]
    · intro s x _ h
      rw [smul_eq_mul, mul_smul, h, smul_zero]
  let φ : (Fin a → R) →ₗ[R] R ⧸ I := I.mkQ ∘ₗ (dotProductBilin R R).flip v₀
  have hφ : ∀ x, φ x = I.mkQ (x ⬝ᵥ v₀) := fun _ => rfl
  have hs : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := I.mkQ_surjective y
    obtain ⟨u, hu⟩ := hk
    refine ⟨Pi.single k (r * u⁻¹.val), ?_⟩
    rw [hφ, single_dotProduct, ← hu, Units.inv_mul_cancel_right]
  have hk' : N = LinearMap.ker φ := by
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
    · intro h
      exact (Submodule.Quotient.mk_eq_zero N).1 ((hx x).trans (hIq _ h))
  exact ⟨(Submodule.quotEquivOfEq _ _ hk').trans (φ.quotKerEquivOfSurjective hs)⟩

theorem cyclic_ideal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → ∀ P : Perf f M, UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K), IsLocalHom g₀ → ∀ (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ I : Ideal R, Nonempty (((Fin P.a → R) ⧸ LinearMap.range P.D₀.transpose.mulVecLin) ≃ₗ[R] (R ⧸ I)) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ X f M hM P hcl hsurj K _ g₀ hloc X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  have unit_of : ∀ r : R, g₀ r ≠ 0 → IsUnit r := fun r hr => hloc.map_nonunit r hr.isUnit
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker₀⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  have hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) :=
    fun R' _ g => hker₀ R' g ((unit_of δ hδ).map g)
  obtain ⟨c₀, hc₀⟩ := hker K g₀ v hv
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : IsUnit (v₀ k) := unit_of _ fun h0 => hk (by
    rw [hc₀]
    change c₀ * g₀ (v₀ k) = 0
    rw [h0, mul_zero])
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    have h₁ := hu i
    rw [hc₀, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : IsUnit r₁ := unit_of r₁ hr₁
  refine ⟨Ideal.span (Set.range (P.D₀.mulVec v₀)), coker_equiv P.D₀ v₀ k hk' hker,
    fun R' _ g X' π f' h => ?_⟩
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      change r₁ ∉ (f (π y)).asIdeal
      exact fun hm => (f (π y)).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hr₁')
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.UU.SecCyclic
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineCover

theorem exists_cover_of_isProjBy_of_infinite (K : Type) [Field K] [Infinite K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (hp : IsProjBy f) :
    ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨H, hH, m, s, hc, hs⟩ := hp
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := ⟨by
    have e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hc]
      rfl
    rw [e]
    exact isCompact_iUnion fun i => (hs i).1.isCompact⟩
  have : IsNoetherian X := ⟨⟩
  obtain ⟨D, hD, h⟩ := exists_affine_le_coheight (X := X) (fun F hF =>
    exists_isAffineOpen_of_finite (cst f ⊤) hH s hc (fun i => (hs i).1) F hF) (g + 1)
  refine ⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩
  have := (h x hx).trans (coheight_le_of_smooth f hf x)
  exact Nat.not_succ_le_self _ (by exact_mod_cast this)

theorem exists_cover_of_isProjBy :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → IsProjBy f → ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ :=
  fun K _ _ X _ f g hf hp => exists_cover_of_isProjBy_of_infinite K X f g hf hp

end GlobalTheory.AffineCover
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AmpleStabFinite
open GlobalTheory.CechPic

theorem eq_pull_of_local {Y S : Scheme.{0}} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom) (c : CechPic.Pic Y)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ CechPic.pull (p ⁻¹ᵁ U).ι c = 0) : c = CechPic.pull (p ≫ e) c := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have key := exists_gen_of_local_on_base hM (K := Fin 2) ![𝟙 Y, p ≫ e] ![1, -1] p e he hp
    (fun U _ k => by
      rw [Fin.prod_univ_two]
      show k (e ≫ 𝟙 Y) ^ (1 : ℤ) * k (e ≫ p ≫ e) ^ (-1 : ℤ) = 1
      rw [← Category.assoc e, he, Category.comp_id, Category.id_comp]; simp)
    (fun s => by
      obtain ⟨U, hs, hU⟩ := h s
      refine ⟨U, hs, (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_⟩
      obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
          n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
        ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          have e' := congrArg (fun q => q (p y.1)) he
          exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
      rw [cls_linComb hM, Fin.sum_univ_two]
      show (1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ 𝟙 Y) (cls M hM) +
        (-1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (cls M hM) = 0
      rw [← n₁, Category.comp_id, pull_comp, hU, map_zero]; simp)
  have k2 := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 key
  rw [cls_linComb hM, Fin.sum_univ_two] at k2
  have k3 : (1 : ℤ) • CechPic.pull (𝟙 Y) (cls M hM) + (-1 : ℤ) • CechPic.pull (p ≫ e) (cls M hM) = 0 := k2
  rw [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at k3
  exact k3

theorem surj_of_isPullback (hG : GlobalFnsSt) {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B)
    {Y T : Scheme.{0}} {a : Y ⟶ B.left} {q : Y ⟶ T} {b : T ⟶ S} (h : IsPullback a q B.hom b) :
    Function.Surjective q.appTop.hom := by
  rw [← h.isoPullback_hom_snd]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)).2 (surj_snd hG hB (Over.mk b))

theorem cls_pw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d : ℤ) : cls (pw L d) (isLB_pw hL d) = d • cls L hL := by
  have h := LB.isLB_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => d)
  have e := cls_linComb hL _ _ h
  rw [Fintype.sum_unique, pull_id] at e
  rw [← e]
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun i _ => i, fun _ _ hy => Set.mem_iInter.2 fun _ => hy, ?_⟩)
  intro y i j hi hj
  refine Eq.trans (map_zpow _ _ _) (Eq.symm ((gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => d) (𝟙 X) y (fun _ => i) (fun _ => j)
    (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans ?_))
  rw [Fintype.prod_unique, Category.id_comp]
  rfl

theorem pull_spec_local {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (y : Spec (CommRingCat.of K) ⟶ X)
    (c : CechPic.Pic X) : CechPic.pull y c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff (pull_isLB hM y)).2 (DVR.exists_gen_of_local M hM _ _)

theorem isAffine_of_quasiAffine {X S : Scheme.{0}} [IsAffine S] [X.IsQuasiAffine] (f : X ⟶ S) [UniversallyClosed f] :
    IsAffine X := by
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Surjective X.toSpecΓ := inferInstance
  exact ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (top_unique fun x _ => X.toSpecΓ.surjective x)⟩

theorem quasiAffine_of_pull_add {X Y : Scheme.{0}} [CompactSpace X] (f g : X ⟶ Y) [IsAffineHom f] {M : LB Y}
    (hM : M.IsLB) {I : Type} (s : I → M.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (h : CechPic.pull f (cls M hM) + CechPic.pull g (cls M hM) = 0) : X.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (f x)))
  obtain ⟨b, hxb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g x)))
  have hN := LB.isLB_linComb hM (Sum.elim (fun _ : PUnit => g) (fun _ : PUnit => f))
    (Sum.elim (fun _ => 1) (fun _ => 1))
  have h0 : cls _ hN = 0 := by
    rw [cls_linComb hM, Fintype.sum_sum_type]
    simpa [add_comm] using h
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_triv X) hN
    ((cls_eq_iff _ _).1 h0.symm)
    (DVR.mulSec M _ _ _ _ (secPull (s b) g) (secPull (s a) f))
  rw [nonzeroLocus_mulSec, nonzeroLocus_secPull (s a)] at ht
  have e : nonzeroLocus t = X.basicOpen (show Γ(X, ⊤) from t.f PUnit.unit) :=
    le_antisymm (iSup_le fun _ => le_rfl) (basicOpen_le_nonzeroLocus t PUnit.unit)
  refine ⟨t.f PUnit.unit, ?_, ?_⟩
  · rw [← e, ht]
    exact isAffineOpen_nonzeroLocus_inf (pull_isLB hM g) _ ((ha a).preimage f)
  · rw [← e, ht, nonzeroLocus_secPull]
    exact ⟨hxb, hxa⟩

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem transl_const (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) (b : T ⟶ B) :
    CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) =
      CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ B).left (cls L hL) -
        CechPic.pull (1 : T ⟶ B).left (cls O hO) := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  have val : ∀ b : T ⟶ B, CechPic.pull (lift (𝟙 T) b).left (cls _ hM) =
      CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) := by
    intro b
    have e₁ : cls _ h₁ = CechPic.pull (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left (cls L hL) -
        CechPic.pull (snd T B).left (cls L hL) := by
      refine (cls_linComb hL _ _ h₁).trans ?_
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
    have a₁ : lift (𝟙 T) b ≫ (lift (fst T B ≫ x) (snd T B) ≫ μ[B]) = x * b := by
      rw [comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]; rfl
    rw [cls_div h₁ h₂, e₁, cls_pull hO, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp,
      ← Over.comp_left, ← Over.comp_left, a₁, lift_snd]
  have sec : ∀ b : T ⟶ B, (lift (𝟙 T) b).left ≫ (fst T B).left = 𝟙 _ := fun b => by
    rw [← Over.comp_left, lift_fst]; rfl
  have key := eq_pull_of_local (fst T B).left (lift (𝟙 T) (1 : T ⟶ B)).left (sec 1)
    (fun V => surj_of_isPullback hG hB
      ((IsPullback.of_hasPullback (fst T B).left V.ι).paste_horiz
        (IsPullback.of_hasPullback T.hom B.hom).flip)) (cls _ hM)
    (fun p => by
      obtain ⟨U, hU, ht⟩ := h p
      exact ⟨U, hU, (cls_eq_zero_iff (pull_isLB hM _)).2 ht⟩)
  have k := congrArg (CechPic.pull (lift (𝟙 T) b).left) key
  rw [← pull_comp, ← Category.assoc, sec, Category.id_comp, val, val, _root_.mul_one] at k
  exact k

theorem add_inv_eq [IsCommMonObj B] (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    CechPic.pull x.left (cls L hL) + CechPic.pull (x⁻¹).left (cls L hL) =
      CechPic.pull y.left (cls L hL) + CechPic.pull (y⁻¹).left (cls L hL) := by
  have a := transl_const hG hB hL hO x hx (x⁻¹ * y⁻¹)
  have b := transl_const hG hB hL hO y hy (x⁻¹ * y⁻¹)
  rw [mul_inv_cancel_left] at a
  rw [mul_comm x⁻¹ y⁻¹, mul_inv_cancel_left, mul_comm y⁻¹ x⁻¹] at b
  linear_combination (norm := abel) b - a

end Points

theorem isFinite_of_relAmple : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ L O : LB B.left, L.IsLB → O.IsLB → RelAmple B L → ∀ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom := by
  intro hG R _ B _ _ hB L O hL hO hA H j hj hH
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  have := hB.proper
  have : IsProper H.hom := by rw [← Over.w j]; infer_instance
  suffices LocallyQuasiFinite H.hom from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (H.hom ⁻¹' {z}) with h0 | ⟨h, hh⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField h
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField h
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (y₀ ≫ H.hom)
  let y : P ⟶ H := Over.homMk y₀ rfl
  let π : (H ⊗ P).left ⟶ H.left := (fst H P).left
  let q : (H ⊗ P).left ⟶ Spec (CommRingCat.of K) := (snd H P).left
  have hpb : IsPullback π q H.hom (y₀ ≫ H.hom) := IsPullback.of_hasPullback H.hom P.hom
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  have key := add_inv_eq hG hB hL hO (fst H P ≫ j) (snd H P ≫ y ≫ j) ((hH _ _).2 ⟨_, rfl⟩)
    ((hH _ _).2 ⟨snd H P ≫ y, Category.assoc _ _ _⟩)
  rw [← GrpObj.comp_inv (snd H P), Over.comp_left _ _ _ (snd H P), Over.comp_left _ _ _ (snd H P), pull_comp (snd H P).left,
    pull_comp (snd H P).left, pull_spec_local (K := K) (y ≫ j).left, pull_spec_local (K := K) (y ≫ j)⁻¹.left,
    map_zero, add_zero] at key
  have : CompactSpace (H ⊗ P).left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (fst H P ≫ j).left := inferInstanceAs (IsAffineHom (π ≫ j.left))
  have : (H ⊗ P).left.IsQuasiAffine := quasiAffine_of_pull_add (fst H P ≫ j).left ((fst H P ≫ j)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add, key, zsmul_zero])
  have : IsAffine (H ⊗ P).left := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set (H ⊗ P).left).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun w hw => ?_
  have e : H.hom w = (y₀ ≫ H.hom) (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = h := Scheme.fromSpecResidueField_apply h _
    exact (show H.hom w = z from hw).trans ((show H.hom h = z from hh).symm.trans (congrArg H.hom e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := y₀ ≫ H.hom) w _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.AmpleStabFinite
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_fam_of_expBij : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → U.ExpBij k → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g := by
  intro hBC R _ _ I hadm D A G _ _ _ U k hk hbij
  obtain ⟨b, hex, huniq⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hBC R I D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin := fun c s hs => GlobalTheory.expands_linear R I hadm D A G U k (k ^ A.g) b F c s hF hs
  let φ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hφ : ∀ c, φ c = ∑ i, c i • F i := fun c => rfl
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 := hlin c s hs
    have h2 := hlin c' s' hs'
    rw [← hφ] at h1 h2
    rw [← h] at h2
    have e : s = s' := (hbij.2 (φ c)).unique h1 h2
    subst e
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.qkToAkU_of_integral_torsion_point : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (k : ℕ), 1 ≤ k → ∀ (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt D.toPre F k) (xF : TFK (R := R) F ⟶ A.A), p.y = 0 → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g → xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) F) ≫ x).left → QkToAkU U.toUnifPre F k p xF := by
  first | exact @GlobalTheory.qkToAkU_of_integral_torsion | exact GlobalTheory.qkToAkU_of_integral_torsion | (intros; apply GlobalTheory.qkToAkU_of_integral_torsion <;> assumption)
end
