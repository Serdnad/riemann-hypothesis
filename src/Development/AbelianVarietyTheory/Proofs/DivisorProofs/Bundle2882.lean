module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.LbChain

theorem lbIso_chain : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  intro A₀ X₁ G₁ G₂ Z P Q LA L₁ L₂ LZ LQ a a' f₁ f₂ f₃ ψ π t hA h₁ h₂ hZ hQ hs e₁ e₂ e₃ e₄ ht
  have E0 : LBIso LA (LA.pull (a' ≫ a)) :=
    LBIso.chartPull (chartPullUnpull LA (a' ≫ a) hs) (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hA _))
  have E1 : LBIso (LA.pull (a' ≫ a)) (L₁.pull (a' ≫ f₁)) := GlobalTheory.GenSpread.lbIso_pull_comp a' rfl rfl e₁
  have E2 : LBIso (L₁.pull (a' ≫ f₁)) (L₂.pull (a' ≫ f₁ ≫ f₂)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₂ (a' ≫ f₁) (by simp)
  have E3 : LBIso (L₂.pull (a' ≫ f₁ ≫ f₂)) (LZ.pull (t ≫ ψ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₃ (a' ≫ f₁ ≫ f₂) (by rw [ht]; simp)
  have E4 : LBIso (LZ.pull (t ≫ ψ)) (LQ.pull (t ≫ π)) := GlobalTheory.GenSpread.lbIso_pull_comp t rfl rfl e₄
  exact LBIso.trans hA (pull_isLB hA _) (pull_isLB hQ _) E0
    (LBIso.trans (pull_isLB hA _) (pull_isLB h₁ _) (pull_isLB hQ _) E1
      (LBIso.trans (pull_isLB h₁ _) (pull_isLB h₂ _) (pull_isLB hQ _) E2
        (LBIso.trans (pull_isLB h₂ _) (pull_isLB hZ _) (pull_isLB hQ _) E3 E4)))

end GlobalTheory.LbChain
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SpreadPolAV

theorem exists_spread : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  classical
  intro F Ω _ _ em A I _ y
  obtain ⟨R, P₀, φ₀, ftR, -, H₀, iso₀⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring Ω A
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have := P₀.smoothDim
  have : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  have : LocallyOfFinitePresentation P₀.A.hom := inferInstance

  have hx : ∀ i, ((y i).left ≫ φ₀) ≫ P₀.A.hom = spMap (algebraMap R Ω) := by
    intro i
    rw [Category.assoc, H₀.1.w, ← Category.assoc, Over.w (y i)]
    exact Category.id_comp _
  obtain ⟨R', y', hR', -, hy'⟩ :=
    GlobalTheory.Spread.exists_fg_points P₀.A.hom (fun i => (y i).left ≫ φ₀) hx ⊥ Subalgebra.fg_bot
  have ftR' : Algebra.FiniteType ℤ R' :=
    Algebra.FiniteType.trans ftR ((Subalgebra.fg_iff_finiteType R').1 hR')
  obtain ⟨s₀, hs₀⟩ := ftR'.out

  letI : Algebra F Ω := em.toAlgebra
  let f₀ : R' →ₐ[ℤ] Ω := R'.val.restrictScalars ℤ
  let T : Subalgebra F Ω := Algebra.adjoin F (f₀ '' (s₀ : Set R'))
  have hTfg : T.FG := ⟨s₀.image f₀, by rw [Finset.coe_image]⟩
  have hR'T : ∀ z ∈ R', z ∈ T := by
    intro z hz
    have h₁ : (⟨z, hz⟩ : R') ∈ Algebra.adjoin ℤ (s₀ : Set R') := by rw [hs₀]; trivial
    have h₂ : f₀ ⟨z, hz⟩ ∈ Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.2 ⟨_, h₁, rfl⟩
    have key : Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) ≤ T.restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := F))
    exact key h₂
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => hR'T r (R'.algebraMap_mem (⟨r, hr⟩ : R))
  let g : R →+* T := R.subtype.codRestrict T fun r => hRT r r.2
  let incl : R' →+* T := R'.val.toRingHom.codRestrict T fun z => hR'T z z.2
  let jT : T →+* Ω := T.val.toRingHom
  have e₁ : spMap jT ≫ spMap g = spMap R.subtype := by
    rw [← Spec.map_comp]; rfl
  have e₂ : spMap jT ≫ spMap incl = spMap R'.val.toRingHom := by
    rw [← Spec.map_comp]; rfl
  have e₃ : spMap incl ≫ spMap (algebraMap R R') = spMap g := by
    rw [← Spec.map_comp]; rfl

  let P : PolAV (Sp T) := GlobalTheory.AmpleSymModel.polPull P₀ (spMap g)
  have Gp : IsGrpPullback P.A P₀.A (spMap g) (pullback.fst P₀.A.hom (spMap g)) :=
    isGrpPullback_pullback P₀.A (spMap g)
  have w : φ₀ ≫ P₀.A.hom = (A.A.hom ≫ spMap jT) ≫ spMap g := by
    rw [Category.assoc, e₁]; exact H₀.1.w
  let φ : A.A.left ⟶ P.A.left := Gp.1.lift _ _ w
  have hφ : φ ≫ pullback.fst P₀.A.hom (spMap g) = φ₀ := Gp.1.lift_fst _ _ w
  have hφ' : φ ≫ P.A.hom = A.A.hom ≫ spMap jT := Gp.1.lift_snd _ _ w
  have hu : ∀ i, (spMap incl ≫ y' i) ≫ P₀.A.hom = 𝟙 (Sp T) ≫ spMap g := by
    intro i
    rw [Category.assoc, (hy' i).1, e₃, Category.id_comp]
  let y₀ : I → (baseOver (Sp T) ⟶ P.A) := fun i =>
    Over.homMk (Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i)) (Gp.1.lift_snd _ _ (hu i))
  refine ⟨T, inferInstance, inferInstance, inferInstance, jT, P, φ, y₀,
    (Subalgebra.fg_iff_finiteType T).1 hTfg, Subtype.val_injective, RingHom.ext fun _ => rfl,
    Gp.cancel (H₀.congr e₁.symm hφ.symm) hφ',
    GlobalTheory.KeyTf.lbIso_pull_pull_of_comp A.isLB P₀.isLB hφ iso₀, fun i => ?_⟩
  apply Gp.1.hom_ext
  · change (y i).left ≫ φ ≫ pullback.fst P₀.A.hom (spMap g) =
      spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ pullback.fst P₀.A.hom (spMap g)
    rw [hφ, Gp.1.lift_fst, ← Category.assoc, e₂, (hy' i).2]
  · change (y i).left ≫ φ ≫ P.A.hom = spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ P.A.hom
    rw [hφ', Gp.1.lift_snd, ← Category.assoc, Over.w (y i)]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
end GlobalTheory.SpreadPolAV
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory

namespace GenericBundleDescent

variable {X X' Y Z : Scheme.{0}}

theorem pull_both {M : LB X} {N : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'} (H : LBIso (M.pull a) (N.pull b)) (h : Z ⟶ Y)
    {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = h ≫ a) (eb : b' = h ≫ b) : LBIso (M.pull a') (N.pull b') :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => ea) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_right {M : LB Y} {N : LB X'} {b : Y ⟶ X'} (H : LBIso M (N.pull b)) (h : Z ⟶ Y)
    {b' : Z ⟶ X'} (eb : b' = h ≫ b) : LBIso (M.pull h) (N.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M h h rfl) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_pull {M : LB X} {N : LB Z} {a : Y ⟶ X} {h : Z ⟶ Y} (H : LBIso (M.pull (h ≫ a)) N) :
    LBIso ((M.pull a).pull h) N :=
  LBIso.chartPull (chartPullLinComb M a (fun _ : PUnit => h) (fun _ => h ≫ a) (fun _ => 1) (𝟙 Z)
    fun _ => (Category.id_comp _).symm) (chartPullId N) H

theorem mono_jK (R : Type) [CommRing R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GenericBundleDescent


open GenericBundleDescent in
theorem unif_bundle_generic_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R W R₂ W₂ K' Ω' _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ρ σ φ₂ io j l i j₂ _ _ _ _ _ _ _ hj₂σ hj₂φ G _ _ A gen GW _ _ βW DW
    AW UW α _ hα A₁ α₁ p hA₁ hp₁ hp₂ hLp G₂ _ _ β A₂ gen₂ q _ hq hLq hgq GW' _ _ βW' τ DW' AW' UW' κ hβW' hτ hsq hκ hL
  have := mono_jK R
  have := mono_jK R₂
  let π := pullback.fst (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  let s := pullback.snd (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  have hπ : π ≫ pullback.fst GW'.hom (jK W₂) ≫ GW'.hom = s ≫ spMap j₂ ≫ jK W₂ := by
    rw [pullback.condition, pullback.condition_assoc]
  have e₁ : spMap j₂ ≫ jK W₂ ≫ spMap σ = spMap j ≫ jK W := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂σ)
  have e₂ : spMap j₂ ≫ jK W₂ ≫ spMap φ₂ = spMap (l.comp i.symm.toRingHom) ≫ jK R₂ := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂φ)
  have e₃ : spMap (l.comp i.symm.toRingHom) ≫ spMap i.toRingHom = spMap l := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun x => by simp)
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : _ ⟶ pullback GW.hom (jK W),
      ℓ ≫ pullback.fst _ _ = π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ ∧ ℓ ≫ pullback.snd _ _ = s ≫ spMap j :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, hτ.1.w, reassoc_of% hπ, e₁, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have wW : UW.gen.hom.left ≫ AW.A.hom = pullback.snd GW.hom (jK W) := Over.w UW.gen.hom
  have w₂ : gen₂.hom.left ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := Over.w gen₂.hom
  let gW : pullback GW.hom (jK W) ⟶ AW.A.left := UW.gen.hom.left
  let g₂ : pullback G₂.hom (jK R₂) ⟶ A₂.A.left := gen₂.hom.left
  let gi : A.A.left ⟶ pullback G.hom (jK R) := gen.inv.left
  have wW' : gW ≫ AW.A.hom = pullback.snd GW.hom (jK W) := wW
  have w₂' : g₂ ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := w₂
  have hα' : gW ≫ α ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := by
    have c : UW.gen.hom.left ≫ UW.gen.inv.left = 𝟙 _ := congrArg Over.Hom.left UW.gen.hom_inv_id
    exact (congrArg (UW.gen.hom.left ≫ ·) hα.symm).trans (by rw [reassoc_of% c])
  have hgq' : g₂ ≫ q ≫ α₁ ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst G₂.hom (jK R₂) ≫ β := by
    have c : gen₂.hom.left ≫ gen₂.inv.left = 𝟙 _ := congrArg Over.Hom.left gen₂.hom_inv_id
    exact (congrArg (gen₂.hom.left ≫ ·) hgq.symm).trans (by rw [reassoc_of% c])
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : _ ⟶ pullback AW.A.hom (spMap j),
      n ≫ pullback.fst _ _ = ℓ ≫ gW ∧ n ≫ pullback.snd _ _ = s :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, wW', hℓ₂]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsIso gi := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
  have hm : n ≫ p = π ≫ κ ≫ g₂ ≫ q := by
    refine hA₁.1.hom_ext ?_ ?_
    · rw [← cancel_mono gi, ← cancel_mono (pullback.fst G.hom (jK R))]
      simp only [Category.assoc]
      rw [reassoc_of% hp₁, reassoc_of% hn₁, hα', reassoc_of% hℓ₁, hgq', reassoc_of% hκ, hsq]
    · have k : π ≫ κ ≫ pullback.snd G₂.hom (jK R₂) = s ≫ spMap (l.comp i.symm.toRingHom) := by
        rw [← cancel_mono (jK R₂)]
        simp only [Category.assoc]
        rw [← pullback.condition, reassoc_of% hκ, hβW'.1.w, reassoc_of% hπ, e₂]
      simp only [Category.assoc]
      rw [hp₂, reassoc_of% hn₂, hq.1.w, reassoc_of% w₂', reassoc_of% k, e₃]
  have H₁ : LBIso (AW.L.pull (ℓ ≫ gW)) (UW.LG.L.pull (π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ)) :=
    pull_both (a := gW) UW.ext ℓ rfl hℓ₁.symm
  have H₂ : LBIso (AW.L.pull (ℓ ≫ gW)) (A₁.L.pull (n ≫ p)) := pull_both hLp n hn₁.symm rfl
  have H₃ : LBIso (A₂.L.pull ((π ≫ κ) ≫ g₂)) (A₁.L.pull (n ≫ p)) :=
    pull_right hLq _ (by simp only [hm, Category.assoc])
  have hG := UW.LG.isLB
  have H : LBIso ((UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)).pull π) (((A₂.L.pull g₂).pull κ).pull π) :=
    pull_pull (pull_pull (pull_pull (LBIso.trans (pull_isLB A₂.isLB _) (pull_isLB A₁.isLB _) (pull_isLB hG _) H₃
      (LBIso.trans (pull_isLB A₁.isLB _) (pull_isLB AW.isLB _) (pull_isLB hG _) H₂.symm H₁)))).symm
  let g' : pullback GW'.hom (jK W₂) ⟶ AW'.A.left := UW'.gen.hom.left
  have : IsIso g' := inferInstanceAs (IsIso ((Over.forget _).map UW'.gen.hom))
  have w' : g' ≫ AW'.A.hom = pullback.snd GW'.hom (jK W₂) := Over.w UW'.gen.hom
  have := AW'.isAb.smooth
  have := AW'.isAb.proper
  have hc := AW'.isAb.geomConnected
  have hD := (lb_gen_iso_descend_field (FractionRing W₂) Ω' j₂ _ _ (pullback.snd GW'.hom (jK W₂)) s π
    (by rw [← w']; infer_instance) (by rw [← w']; infer_instance)
    (by rw [← w']; exact (MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id (g' ≫ AW'.A.hom)).symm⟩) hc))
    (IsPullback.of_hasPullback _ _)).2 _ _ (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) H
  exact LBIso.trans (pull_isLB UW'.LG.isLB _) (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) hL hD

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem sym_of_lbIso_pull_hom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f →
    ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  intro S H H' _ _ f hf N M hN hM hs hiso s
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, ?_⟩
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme,
      n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left :=
    ⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  have hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom f)
  let ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left) :=
    ![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by
    fin_cases k
    · show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left =
        n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc, hi]
    · show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι
      rw [hn])) t ht
  exact exists_down hw' hN hM (φ' := ψ) c₂ h₂

end GlobalTheory
end

section

open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  letI : (Over.pullback (⊤ : (Sp R₁).Opens).ι).Monoidal :=
    (Over.instBraidedPullback (f := (⊤ : (Sp R₁).Opens).ι)).toMonoidal
  letI : GrpObj ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) :=
    Functor.grpObjObj (F := Over.pullback (⊤ : (Sp R₁).Opens).ι) (G := B)
  have hPB := isGrpPullback_pullback B (⊤ : (Sp R₁).Opens).ι
  have hAb : IsAbelianScheme ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) := by
    have := hB.comm
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hPB.1 hB.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hPB.1 hB.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hPB.1 hB.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hPB.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hPB.2 T x y (pushPt hPB.1.w x) (pushPt hPB.1.w y) rfl rfl,
      ← hPB.2 T y x (pushPt hPB.1.w y) (pushPt hPB.1.w x) rfl rfl, _root_.mul_comm]
  letI : ∀ _ : PUnit.{1}, GrpObj ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) :=
    fun _ => inferInstance
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => hAb) (fun _ => H)

end GlobalTheory.SharpLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  letI : ∀ p, GrpObj ((Over.pullback (U p).ι).obj Y) := fun p =>
    letI : (Over.pullback (U p).ι).Monoidal := (Over.instBraidedPullback (f := (U p).ι)).toMonoidal
    Functor.grpObjObj (F := Over.pullback (U p).ι) (G := Y)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => by
      have := hY.comm
      have := hY.smooth
      have := hY.proper
      have := hY.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change IsProper (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change GeometricallyConnected (pullback.snd Y.hom (U p).ι)
        infer_instance) hK

end GlobalTheory.KTrivSqZero
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.lineBundleIso_of_pullback_chain_through_section : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  first | exact @GlobalTheory.LbChain.lbIso_chain | exact GlobalTheory.LbChain.lbIso_chain | (intros; apply GlobalTheory.LbChain.lbIso_chain <;> assumption)

end
end
