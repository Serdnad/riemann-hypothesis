module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

lemma boxGen_overlap_le {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (a b : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => a k i) ⊓
        LB.wchart (L.pull (F i)) φ (fun k _ => b k i) := by
  have key : ∀ c : K → (LB.LinComb L F (fun _ => 1)).ι,
      LB.wchart (LB.LinComb L F (fun _ => 1)) φ c ≤ LB.wchart (L.pull (F i)) φ (fun k _ => c k i) := by
    intro c y hy
    simp only [LB.wchart, LB.pull, LB.LinComb, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe] at hy ⊢
    intro k _
    exact hy k i
  exact inf_le_inf (key a) (key b)

lemma lcg_linComb_eq_prod {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (a b : K → (LB.LinComb L F (fun _ => 1)).ι) :
    LB.lcg (LB.LinComb L F (fun _ => 1)) φ ε a b =
      ∏ i, res (boxGen_overlap_le L F φ a b i)
        (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i)) := by
  show (∏ k, (res _ (pullU (φ k) (LB.wchart L F (a k) ⊓ LB.wchart L F (b k))
      (LB.lcg L F (fun _ => 1) (a k) (b k)))) ^ ε k) =
    ∏ i, res _ (∏ k, (res _ (pullU (φ k)
      (LB.wchart L (fun _ : PUnit => F i) (fun _ => a k i) ⊓ LB.wchart L (fun _ : PUnit => F i) (fun _ => b k i))
      (LB.lcg L (fun _ : PUnit => F i) (fun _ => 1) (fun _ => a k i) (fun _ => b k i)))) ^ ε k)
  simp only [LB.lcg, map_prod, map_zpow, zpow_one, Finset.univ_unique, Finset.prod_singleton,
    ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  congr 1
  repeat erw [ReciprocityTheory.ChartRestriction.G.DVR.res_res']

private lemma res_res_eq {Z : Scheme.{0}} {U V V' W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : V' ≤ U)
    (h₄ : W ≤ V') (x : Γ(Z, U)ˣ) : res h₂ (res h₁ x) = res h₄ (res h₃ x) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res']

theorem isGen_boxGen {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  apply GlobalTheory.BoxCubical.isGen_boxGen <;> assumption

theorem boxIsLB (S : Scheme.{0}) : BoxIsLBSt (S := S) := by
  intro G' G _ _ j p L hL
  exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

theorem boxRigIsGen (S : Scheme.{0}) : BoxRigIsGenSt (S := S) := by
  intro G' G _ _ _ _ j p L r hL hr
  refine isGen_boxGen _ _ _ _ _ (fun i => ?_)
  have := p.hom i
  exact LBxP.isGen_pullAlong L (p.pr i).left (𝟙 _) (fun _ : PUnit => eSec G)
    (fun _ => 1) (fun _ => eSec G') (fun _ => (CubeMap.ofHom (p.pr i)).e_comm) r hr

end GlobalTheory
end

section

namespace GlobalTheory.UT

theorem sumI_of_finite {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E)
    (S : Finset Ix) (hS : ∀ i, i ∉ S → x i = 0) : SumI I x (∑ i ∈ S, x i) := by
  classical
  have hx : ∀ i, x i ∈ Submodule.span R (↑(S.image x) : Set E) := fun i => by
    by_cases h : i ∈ S
    · exact Submodule.subset_span (by simpa using ⟨i, h, rfl⟩)
    · rw [hS i h]; exact Submodule.zero_mem _
  refine ⟨Submodule.span R ↑(S.image x), ⟨_, rfl⟩, Submodule.sum_mem _ fun i _ => hx i, hx, fun n => ⟨S, fun T hT => ?_⟩⟩
  rw [Finset.sum_subset hT (fun i _ h => hS i h), sub_self]; exact Submodule.zero_mem _

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {Z : Scheme.{0}}

def rv (ρ : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ r z J

theorem val_rigPow (ρ : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : val (rigPow A L ρ k) r z J = rv ρ r z J ^ k :=
  map_zpow _ _ _

theorem val_rigT (ρ : LB.Gen (L.pull (eSec A))) (T : Over S) (k : ℤ) (r : Z ⟶ T.left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (rigT A L ρ T k) r z J = rv ρ (r ≫ T.hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  refine Eq.trans ?_ (val_of (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => congrArg J (Category.assoc _ _ _))).symm
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

omit [GrpObj A] in
theorem val_powFrame {T : Over S} (x : T ⟶ A) (e) (k : ℤ) (r : Z ⟶ T.left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : val (powFrame A L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem val_powGen {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) :
    val (GeneratorPullback.powGen M φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

theorem one_left (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  rw [Hom.one_def, Over.comp_left]; rfl

theorem pull_mul (P : PolAV S) (T : Over S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (n k k' : ℕ) (hk : k' = k * n ^ 2)
    (x : T ⟶ P.A) (e) (hx : IsTorsFrame P ρ n x e) (ψ : T ⊗ P.A ⟶ T ⊗ P.A) (m : T ⊗ P.A ⟶ P.A)
    (hm : ψ ≫ snd _ _ = m) (hψ : ψ ≫ fst _ _ = fst _ _) (hmn : m = snd _ _ ≫ (𝟙 P.A ^ n)) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, m.left] ![(k' : ℤ), -(k : ℤ)]), α.IsGen ∧
      LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T ((k' : ℤ) - k)) ∧
      ∀ (t : LB.Sec (LPow P.A P.L (k : ℤ) T)) (c : ∀ z : T.left, T.left.presheaf.stalk z),
        (∀ z J, Good P.L z J → VVRank.sv P.A t (ptSecT P.A 1).left z J =
          c z * (val (rigT P.A P.L ρ T (k : ℤ)) (𝟙 _) z J).val) →
        ∃ t' : LB.Sec (LPow P.A P.L (k' : ℤ) T), IsTwistPull P.A P.L ψ m hm k' k α t t' ∧
          ∀ z J, Good P.L z J → VVRank.sv P.A t' (ptSecT P.A x).left z J =
            c z * (val (powFrame P.A P.L x e k') (𝟙 _) z J).val := by
  obtain ⟨hxn, -, α₀, hα₀, hN, hC⟩ := hx
  have em : (snd T P.A).left ≫ (mulA P.A n).left = m.left := by rw [hmn, Over.comp_left]
  obtain ⟨α, hα, hv⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, m.left]) (ε' := ![(k' : ℤ), -(k : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, em, hk]
      congr 2 <;> push_cast <;> ring)
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L _ _ α₀ (snd T P.A).left) k)
    (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα₀ _) k)
  have hv' : ∀ (y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      val α (ptSecT P.A y).left z J = val α₀ y.left z J ^ k := fun y z J hJ => by
    rw [hv _ _ z J hJ, val_powGen, val_pull hJ, ← Over.comp_left, ptSecT, lift_snd]
  refine ⟨α, hα, corr_of_val P.isLB fun z J hJ => ?_, fun t c ht => ?_⟩
  · have a := val_corr hJ hN T.hom
    rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow] at a
    rw [val_pull hJ, Category.id_comp, hv' 1 z J hJ, one_left, val_rigT ρ T _ _ z hJ, Category.id_comp]
    refine (congrArg (· ^ k) a).trans ?_
    change (rv ρ T.hom z J ^ ((n : ℤ) ^ 2) * (rv ρ T.hom z J)⁻¹) ^ k = rv ρ T.hom z J ^ _
    rw [← zpow_sub_one, ← zpow_natCast, ← zpow_mul, hk]
    congr 1; push_cast; ring
  · obtain ⟨t', ht'⟩ := VVRank.exists_isTwistPull P.A (ψ := ψ) (hm := hm) P.isLB hα t
    refine ⟨t', ht', fun z J hJ => ?_⟩
    have e₁ : ptSecT P.A x ≫ ψ = ptSecT P.A 1 := by
      ext1
      · rw [Category.assoc, hψ, ptSecT, ptSecT, lift_fst, lift_fst]
      · rw [Category.assoc, hm, hmn, ptSecT, ptSecT, lift_snd_assoc, lift_snd, MonObj.comp_pow,
          Category.comp_id, hxn]
    have a := val_corr hJ hC (𝟙 _)
    rw [val_powFrame, val_mul hJ, val_pull hJ, val_rigT ρ T _ _ z hJ, Category.id_comp, zpow_one] at a
    rw [VVRank.sv_of_isTwistPull P.A ht' _ z hJ, ← Over.comp_left, e₁, ht z J hJ, hv' x z J hJ,
      val_rigT ρ T _ _ z hJ, val_powFrame, mul_left_comm, ← Units.val_mul, zpow_natCast, ← mul_pow, ← a,
      ← zpow_natCast, ← zpow_mul, hk]
    congr 3; push_cast; ring

theorem pull_mul_value : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (n k k' : ℕ), k' = k * n ^ 2 → ∀ (x : TFK (R := R) F ⟶ A.A) e, IsTorsFrame A ρ n x e → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ (𝟙 A.A ^ n) → ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)]), α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) ∧ ∀ (t : SecA A F k) (c : F), (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → ∃ t' : SecA A F k', IsTwistPull A.A A.L ψ m hm k' k α t t' ∧ (∀ z J, Good A.L z J → sA t' (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k') (𝟙 _) z J).val) :=
  fun R _ _ A F _ _ ρ _ n k k' hk x e hx ψ m hm hψ hmn => by
    obtain ⟨α, h₁, h₂, h₃⟩ := pull_mul A (TFK (R := R) F) ρ n k k' hk x e hx ψ m hm hψ hmn
    exact ⟨α, h₁, h₂, fun t c ht => h₃ t (fun z => cst (R := R) F z c) ht⟩

end GlobalTheory.UT.PullMul
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcNotAbelian

theorem isProper_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (p : Spec (CommRingCat.of K)) (hp : t p ∈ abLocus G) :
    IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Spec (CommRingCat.of K') := (default : PrimeSpectrum K')
  have : Nonempty (Spec (CommRingCat.of K')) := ⟨q⟩
  have h₁ : IsProper (pullback.snd G.hom (u ≫ t)) :=
    hp K' (u ≫ t) ⟨q, congrArg (fun z => t z) (Subsingleton.elim (u q) p)⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]; infer_instance
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩


open TorusToProper in
theorem subsingleton_of_mono (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  have h := splitTorus_hom_proper_trivial_field K X B f hf
  have e : ptFun K X (AddMonoidAlgebra K X) (univ K X) = ptFun K X (AddMonoidAlgebra K X) 1 := by
    rw [← cancel_mono f, h, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have e₂ := (ptFun_fst K X _ (univ K X)).symm.trans
    ((congrArg (fun z => z.left ≫ Rosenlicht.torusFst _ X) e).trans (ptFun_fst K X _ 1))
  have e₃ : charRing X _ (univ K X) = charRing X (AddMonoidAlgebra K X) 1 :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
  have key : ∀ a : X, (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra K X) = 1 := by
    intro a
    have := congrArg (fun φ => φ (AddMonoidAlgebra.single a 1)) e₃
    simp only [charRing_single] at this
    simpa [univ] using this
  exact ⟨fun a b => AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K)) ((key a).trans (key b).symm)⟩

theorem subsingleton_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (A : Type) [CommRing A] (hA : IsField A) (t : Spec (CommRingCat.of A) ⟶ S) (p : Spec (CommRingCat.of A))
    (hp : t p ∈ abLocus G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ (Over.pullback t).obj G) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  letI := hA.toField
  have : IsProper ((Over.pullback t).obj G).hom := isProper_fibre G hG A t p hp
  exact subsingleton_of_mono A X _ f hf

end ArcNotAbelian


open ArcNotAbelian in
theorem arcWit_mem_range_jK_of_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (x : Sp (PowerSeries k)), χ x ∈ Set.range Y.j → x ∈ Set.range (jK (PowerSeries k)) := by
  intro E _ _ _ H D l Xo c k _ bF a O _ β Y χ W x hx
  refine mem_range_jK x fun hX => ?_
  have h₁ : χ x ∈ abLocus Y.t.G := by
    obtain ⟨p, hp⟩ := hx
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    rw [← hp]
    exact hz
  have h₂ : x ∈ abLocus W.t.G := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 x).1 h₁
  have hmax : (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one, ← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hF : IsField (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1) ≤ x.asIdeal := by
    rw [zero_add, pow_one, Ideal.span_le, Set.singleton_subset_iff]; exact hX
  obtain ⟨p, hp⟩ : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick (PowerSeries k) (Ideal.span {PowerSeries.X}) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial (a.restrict β).D₀.X := (a.restrict β).nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory



theorem arcWit_agree_of_isPullUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ := by
  intro E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD₂ ⟨hφe, hee, w₂, hwe, T₂⟩ ψ bc hψ _ hbc hPU₂
    hact h3
  have he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G := by
    rw [Category.id_comp]
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ψ.hom)
  obtain ⟨wL₂, g₂, he₂, m₂, lev₂⟩ := hPU₂.lg
  have pg₂ := (isGen_iff wL₂).1 g₂
  refine ⟨hψ, hact, h3, he, pullCongr hbc wL₂,
    (isGen_iff _).2 (pgen_pullCongr hbc pg₂), ?_, fun n ψn hψn => ?_⟩
  · have HA := (maps_iff wL₂ _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig
      (Out.specOf (RingHom.id (PowerSeries k))) _ (rigPull_le _ _ he₂ W'.P.U.LG.L) (fun _ => rfl)).1 m₂
    have e0 : Out.specOf (RingHom.id (PowerSeries k)) = 𝟙 (𝟙_ (Over (Sp (PowerSeries k)))).left := by
      simp [Out.specOf]
    have HB : PMaps wL₂ (fun _ : PUnit => eSec W.t.G) (fun _ => eSec W'.t.G) (fun _ => 1) W.P.U.LG.rig W'.P.U.LG.rig
        (𝟙 _) := e0 ▸ HA
    exact (maps_iff (pullCongr hbc wL₂) _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig (𝟙 _) _
      (rigPull_le _ _ he W'.P.U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr hbc HB)
  · obtain ⟨h₂, hh₁, hh₂, ht₂, hw₂⟩ := lev₂ n
    have hfst : h₂ ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
        (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left ≫ ψ.hom.left := by
      rw [hh₁, hbc]
    obtain rfl : h₂ = ψn := by rw [hψn]; exact thick_map_eq ψ.hom h₂ hfst
    refine ⟨?_, fun A _ _ v => ⟨fun x pt₀ t₀ _ hg => ?_, fun j₀ jM jM' jL jL' H1 H2 H3 => ?_⟩⟩
    · exact (congrArg (fun f => (W.P.U.gt n).pG.left ≫ f) hφe.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ W'.φ) hh₂)).trans (Category.assoc _ _ _))
    · obtain ⟨hψ₂, hm₂⟩ := ht₂ (W.e x)
      have P₂ := (maps_iff hD₂.w _ _ _ ((W.P.U.gt n).t (W.e x)) ((W'.P.U.gt n).t (hD₂.xe (W.e x))) h₂ _
        (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ₂) (fun _ => rfl)).1 hm₂
      have Q₂ := genRelR_transfer T₂ W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB
        (fun k => by rw [Category.assoc, hψ₂ k, Category.id_comp, Category.assoc])
        (pmaps_pullGen P₂ v (v ≫ h₂) rfl) t₀
      have Q₃ := genRelR_heq hφe hwe (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀
      rw [← hee x]
      exact Q₂.2 (Q₃.2 hg)
    · have m1 := (top_le_iff_cpt _ _).1 H1
      have m2 := (top_le_iff_cpt _ _).1 H2
      have m3 := (top_le_iff_cpt _ _).1 H3
      have p2 : (v ≫ (W.P.U.gt n).pG.left) ≫ hD₂.e.hom.left ≫
          pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))) =
          v ≫ h₂ ≫ (W'.P.U.gt n).pG.left := by rw [Category.assoc, hh₂]
      have p3 : (v ≫ h₂) ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
          (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ≫ ψ.hom.left := by
        rw [Category.assoc, hfst, Category.assoc]
      have e2 := congrArg (fun g => g (cpt A)) p2
      have e3 := congrArg (fun g => g (cpt A)) p3
      simp only at e2 e3
      have hjM := m1.2
      have mB1 : W'.φ ((hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom
          (Out.specOf (RingHom.id (PowerSeries k)))) ((v ≫ (W.P.U.gt n).pG.left) (cpt A))) ∈ a.D₀.P.L.U j₀ := by
        have := mem_pull.1 m2.1; rw [← e2] at this; exact this
      have mB2 : (hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (W.P.U.gt n).pG.left) (cpt A)) ∈ W'.P.D.toPre.P.L.U jM' := by
        have := m2.2; rw [← e2] at this; exact this
      have mC1 := mem_pull.1 m3.1
      have mC2 := m3.2
      have mC3 : (bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        rw [hbc]; exact mC1
      have mD : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        have e3' : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) =
            ψ.hom.left ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) := e3
        rw [e3']; exact mC1
      have R2 := T₂ _ (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM' jM mB1 mB2 hjM
      rw [p2] at R2
      have RE := gw_heq hφe hwe (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM
      have RU2 : gw hD₂.w (v ≫ (W.P.U.gt n).pG.left) (cpt A) jM' jM *
          gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)) =
          gm (v ≫ h₂) (cpt A) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')) *
          gw wL₂ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A) jL' jL := by
        have := gm_of_res_eq' (hw₂ (fun _ => jM') jM jL (fun _ => jL')) v (y := cpt A)
          ⟨⟨⟨⟨mem_pull.2 mB2, hjM⟩, ⟨mem_pull.2 hjM, mem_pull.2 mC2⟩⟩, ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩⟩,
            ⟨mem_pull.2 mC3, mC2⟩⟩
        rw [gm_pull, gm_pull, gm_pull] at this
        · exact this
        · exact ⟨mem_pull.2 mC3, mC2⟩
        · exact ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        · exact ⟨mem_pull.2 mB2, hjM⟩
      have EU := congrArg (· * gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL))) (RE.symm.trans R2)
      beta_reduce at EU
      rw [_root_.mul_assoc, RU2, ← _root_.mul_assoc, ← gw_pullCongr hbc wL₂] at EU
      apply toStkA_injective
      rw [map_mul, map_mul, map_mul, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR]
      · have EU' := congrArg Units.val EU
        simp only [Units.val_mul] at EU'
        exact EU'
      all_goals first
        | exact H1
        | exact H2
        | exact H3
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m1.2, mem_pull.2 mC2⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericDim

theorem smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (g : ℕ), SmoothOfRelativeDimension g (pullback.snd G.hom (jK R)) → SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ _ g hg
  have hdense := (ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK (V := R)).denseRange
  have hloc : ∀ x : G.left, ∃ W : G.left.Opens, x ∈ W ∧
      SmoothOfRelativeDimension g (W.ι ≫ G.hom) := by
    intro x
    obtain ⟨n, W, hxW, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    refine ⟨W, hxW, ?_⟩
    have hopen : IsOpen (G.hom '' (W : Set G.left)) := G.hom.isOpenMap _ W.isOpen
    obtain ⟨y, w, hwW, hwy⟩ := hdense.exists_mem_open hopen ⟨G.hom x, x, hxW, rfl⟩
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := jK R) w y hwy
    have hzW : pullback.fst G.hom (jK R) z ∈ W := by rw [hz]; exact hwW
    have hng : n = g :=
      ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback G.hom (jK R)) hW hg z hzW
    exact hng ▸ hW
  have i1 : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension g)
  choose W hxW hW using hloc
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) hW

end GlobalTheory.GenericDim
end
