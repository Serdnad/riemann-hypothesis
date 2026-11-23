module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExAtMemPairChartIff
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem one_le_rN (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)

end GlobalTheory.RealCompare
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem mono_fst_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem corr_pullGen_of_pmaps {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) :
    LB.Gen.Corr L _ _ _ _ a (LB.pullGen L _ _ t h) := by
  subst hF
  refine corr_of_val hL fun z J hJ => ?_
  have hk : ∀ k, (𝟙 Y' ≫ h) ≫ φ k = 𝟙 Y' ≫ φ' k := fun k => by
    rw [Category.assoc, ← hψ k, Category.comp_id]
  have hmem : ∀ k, (𝟙 Y' ≫ φ' k) z ∈ L.U (J (𝟙 Y' ≫ φ' k)) := fun k => hJ _
  have key := hm _ (𝟙 Y') z (fun k => J (𝟙 Y' ≫ φ' k)) (fun k => J (𝟙 Y' ≫ φ' k)) hmem hmem
  rw [Finset.prod_eq_one (fun k _ => by
    rw [hw _ _ z _ _ (hmem k) (hmem k), gm_self hL _ z (hmem k), one_zpow]), _root_.one_mul] at key
  rw [val_pull hJ, val_of t _ z J _ (fun k => congrArg J (hk k))]
  exact key.symm

theorem sameUnif_of_isPullUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by
  intro R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H
  obtain ⟨hx, hΦ, hw₀⟩ := hid
  obtain ⟨wL, hg, he, hr, H⟩ := (isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H
  have hr' := (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
    (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr
  clear hr he
  generalize bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF
  subst hF
  refine ⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩
  · have hs := specOf_id R
    rw [hs] at hr'
    exact hr'
  obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
  have hh : h = ((Over.pullback (thick R I e)).map ε.hom).left := by
    have := mono_fst_thick I e G
    rw [← cancel_mono (pullback.fst G.hom (thick R I e))]
    refine hf.trans ?_
    exact (pullback.lift_fst _ _ _).symm
  subst hh
  rw [hΦ, Category.comp_id] at hp
  have hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y := fun y => by
    rw [hΦ]; rfl
  refine ⟨?_, fun χ => ?_, ?_⟩
  · ext1
    have := mono_fst_thick I e D.toPre.P.A
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]
    exact hp
  · obtain ⟨hψ, hm⟩ := ht χ
    rw [hx χ] at hψ hm
    exact corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm
  · intro Z r z jM jL jL' h₁ h₂ h₃
    have key := hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃
    rw [hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁,
      _root_.one_mul] at key
    exact key

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem exists_hol_linear_lift {B : Set (Fin m → ℂ)} (hB : IsOpen B) {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (f : G ⟶ G) [IsMonHom f] :
    ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ b ∈ B, ∀ z, e b (L b z) = e b z ≫ f) ∧
      ∀ z, DifferentiableOn ℂ (fun b => L b z) B := by
  have key : ∀ b₁ ∈ B, ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ᶠ b in 𝓝 b₁, ∀ z, e b (L b z) = e b z ≫ f) ∧ ∀ z, DifferentiableAt ℂ (fun b => L b z) b₁ := by
    intro b₁ hb₁
    obtain ⟨ζ, -, h2, h3⟩ := hl.lift (W := B ×ˢ Set.univ) (β := Prod.fst)
      (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2 ≫ f) (w₀ := (b₁, 0)) (z₀ := 0)
      (hB.prod isOpen_univ) ⟨hb₁, trivial⟩ differentiableOn_fst (fun _ h => h.1) (isHolTo_comp_hom hol f.left)
      (by simp only [hom_zero (he b₁ hb₁).1.1, MonObj.one_comp])
    refine ⟨fun b => ((fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ _ _)).toLinearMap, ?_, fun z => ?_⟩
    · have ht : Tendsto (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (𝓝 b₁) (𝓝 (b₁, 0)) :=
        (Continuous.prodMk_left _).tendsto _
      filter_upwards [hB.mem_nhds hb₁, ht.eventually h2.eventually_analyticAt, ht.eventually h3.eventually_nhds]
        with b hb ha hz z
      have hd := ha.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right b (0 : Fin g → ℂ))
      have := fderiv_lift (x := fun z => e b z ≫ f) (fun z w => by simp only [(he b hb).1.1, MonObj.mul_comp])
        (he b hb).1.1 (he b hb).1.2.1 hr (he b hb).2 hd.differentiableAt
        (((Continuous.prodMk_right b).tendsto 0).eventually hz) z
      rwa [hd.fderiv] at this
    · have : DifferentiableAt ℂ (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0) ((0 : Fin m → ℂ), z)) b₁ :=
        (h2.fderiv.differentiableAt.comp b₁ (hasFDerivAt_prodMk_left b₁ (0 : Fin g → ℂ)).differentiableAt).clm_apply
          (differentiableAt_const ((0 : Fin m → ℂ), z))
      exact this
  choose! L h1 h2 using key
  refine ⟨fun b => L b b, fun b hb => (h1 b hb).self_of_nhds, fun z b₁ hb₁ => ?_⟩
  refine ((h2 b₁ hb₁ z).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hB.mem_nhds hb₁, h1 b₁ hb₁] with b hb h
  rw [linear_lift_unique (he b hb).1.1 hr (he b hb).2 (L := L b b) (L' := L b₁ b)
    fun z => ((h1 b hb).self_of_nhds z).trans (h z).symm]

theorem exists_hol_rep {O : Type} [CommRing O] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (act : OAct O G) :
    ∃ F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ),
      (∀ b ∈ B, ∀ a z, e b ((F b a).mulVec z) = e b z ≫ act.act a) ∧
      ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B := by
  classical
  choose L h1 h2 using fun a => haveI := act.hom a; exists_hol_linear_lift hB hr hol he hl (act.act a)
  have key : ∀ b ∈ B, ∃ F : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a, F a = LinearMap.toMatrix' (L a b) := by
    intro b hb
    have u := fun L L' => linear_lift_unique (he b hb).1.1 hr (he b hb).2 (V := Fin g → ℂ) (L := L) (L' := L')
    refine ⟨RingHom.mk' ⟨⟨fun a => LinearMap.toMatrix' (L a b), ?_⟩, fun a a' => ?_⟩ fun a a' => ?_, fun _ => rfl⟩
    · rw [u (L 1 b) LinearMap.id fun z => by rw [h1 1 b hb, act.one, Category.comp_id, LinearMap.id_apply],
        LinearMap.toMatrix'_id]
    · change LinearMap.toMatrix' (L (a * a') b) = _
      rw [u (L (a * a') b) (L a b ∘ₗ L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.comp_apply, h1 _ b hb, h1 _ b hb, mul_comm, act.mul, Category.assoc],
        LinearMap.toMatrix'_comp]
    · change LinearMap.toMatrix' (L (a + a') b) = LinearMap.toMatrix' (L a b) + LinearMap.toMatrix' (L a' b)
      rw [u (L (a + a') b) (L a b + L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.add_apply, (he b hb).1.1, h1 _ b hb, h1 _ b hb, act.add, MonObj.comp_mul], map_add (f := _)]
  choose F hF using key
  refine ⟨fun b => if hb : b ∈ B then F b hb else F b₀ hb₀, fun b hb a z => ?_, fun a i j => ?_⟩
  · simp only [dif_pos hb, hF, LinearMap.toMatrix'_mulVec, h1 a b hb]
  · refine (differentiableOn_pi.1 (h2 a (Pi.single j 1)) i).congr fun b hb => ?_
    simp only [dif_pos hb, hF, LinearMap.toMatrix'_apply]

def HasForm {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) : Prop :=
  ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y

open Matrix in
theorem HasForm.of_comp {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {P : La → (Fin g → ℂ)} {g' : ℕ}
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hL : Function.Injective L) (h : HasForm EF (fun x => L (P x))) :
    HasForm EF P := by
  obtain ⟨Hm, h1, h2, h3⟩ := h
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h1, fun z hz => ?_, fun x y => ?_⟩
  · rw [key]
    exact h2 _ fun h0 => hz (hL (h0.trans (map_zero L).symm))
  · rw [key, h3]

theorem int_eq_of_exp {a b : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) : a = b := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ b - a := fun k hk => by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp := Complex.two_pi_I_ne_zero
    refine ⟨n, ?_⟩
    have : ((b : ℂ) - a) = k * n := by
      refine mul_left_cancel₀ hp ?_
      field_simp at hn
      linear_combination (2 * Real.pi * Complex.I) * hn
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((b - a).natAbs + 1) (Nat.succ_pos _)) (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem hasForm_of_weil (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt)
    (A : Out.PolAV X) (y₀ y : Sp ℂ ⟶ X) (hy : y = (𝟙_ (Over (Sp ℂ))).hom ≫ y₀)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ A.A)} (he : IsExp y e) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0)
    (hl : ∀ (n : ℕ) (x : (Fin n → ℂ) → (Over.mk y ⟶ A.A)), IsHolTo Set.univ (fun w => (x w).left) → e 0 = x 0 →
      ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), AnalyticAt ℂ ζ 0 ∧ ∀ᶠ w in 𝓝 0, e (ζ w) = x w)
    {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) (hP : ∀ a, e (P a) = 1)
    (hw : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs A.A A.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) : HasForm EF P := by
  subst hy
  obtain ⟨A', φ, hφ, -, hm, t, ht⟩ := hB _ _ y₀ A
  have hgp : IsGrpPullback A'.A A.A y₀ φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨rig, hrig⟩ := A'.rigid
  obtain ⟨u, Hm, χ, Ef, ⟨h1, h2, -⟩, -, -, -, -, -, h3, -, h4⟩ := hT A' rig hrig
  let x : (Fin A'.g → ℂ) → (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y₀) ⟶ A.A) := fun w => Out.toBase hφ.w (u.ex w)
  have hx : ∀ z w, x (z + w) = x z * x w := fun z w => by simp only [x, u.ex_add, hm]
  have hinj : Function.Injective (fun p : 𝟙_ (Over (Sp ℂ)) ⟶ A'.A => Out.toBase hφ.w p) := fun p q h =>
    Over.OverMorphism.ext (hφ.hom_ext (congrArg (fun s => s.left) h) ((Over.w p).trans (Over.w q).symm))
  have hker : ∀ z, x z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [← u.ker, ← hom_zero hx, ← hom_zero u.ex_add]
    exact hinj.eq_iff
  have hsx : Function.Surjective x := fun q => by
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk (hφ.lift q.left (𝟙_ (Over (Sp ℂ))).hom (Over.w q)) (hφ.lift_snd _ _ _))
    refine ⟨w, Over.OverMorphism.ext ?_⟩
    change (u.ex w).left ≫ φ = _
    rw [hw]
    exact hφ.lift_fst _ _ _
  have hhol : IsHolTo Set.univ (fun w => (u.ex w).left) := fun U f => by simpa using u.hol U f
  obtain ⟨ζ, hζ, hζ'⟩ := hl _ x (isHolTo_comp_hom hhol φ) (by rw [hom_zero hx, hom_zero he.1])
  obtain ⟨L, hL⟩ := exists_linearEquiv_lift hx he.1 hsx he.2.1 (by
    haveI := u.discrete
    rw [show {z | x z = 1} = (u.Λ : Set _) from Set.ext hker]
    exact DiscreteTopology.isDiscrete) hr hk hζ.differentiableAt hζ'
  have hmem : ∀ a, L.symm (P a) ∈ u.Λ := fun a => by rw [← hker, ← hL, L.apply_symm_apply, hP]
  refine HasForm.of_comp L.symm.toLinearEquiv.toLinearMap L.symm.injective ⟨Hm, h1, h2, fun a a₂ => ?_⟩
  refine (h3 ⟨_, hmem a⟩ ⟨_, hmem a₂⟩).symm.trans (congrArg _ (int_eq_of_exp fun k hk0 => ?_))
  have e1 := h4 k ⟨_, hmem a⟩ ⟨_, hmem a₂⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have e2 := hw k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have hp : ∀ a, (e ((k : ℂ)⁻¹ • P a)).left = (u.ex ((k : ℂ)⁻¹ • L.symm (P a))).left ≫ φ := fun a => by
    rw [← map_smul, ← L.apply_symm_apply ((k : ℂ)⁻¹ • P a), hL, L.symm_apply_apply]
    rfl
  haveI := A.isAb.comm
  have e3 := (weilIs_grpPullback_of_comm _ _ A.A A'.A y₀ φ A.L A'.L A.isLB A'.isLB hgp (LBIso.symm ⟨t, ht⟩) _ k _ _ _ _ _ (hp a) (hp a₂)).1 e1
  exact congrArg Units.val (weilIs_unique_fieldPoint _ A.A A.L A.isLB ℂ _ k _ _ _ _ e3 e2)

end

end GlobalTheory.LocLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.weilIs_iff_of_isGrpPullback_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  GlobalTheory.weilIs_grpPullback_of_comm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.const_thickening_field_structure : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.ConstThickening.structure_dualNumber | exact GlobalTheory.ConstThickening.structure_dualNumber | (intros; apply GlobalTheory.ConstThickening.structure_dualNumber <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_mulPull_gen_over (H : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (T : Over S) (N : ℕ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := H _ P N
  have e₁ : (snd T P.A).left ≫ (Out.mulA P.A N).left = (snd T P.A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ N).left])
    (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((N : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (Out.mulA P.A N).left] ![(N : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_twistPull_mul_fn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (th : LB.Sec (Out.LPow P.A P.L 1 T)), u.IsAH Hm χ → Odd N → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) → ∃ (s1 : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)) (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1])) (c : ℂ), c ≠ 0 ∧ α.IsGen ∧ Out.IsTwistPull P.A P.L (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α th s1 ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s1.f j) = c * θ ((N : ℂ) • z) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro hLaw _ _ _ P u Hm χ N θ T _ p th hAH _ hth
  have hL := P.isLB
  obtain ⟨α, hα⟩ := exists_mulPull_gen_over hLaw.mulPull P T N
  obtain ⟨s1, hs1⟩ := ThetaPtExist.exists_isTwistPull hL (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α hα th
  obtain ⟨c, hc0, -, hc, -⟩ := (ThetaFn.pull_analytic_at hL hAH (ψ := Out.mulT P.A T N) (p := p)
    (m := snd T P.A ^ N) (lift_snd _ _) (Φ := (N : ℂ) • LinearMap.id) (fun z => by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ThetaFn.exAt_mulT]) (a := (N : ℤ) ^ 2) (b := 1) hα).2
  have h1 : ThetaFn.IsFnAt u p 1 th θ := fun j z hj =>
    hth j z ((ThetaFn.exAt_mem_chart_iff u p 1 j z).1 hj)
  have h2 := ThetaFn.isFnAt_fnAt u p hL ((N : ℤ) ^ 2) s1
  refine ⟨s1, α, c, hc0, hα, hs1, fun j z hj => ?_⟩
  refine (h2 j z ((ThetaFn.exAt_mem_chart_iff u p _ j z).2 hj)).trans ?_
  rw [hc th s1 θ _ hs1 h1 h2 z]
  rfl

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LinDescent


open ThetaSplit in
theorem lbPow_descends : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by
  intro hlaw k _ _ P n C B _ ψ hn hnk htor hW hψ hfin het hsurj hker
  have := P.isAb.comm
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }
  have hfinT : Finite {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} := by
    have h := (hlaw.mulN (Sp k) P n hn).2.2.2.2 k (𝟙 _) hnk
    exact Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ hn.ne'))
  have : Finite C := Finite.of_injective
    (fun c : C => (⟨c.1, htor c.1 c.2⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1}))
    fun a b h => Subtype.ext (congrArg (fun q => q.1) h)
  obtain ⟨u, hu, hc⟩ := ThetaSplit.exists_cocycle hlaw.globalFns P.isAb P.isLB (ThetaSplit.units_divisible k) n C.subtype
    (fun c c' => hW c.1 c.2 c'.1 c'.2)
  refine exists_descent_of_isReduced (Sp k) P.A B ψ C C.subtype (lbPow P.L n) (DVR.linComb_isLB P.L P.isLB _ _) hψ hfin het hsurj
    (fun k' _ _ t => ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c h => ?_⟩) u hu hc
  · obtain ⟨c, h₁, h₂⟩ := ThetaSplit.exists_rational_ker ψ t x hx
    exact ⟨⟨c, (hker c).1 h₁⟩, h₂⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, (hker (C.subtype c)).2 c.2, MonObj.comp_one]
  · have : Epi t := ThetaSplit.epi_of_fields t
    refine Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 ?_))
    have e : toUnit (Over.mk t) ≫ c.1 = toUnit (Over.mk t) ≫ (1 : 𝟙_ (Over (Sp k)) ⟶ P.A) :=
      h.trans (MonObj.comp_one _).symm
    exact congrArg (fun q => q.left) e

end GlobalTheory.LinDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_isSeparated_pullback_snd : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), LocallyOfFiniteType p → QuasiCompact p → IsSeparated (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.SpreadSep.exists_fg_isSeparated | exact GlobalTheory.SpreadSep.exists_fg_isSeparated | (intros; apply GlobalTheory.SpreadSep.exists_fg_isSeparated <;> assumption)
end
