module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOneAddKill

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjQuot

open MvPolynomial GlobalTheory.ProjSpace GlobalTheory.ThickeningDetermines

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {R A σ : Type} [CommRing R] [CommRing A] [Algebra R A] {r : σ → A} {i : σ}

theorem aeval_X_pow_mul (hi : r i = 1) (k : ℕ) (F : MvPolynomial σ R) :
    aeval r (X i ^ k * F) = aeval r F := by
  rw [map_mul, map_pow, aeval_X, hi, one_pow, _root_.one_mul]

theorem isHomogeneous_X_pow_mul_add_X_pow_mul (i : σ) {n m : ℕ} {F G : MvPolynomial σ R} (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : (X i ^ m * F + X i ^ n * G).IsHomogeneous (m + n) := by
  have h₁ : (X i ^ m * F).IsHomogeneous (m + n) := (isHomogeneous_X_pow i m).mul hF
  have h₂ : (X i ^ n * G).IsHomogeneous (m + n) := by
    simpa only [Nat.add_comm n m] using (isHomogeneous_X_pow i n).mul hG
  exact h₁.add h₂

theorem exists_isHomogeneous_aeval_eq (hi : r i = 1) (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ aeval r G = aeval r p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isHomogeneous_C _ a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, F, hF, eF⟩ := hp
    obtain ⟨b, G, hG, eG⟩ := hq
    refine ⟨b + a, X i ^ b * F + X i ^ a * G, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG, ?_⟩
    rw [map_add (f := _), aeval_X_pow_mul hi, aeval_X_pow_mul hi, eF, eG, map_add (f := _)]
  | mul_X p j hp =>
    obtain ⟨a, F, hF, eF⟩ := hp
    exact ⟨a + 1, F * X j, hF.mul (isHomogeneous_X R j), by rw [map_mul, map_mul, eF]⟩

def valueIdeal (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (J : Ideal (MvPolynomial σ R)) : Ideal A where
  carrier := {a | ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ G ∈ J ∧ aeval r G = a}
  zero_mem' := ⟨0, 0, isHomogeneous_zero _ R 0, J.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, F, hF, jF, rfl⟩ ⟨m, G, hG, jG, rfl⟩
    refine ⟨_, _, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG,
      J.add_mem (J.mul_mem_left _ jF) (J.mul_mem_left _ jG), ?_⟩
    rw [map_add (f := _), aeval_X_pow_mul hi, aeval_X_pow_mul hi]
  smul_mem' := by
    rintro c _ ⟨m, G, hG, jG, rfl⟩
    obtain ⟨p, rfl⟩ := hr c
    obtain ⟨n, F, hF, eF⟩ := exists_isHomogeneous_aeval_eq hi p
    exact ⟨_, _, hF.mul hG, J.mul_mem_left _ jG, by rw [map_mul, eF, smul_eq_mul]⟩

end Algebra

variable {R : Type} [CommRing R] {n : ℕ}

def formIdeal (J : Ideal (MvPolynomial (Fin (n + 1)) R)) : (PSpace R n).IdealSheafData :=
  ⨆ p : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J},
    secIdeal (On_isLB R n p.1.1) (formSec p.1.1 p.1.2 p.2.1)

theorem ideal_secIdeal_formSec (i : Fin (n + 1)) (d : ℕ) (G : MvPolynomial (Fin (n + 1)) R)
    (hG : G.IsHomogeneous d) :
    (secIdeal (On_isLB R n d) (formSec d G hG)).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ =
      Ideal.span {aeval (ratio R n i) G} := by
  have hle : chart R n i ≤ (On R n (d : ℤ)).U (fun _ => i) := (On_U R n d (fun _ => i)).ge
  rw [GlobalTheory.ThickeningDetermines.secIdeal]
  refine (GlobalTheory.EffCartierData.ideal_locIdeal _ _ _ _ _ (fun _ => i) hle).trans ?_
  rw [formSec_f, resG_formOn, formOn_eq_aeval]

private theorem mem_valueIdeal_of_eq_one {S A σ : Type} [CommRing S] [CommRing A] [Algebra S A] {r : σ → A}
    {i : σ} (hi : r i = 1) (hr : Function.Surjective (aeval (R := S) r)) (J : Ideal (MvPolynomial σ S))
    (a : A) : a ∈ valueIdeal hi hr J ↔
      ∃ (m : ℕ) (G : MvPolynomial σ S), G.IsHomogeneous m ∧ G ∈ J ∧ aeval r G = a :=
  Iff.rfl

theorem aeval_mem_formIdeal_iff (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1))
    {t : ℕ} {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous t) :
    aeval (ratio R n i) F ∈ (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ ↔
      ∃ k : ℕ, X i ^ k * F ∈ J := by
  have hone : ratio R n i i = 1 := ratioOn_self
  have hsurj := aeval_ratio_surjective R n i
  have key : (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ = valueIdeal hone hsurj J := by
    rw [formIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    simp only [ideal_secIdeal_formSec]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_valueIdeal_of_eq_one]
      exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · intro a ha
      obtain ⟨m, G, hG, jG, rfl⟩ := (mem_valueIdeal_of_eq_one hone hsurj J a).1 ha
      refine Ideal.mem_iSup_of_mem
        (⟨(m, G), hG, jG⟩ : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J}) ?_
      exact Ideal.subset_span (Set.mem_singleton _)
  rw [key, mem_valueIdeal_of_eq_one]
  constructor
  · rintro ⟨m, G, hG, jG, e⟩
    refine ⟨m, ?_⟩
    have h₁ : (X i ^ m * F).IsHomogeneous (m + t) := (isHomogeneous_X_pow i m).mul hF
    have h₂ : (X i ^ t * G).IsHomogeneous (m + t) := by
      simpa only [Nat.add_comm t m] using (isHomogeneous_X_pow i t).mul hG
    have hEq : X i ^ m * F = X i ^ t * G := by
      rw [← formOn_chart_inj R n i h₁ h₂, formOn_eq_aeval, formOn_eq_aeval]
      change aeval (ratio R n i) (X i ^ m * F) = aeval (ratio R n i) (X i ^ t * G)
      rw [aeval_X_pow_mul hone, aeval_X_pow_mul hone, e]
    rw [hEq]
    exact J.mul_mem_left _ jG
  · rintro ⟨k, hk⟩
    exact ⟨k + t, X i ^ k * F, (isHomogeneous_X_pow i k).mul hF, hk, aeval_X_pow_mul hone k F⟩

private theorem resG_refl' {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)) :
    resG Y h a = a := by
  have e : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]

private theorem appLE_congr_of_eq' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (a : Γ(Z, U)) : (φ.appLE U V e).hom a = resG Y e ((φ.app U).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]

private theorem cst_comp_eq_resG_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (φ : Y ⟶ Z)
    (g : Z ⟶ Spec (CommRingCat.of S)) (U : Z.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (h : U ≤ g ⁻¹ᵁ ⊤) (a : S) :
    GlobalTheory.AbLaw.cst (φ ≫ g) V a = resG Y e ((φ.app U).hom ((g.appLE ⊤ U h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a))) := by
  rw [← appLE_congr_of_eq', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_of_eq']
  rfl

theorem eval₂Hom_secPull_coord {Y : Scheme.{0}} (φ : Y ⟶ PSpace R n) (k : PUnit → Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
        (fun j => (Cartier.secPull (coord R n j) φ).f k) F =
      resG Y (Cartier.pull_U (O1 R n) φ k).le
        ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) F)) := by
  have hle := (Cartier.pull_U (O1 R n) φ k).le
  have key : (eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
      fun j => (Cartier.secPull (coord R n j) φ).f k) =
      (resG Y hle).comp ((φ.app (chart R n (k ⟨⟩))).hom.comp (aeval (ratio R n (k ⟨⟩))).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (C a)))
      rw [eval₂Hom_C, aeval_C, algebraMap_sections_eq, CommRingCat.comp_apply]
      exact cst_comp_eq_resG_app φ (PSpace.str R n) _ _ hle le_top a
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (X j)))
      rw [eval₂Hom_X', aeval_X, ← resG_refl' (le_refl (((O1 R n).pull φ).U k)) ((Cartier.secPull (coord R n j) φ).f k),
        resG_secPull_coord φ j k (le_refl _), pullRatio, appLE_congr_of_eq']
      rfl
  exact RingHom.congr_fun key F

private theorem eq_zero_of_resG_eq_zero_of_eq {Y : Scheme.{0}} {U V : Y.Opens} (hUV : V = U) {h : V ≤ U}
    {a : Γ(Y, U)} (ha : resG Y h a = 0) : a = 0 := by
  subst hUV
  have e : homOfLE h = 𝟙 V := Subsingleton.elim _ _
  rwa [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at ha

theorem exists_veryAmpleBy_of_ideal : ∀ (R : Type) [CommRing R] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ F ∈ J, ∀ t, MvPolynomial.homogeneousComponent t F ∈ J) → ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → ((∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) ↔ ∀ i, ∃ k : ℕ, MvPolynomial.X i ^ k * F ∈ J) := by
  intro R _ n J _
  refine ⟨(formIdeal J).subscheme, (formIdeal J).subschemeι ≫ PSpace.str R n,
    (O1 R n).pull (formIdeal J).subschemeι,
    fun j => Cartier.secPull (coord R n j) (formIdeal J).subschemeι,
    pull_isLB (O1_isLB R n) _, veryAmpleBy_secPull_coord _, fun t F hF => ?_⟩
  constructor
  · intro h i
    rw [← aeval_mem_formIdeal_iff J i hF, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
    exact eq_zero_of_resG_eq_zero_of_eq (Cartier.pull_U (O1 R n) _ (fun _ => i))
      ((eval₂Hom_secPull_coord _ (fun _ => i) F).symm.trans (h (fun _ => i)))
  · intro h k
    obtain ⟨m, hm⟩ := h (k ⟨⟩)
    have hz := (aeval_mem_formIdeal_iff J (k ⟨⟩) hF).2 ⟨m, hm⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hz
    exact ((eval₂Hom_secPull_coord _ k F).trans (congrArg _ hz)).trans (map_zero _)

end GlobalTheory.ProjQuot
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem relAmple_of_veryAmpleBy {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (s : Fin (M + 1) → LB.Sec (pw L N))
    (hA : VeryAmpleBy A.hom (pw L N) s) : RelAmple A L := by
  intro U hU
  obtain ⟨hcov, hs⟩ := hA
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have H : IsPullback ψ (A.hom ∣_ U) A.hom U.ι := (isPullback_morphismRestrict A.hom U).flip
  have : IsAffine U := hU
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := isLB_pw hL N
  have hP' := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have h₀ : LBIso (LB.LinComb L (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1)) (pw L N) :=
    LBIso.chartPull (chartPullId _) (chartPullPw L N)
      ⟨_, idIso_isGen (linComb_isLB L hL (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1))⟩
  obtain ⟨W, hW⟩ := LBIso.chartPull
    (chartPullSame L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 𝟙 A.left) (fun _ => 1) ψ
      fun _ => (Category.comp_id _).symm) (chartPullPull (pw L N) ψ ψ rfl) h₀
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A L U N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (pw L N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A L U N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((U.ι.appLE ⊤ ⊤ le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      have e : ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (M := powOver A L U N) (s' i)) le_top).hom.comp
          ((U.ι.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) =
          (ψ.appLE _ _ (loc i).le).hom.comp (cst A.hom (nonzeroLocus (s i))) := by
        ext x
        exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) po.w.symm
      exact (congrArg (fun q => MvPolynomial.eval₂Hom q _ p) e).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem relAmple_iff_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → (RelAmple B L ↔ ∃ d : ℕ, 1 ≤ d ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy B.hom (pw L d) s) := by
  intro R _ B L hL
  refine ⟨fun h => ?_, fun ⟨d, hd, n, s, hs⟩ => relAmple_of_veryAmpleBy hL hd s hs⟩
  obtain ⟨d, hd, n, s, -, hs⟩ := veryAmpleBy_of_relAmple hL h (𝟙 _) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) ⟨_, idIso_isGen hL⟩)
  exact ⟨d, hd, n, s, hs⟩

end GlobalTheory.Unif
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

open TopologicalSpace GlobalTheory.AmpleLocal

theorem gs_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (D : X.Opens) (c : R)
    (z : X) (hz : z ∈ D) : gs (𝟙 X) z D (AbLaw.cst f D c) = gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ c) := by
  rw [← rs_cst f (le_top : D ≤ ⊤) c]
  exact gs_res (𝟙 X) z le_top hz _

theorem veryAmpleBy_pw : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X)
    (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, 1 ≤ d →
    ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s' := by
  intro R _ X f H n s hH ⟨cov, hs⟩ d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  choose aff r hr surj using hs
  choose c hc using fun z : X => exists_chart hH z
  let G : H.ι → Fn X := fun i z => (gm (𝟙 X) z _ (H.g i (c z))).val
  let φ : R → Fn X := fun a z => gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ a)
  have hU : ∀ z, ∃ i, z ∈ H.U i := fun z => ⟨c z, hc z⟩
  have hG : ∀ i z, IsUnit (G i z) := fun _ _ => Units.isUnit _
  let σ : Fin (n + 1) → Fn X := fun i => sv c (s i)
  have hσ : ∀ i, Sc H.U G ⊤ 1 (σ i) := fun i =>
    sc_sv (P := H) (κ := id) (fun _ => le_rfl) hc (fun _ _ _ => (pow_one _).symm) (s i)
  have gen : ∀ i, Gen (nonzeroLocus (s i)) (Set.range φ ∪ Set.range fun m => σ m * AmpleLocal.inv (σ i)) := fun i =>
    (gen_iff _ (r i) _ _ (fun a z hz => gs_cst f _ a z hz)
      (fun m => (ratio_iff hc (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := Fin (n + 1) × Fin (n + 1))).ne'
  let ε := Fintype.equivFinOfCardEq hM
  let τ : Fin (M + 1) → Fn X := fun m => σ (ε.symm m).2 * σ (ε.symm m).1 ^ e
  have hτ : ∀ m, Sc H.U G ⊤ (1 * (e + 1)) (τ m) := fun m => by
    rw [mul_add, _root_.mul_one, add_comm]
    exact (hσ _).mul ((hσ _).pow _)
  have hγ : ∀ y, y ∈ (pw H ((e + 1 : ℕ) : ℤ)).U (c y) := hc
  choose t ht using fun m => exists_sv (P := pw H ((e + 1 : ℕ) : ℤ)) (κ := id) (N := 1 * (e + 1)) (G := G)
    (fun _ => le_rfl) hc (fun i y _ => by
      show (gm (𝟙 X) y _ (H.g i (c y) ^ ((e + 1 : ℕ) : ℤ))).val = _
      rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val, _root_.one_mul]) (isLB_pw hH _) (hτ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (t m)) ⊤ (τ m) := fun m => ht m ▸ loc_sv hγ (t m)
  have main := fun m => extra_section hU hG hσ (fun i => loc_sv hc (s i))
    (fun z _ => Opens.mem_iSup.1 (cov.ge trivial)) aff (S₀ := Set.range φ)
    (by rintro _ ⟨a, rfl⟩; exact mem_reg_iff.2 ⟨_, fun _ _ => rfl⟩) gen (hτ m) (loc m)
  refine ⟨M, t, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i).1, ?_⟩⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (cov.ge (Set.mem_univ z))
    have hu : IsUnit (σ j z) := (loc_sv hc (s j)).unit hj
    refine Opens.mem_iSup.2 ⟨ε (j, j), (loc _ z).2 ⟨trivial, ?_⟩⟩
    simp only [τ, Equiv.symm_apply_apply]
    exact hu.mul (hu.pow e)
  · choose ρ hρ using fun m => mem_reg_iff.1 (Sc.ratio hU hG (hτ m) (hτ i) (loc i))
    refine ⟨ρ, fun m => (ratio_iff hγ (t i) (t m) (ρ m)).2 ?_, ?_⟩
    · have e₁ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t i) = τ i := ht i
      have e₂ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t m) = τ m := ht m
      rw [e₁, e₂]
      exact hρ m
    · refine (gen_iff _ ρ φ _ (fun a z hz => gs_cst f _ a z hz) hρ).1 ((main i).2.mono ?_)
      rintro x (hx | ⟨p, rfl⟩)
      · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
      · refine ⟨_, Subring.subset_closure (Or.inr ⟨ε p, ?_⟩), fun _ _ => rfl⟩
        simp only [τ, Equiv.symm_apply_apply]

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjUniq

theorem hom_eq_of_proportional : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (T : Scheme.{0}) (φ ψ : T ⟶ Z), φ ≫ f = ψ ≫ f → (∀ z k k' i i', φ z ∈ H.U k → ψ z ∈ H.U k' → gs φ z (H.U k) ((s i).f k) * gs ψ z (H.U k') ((s i').f k') = gs φ z (H.U k) ((s i').f k) * gs ψ z (H.U k') ((s i).f k')) → φ = ψ := by
  intro R _ Z f H n s hH hs T φ ψ hf h
  choose r hr hsurj using fun i => (hs.2 i).2
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
    obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show ψ z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk] at hz
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i') ψ z hk'] at hi'
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk']
    have hu := hz.mul hi'
    rw [h z k k' i i' hk hk'] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm
    fun i z hz a => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (φ z)
  obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j => by
    have e₁ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) φ z hz hk
    have e₂ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) ψ z hz' hk'
    have u₁ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk).1 hz
    have u₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk').1 hz'
    have e := h z k k' j i hk hk'
    rw [e₁, e₂] at e
    refine (u₁.mul u₂).mul_right_cancel ?_
    linear_combination e
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, MapUniq.gs_cst f φ z _ hz, MapUniq.gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add (f := _), gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.ProjUniq
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.uniformisation_endomorphism_character_map_constant : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (aG : G ⟶ G), IsMonHom aG → ∃ h : D.toPre.X →+ D.toPre.X, ∀ e, ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X, TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map aG = t ≫ (U.gt e).i := by
  first | exact @GlobalTheory.unifPre_end_character_const | exact GlobalTheory.unifPre_end_character_const | (intros; apply GlobalTheory.unifPre_end_character_const <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  first | exact @GlobalTheory.polarisations_agree_at_level | exact GlobalTheory.polarisations_agree_at_level | (intros; apply GlobalTheory.polarisations_agree_at_level <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.UT.ExactTerm.exact_term_after_torsion | exact GlobalTheory.UT.ExactTerm.exact_term_after_torsion | (intros; apply GlobalTheory.UT.ExactTerm.exact_term_after_torsion <;> assumption)
end
