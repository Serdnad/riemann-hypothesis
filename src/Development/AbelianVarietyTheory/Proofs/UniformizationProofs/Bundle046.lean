module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem isProper_of_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), IsProjBy f → IsProper f := by
  intro R _ X f h
  obtain ⟨N, φ, hφ, e⟩ := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver (R := R) f).1 h
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  rw [← e]
  infer_instance

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem submodule_eq_top_of_sup_smul_of_isNilpotent {A B : Type} [CommRing A] [AddCommGroup B] [Module A B]
    {J : Ideal A} (hJ : IsNilpotent J) {N : Submodule A B} (h : ⊤ ≤ N ⊔ J • ⊤) : N = ⊤ := by
  have key : ∀ n : ℕ, ⊤ ≤ N ⊔ J ^ n • (⊤ : Submodule A B) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact le_sup_right
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ((Submodule.smul_mono le_rfl h).trans ?_))
      rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
      exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨n, hn⟩ := hJ
  have := key n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_unique this

theorem surjective_eval₂Hom_of_isPushout {A B C P : CommRingCat.{0}} {α : A ⟶ B} {β : A ⟶ C} {c' : B ⟶ P}
    {d' : C ⟶ P} (h : IsPushout α β c' d') (hβ : Function.Surjective β) (hJ : IsNilpotent (RingHom.ker β.hom))
    {σ : Type} (r : σ → B) (hr : Function.Surjective (MvPolynomial.eval₂Hom d'.hom fun j => c'.hom (r j))) :
    Function.Surjective (MvPolynomial.eval₂Hom α.hom r) := by
  letI : Algebra A B := α.hom.toAlgebra
  have hN : Subalgebra.toSubmodule (MvPolynomial.aeval (R := A) r).range = ⊤ := by
    refine submodule_eq_top_of_sup_smul_of_isNilpotent hJ fun b _ => ?_
    obtain ⟨p, hp⟩ := hr (c'.hom b)
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective β.hom hβ p
    have e : c'.hom (MvPolynomial.eval₂Hom α.hom r q) = c'.hom b := by
      rw [← hp, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun c => MvPolynomial.eval₂Hom c _ q) (congrArg CommRingCat.Hom.hom h.w)
    have hk : b - MvPolynomial.eval₂Hom α.hom r q ∈ RingHom.ker c'.hom := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    rw [PrimeSection.ker_eq_map_of_isPushout h hβ] at hk
    refine Submodule.mem_sup.2 ⟨MvPolynomial.eval₂Hom α.hom r q, ⟨q, rfl⟩, _, ?_, add_sub_cancel _ _⟩
    rw [Ideal.smul_top_eq_map]
    exact hk
  intro b
  exact (hN.ge (Submodule.mem_top : b ∈ ⊤) :)

theorem surjective_specMap_of_isNilpotent {R R₀ : Type} [CommRing R] [CommRing R₀] (g : R →+* R₀)
    (hg : Function.Surjective g) (hJ : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := ⟨fun x => by
  obtain ⟨n, hn⟩ := hJ
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g : Set R) := fun a ha =>
    x.isPrime.mem_of_pow_mem n (by
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _)
  rw [← range_comap_of_surjective _ g hg] at hx
  exact hx⟩

theorem veryAmpleBy_of_isNilpotent : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (g : R →+* R₀), Function.Surjective g → IsNilpotent (RingHom.ker g) → ∀ (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (j₀ : X₀ ⟶ X), IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g)) → ∀ (H : LB X) (H₀ : LB X₀) (w : LB.Iso H₀ (H.pull j₀)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s₀ : Fin (n + 1) → LB.Sec H₀), H.IsLB → H₀.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (j₀) z ∈ (H).U k → z ∈ (H₀).U k' → gs (j₀) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → VeryAmpleBy f₀ H₀ s₀ → VeryAmpleBy f H s := by
  intro R R₀ _ _ g hg hJ X X₀ f f₀ j₀ h H H₀ w n s s₀ hH hH₀ _ hs ⟨hcov, hva⟩
  have hsurj : Surjective j₀ :=
    MorphismProperty.of_isPullback h.flip (surjective_specMap_of_isNilpotent g hg hJ)
  have loc : ∀ i, nonzeroLocus (s₀ i) = j₀ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (j₀ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hH (j₀ y)
      have e := hs i y j k hj hk
      rw [gs_stalkMap j₀ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (j₀.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hH₀ y
      have e := hs i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap j₀ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨top_le_iff.1 fun x _ => ?_, fun i => ?_⟩
  · obtain ⟨y, rfl⟩ := j₀.surjective x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (loc i).le hi⟩
  obtain ⟨haff₀, r₀, hr₀, hs₀⟩ := hva i
  have haff : IsAffineOpen (nonzeroLocus (s i)) :=
    AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hJ (CommRingCat.ofHom g) hg rfl
      ((isPullback_morphismRestrict j₀ (nonzeroLocus (s i))).paste_vert h) (loc i ▸ haff₀ :)
  have hr := fun j => ProjSpace.secRatio_spec (s i) (s j)
  refine ⟨haff, fun j => ProjSpace.secRatio (s i) (s j), hr, ?_⟩
  have e₀ : r₀ = fun j => (j₀.appLE _ _ (loc i).le).hom (ProjSpace.secRatio (s i) (s j)) := funext fun j => by
    refine (ProjSpace.eq_secRatio _ _ (hr₀ j)).trans (ProjSpace.eq_secRatio _ _ fun k => fn_ext fun y hy => ?_).symm
    obtain ⟨l, hl⟩ := exists_chart hH (j₀ y)
    have hm : j₀ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs j₀ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs j y l k hl hy.2
    have e₂ := hs i y l k hl hy.2
    have e₃ := (Geo.Tor.gw w (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    exact (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE j₀ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  subst e₀
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
    (UY := nonzeroLocus (s₀ i)) (by rw [loc]; simp)).1
    (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (nonzeroLocus (s i)) le_top)
      (CommRingCat.ofHom g) (j₀.appLE _ _ (loc i).le)
      ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f₀.appLE ⊤ (nonzeroLocus (s₀ i)) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact surjective_eval₂Hom_of_isPushout po' hg hJ _ hs₀

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefDet

theorem fn_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType p] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Spec (CommRingCat.of F) ⟶ Y, r ≫ p = 𝟙 _ → ∀ z, r z ∈ U → gs r z U a = gs r z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let r := pointOfClosedPoint p c hc
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hz : r z ∈ Y.basicOpen (a - b) := (congrArg (· ∈ Y.basicOpen (a - b)) (pointOfClosedPoint_apply p c hc z)).mpr hcW
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  have e := h r (pointOfClosedPoint_comp p c hc) z hU
  have hu : IsUnit (gs r z U (a - b)) := by
    rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
    exact hz
  rw [gs_eq r z U hU, gs_eq r z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [gs_eq r z U hU, e] at hu
  exact not_isUnit_zero hu

theorem fam_eq_of_coef_eq : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end GlobalTheory.UT.CoefDet
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Balanced
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem stalkMap_inj {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) := inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (r z)) (B := Z.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem surjective_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have := surjective_spMap β
  exact Flat.epi_of_flat_of_surjective _

theorem val_descend {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) [Flat r] [Surjective r]
    (h : ∀ z J, Good L z J → val t r z J = val t' r z J) (y : Y) (J) (hJ : Good L y J) :
    val t (𝟙 Y) y J = val t' (𝟙 Y) y J := by
  have : Epi r := Flat.epi_of_flat_of_surjective r
  obtain ⟨z, rfl⟩ := r.surjective y
  obtain ⟨J', hJ', e⟩ := exists_good L hL z (fun ψ : Y ⟶ X => r ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi r).1 e)) (fun ψ => hJ ψ)
  have := h z J' hJ'
  rw [val_of t r z J' (fun k => J (𝟙 Y ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e _),
    val_of t' r z J' (fun k => J (𝟙 Y ≫ φ' k)) (fun k => by rw [Category.id_comp]; exact e _)] at this
  have h₁ := hJ.mem φ (𝟙 Y)
  have h₂ := hJ.mem φ' (𝟙 Y)
  have k : ∀ (U : Y.Opens) (_ : r z ∈ U) (a : Γ(Y, U)ˣ),
      (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 Y) (r z) U a).val := fun U hU a => by
    rw [gm_val r z U hU, gm_val _ (r z) U hU]
    exact (Scheme.Hom.germ_stalkMap_apply r U z hU _).symm
  exact Units.ext (stalkMap_inj r z ((k _ h₁ _).symm.trans ((congrArg Units.val this).trans (k _ h₂ _))))

section Ext
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem gtExt_injective (D : DegPre R) : Function.Injective (gtExt D f hf) := fun g g' h => by
  have := epi_spMap f
  have := surjective_spMap f
  have : Flat (spMap f) := inferInstance
  refine gt_ext_val (Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)) fun χ y J hJ => ?_
  · exact ((eq_gtExt_iff f hf g _).1 rfl).1.symm.trans (((eq_gtExt_iff f hf g' _).1 h).1)
  · refine val_descend D.P.isLB (g.s χ) (g'.s χ) (spMap f) (fun z J hJ => ?_) y J hJ
    exact (gtExt_val f hf g χ hJ).symm.trans ((congrArg (fun q => charVal q χ z J) h).trans (gtExt_val f hf g' χ hJ))

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)

theorem act_unique {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E.Act g g₂) : g₁ = g₂ :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ y J hJ => (h₁.2 χ y J hJ).trans (h₂.2 χ y J hJ).symm

theorem act_gtExt {g g' : GtPtF D.toPre F} (h : E.Act g g') : E.Act (gtExt _ f hf g) (gtExt _ f hf g') := by
  refine ⟨by rw [gtExt_b, gtExt_b, h.1, Category.assoc], fun χ z J hJ => ?_⟩
  have c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (g'.s χ)
      (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ)) (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) :=
    corr_of_val D.toPre.P.isLB fun y J hJ => (h.2 χ y J hJ).trans (Eq.trans (congrArg₂ (· * ·) rfl (by
      rw [val_pull hJ, Category.id_comp])) (val_mul hJ _ _ _).symm)
  refine (gtExt_val f hf g' χ hJ).trans ((val_corr hJ c _).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (gtExt_val f hf g _ hJ).symm ((val_pull hJ _ _ _).trans ?_))))
  rw [gtExt_b]; rfl

end Ext

section Adjoint

theorem adj_add {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (a a' : G ⟶ G) (h : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ a'] L.L)) (m : ℕ) :
    LBIso (cubeLB G ![fst G G ≫ (a * 𝟙 G ^ m), snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ (a' * 𝟙 G ^ m)] L.L) := by
  have hc := PrimNorm.diff₃_ptCls (T := G ⊗ G) L.isLB ⟨c.t, c.isGen⟩
  have p : ∀ (x y : G ⊗ G ⟶ G) (m : ℕ), PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) (x ^ m) y =
      PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y ^ m := fun x y m =>
    map_pow (MonoidHom.mk' (fun x => PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y)
      fun u v => PrimNorm.diff₂_mul_left hc u v y) x m
  have q : ∀ (x : G ⊗ G ⟶ G) (b : G ⟶ G), x ≫ (b * 𝟙 G ^ m) = (x ≫ b) * x ^ m := fun x b =>
    (map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans
      (congrArg (· ^ m) (Category.comp_id x))))
  refine (PrimNorm.lbIso_iff L.isLB _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).symm))
  show PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _ = PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _
  rw [q, q, PrimNorm.diff₂_mul_left hc, PrimNorm.diff₂_mul_right hc, PrimNorm.diff₂_ptCls_adj L.isLB h, p,
    PrimNorm.diff₂_comm (fst G G) (snd G G ^ m), p, PrimNorm.diff₂_comm (snd G G)]

theorem adj_pull {B B' : Scheme.{0}} (f : B' ⟶ B) (G : Over B) [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {L' : LB ((Over.pullback f).obj G).left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : LBIso L' (L.pull (pullback.fst G.hom f))) (a a' : G ⟶ G)
    (ha : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a'] L)) :
    LBIso (cubeLB ((Over.pullback f).obj G) ![fst _ _ ≫ (Over.pullback f).map a, snd _ _] L')
      (cubeLB ((Over.pullback f).obj G) ![fst _ _, snd _ _ ≫ (Over.pullback f).map a'] L') := by
  have h := isGrpPullback_pullback G f
  let G' := (Over.pullback f).obj G
  let φ : G'.left ⟶ G.left := pullback.fst G.hom f
  have pa : ∀ (w : G ⟶ G) {T : Over B'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ (Over.pullback f).map w) = pushPt h.1.w x ≫ w := fun w T x =>
    Over.OverMorphism.ext (by
      have hw : ((Over.pullback f).map w).left ≫ φ = φ ≫ w.left := pullback.lift_fst _ _ _
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ (Over.pullback f).map a, snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ (Over.pullback f).map a'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _ _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end Adjoint

theorem exists_add_injective {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X) :
    ∃ m : ℕ, (Function.Injective fun x => h x + m • x) ∧ Function.Injective fun x => h' x + m • x := by
  have key : ∀ h : X →+ X, {m : ℕ | ¬ Function.Injective fun x => h x + m • x}.Finite := fun h => by
    let f : Module.End ℤ X := h.toIntLinearMap
    have fin : (f.charpoly.rootSet ℤ).Finite := Polynomial.rootSet_finite _ _
    refine Set.Finite.subset (fin.preimage (f := fun m : ℕ => -(m : ℤ)) (fun a _ b _ e => by simpa using e)) ?_
    intro m hm
    simp only [Function.Injective, Set.mem_setOf_eq, not_forall] at hm
    obtain ⟨x, y, e, hxy⟩ := hm
    have ev : f.HasEigenvector (-(m : ℤ)) (x - y) := by
      refine ⟨Module.End.mem_eigenspace_iff.2 ?_, sub_ne_zero.2 hxy⟩
      show h (x - y) = _
      rw [map_sub, neg_smul, natCast_zsmul, smul_sub]
      linear_combination (norm := abel) e
    have := Module.End.aeval_apply_of_hasEigenvector (p := f.charpoly) ev
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    refine (Polynomial.mem_rootSet).2 ⟨f.charpoly_monic.ne_zero, ?_⟩
    simpa [sub_ne_zero.2 hxy] using this.symm
  obtain ⟨m, hm⟩ := ((key h).union (key h')).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hm
  exact ⟨m, hm⟩

end GlobalTheory.Balanced
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_cancel_nonzero_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.expandsAt_cancel_scalar | exact GlobalTheory.expandsAt_cancel_scalar | (intros; apply GlobalTheory.expandsAt_cancel_scalar <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.relAmple_externalTensorPower_groupPower : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → RelAmple G L → RelAmple G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.relAmple_boxLB | exact GlobalTheory.relAmple_boxLB | (intros; apply GlobalTheory.relAmple_boxLB <;> assumption)
end
