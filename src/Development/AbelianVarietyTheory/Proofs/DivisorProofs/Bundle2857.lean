module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle205
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabTrans

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

section Ext

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] {k : ℕ}

theorem qkExt_trans {f : F →+* F'} {g : F' →+* F''} {p : QkPt D F k} {q : QkPt D F' k} {r : QkPt D F'' k}
    (h₁ : QkExt f p q) (h₂ : QkExt g q r) : QkExt (g.comp f) p r := by
  have hs : spMap (g.comp f) = spMap g ≫ spMap f := Geo.Tor.spMap_comp _ _
  refine ⟨h₂.1.trans h₁.1, by rw [h₂.2.1, h₁.2.1, hs, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine ((val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    (val_pull hJ _ _ _)))).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact congrArg (fun s => val (p.g.s χ) s y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hs.symm))

theorem qkExt_inj (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p q : QkPt D F k} {r : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom q r) : p = q := by
  have e := ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).symm.trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂)
  exact qk_ext (congrArg QkPt.y e :) (gtExt_injective _ f.comp_algebraMap (congrArg QkPt.g e))

theorem exists_ext (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') (p : QkPt D F k) : ∃ r, QkExt f.toRingHom p r :=
  ⟨_, (qkExt_iff hB _ f.comp_algebraMap _ _).2 rfl⟩

theorem ext_unique (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p : QkPt D F k} {r r' : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom p r') : r = r' :=
  ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂).symm

theorem exists_of_ext [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F')
    (hk : 1 ≤ k) (r : QkPt D F' k) : ∃ p : QkPt D F k, QkExt f.toRingHom p r := by
  have : CharZero F := (RingHom.charZero_iff (algebraMap (FractionRing R) F).injective).1 inferInstance
  obtain ⟨p, hp⟩ := exists_qkExt f.toRingHom f.comp_algebraMap hB GlobalTheory.firstFiveLaws.1 (Nat.cast_ne_zero.2 (by omega)) r
  exact ⟨p, (qkExt_iff hB _ f.comp_algebraMap _ _).2 hp.symm⟩

end Ext

theorem exists_lift_pt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ga : FractionRing R →+* FractionRing R'}
    {A : Over (Sp (FractionRing R))} {A' : Over (Sp (FractionRing R'))} {a : A'.left ⟶ A.left}
    (h : IsPullback a A'.hom A.hom (spMap ga)) {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F'] (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = (algebraMap _ F').comp ga)
    (x : TFK (R := R) F ⟶ A) : ∃ x' : TFK (R := R') F' ⟶ A', x'.left ≫ a = spMap f ≫ x.left := by
  have w : (spMap f ≫ x.left) ≫ A.hom = jFK (R := R') F' ≫ spMap ga := by
    rw [Category.assoc, Over.w x]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap hf).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

theorem eq_fracMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {ga : FractionRing R →+* FractionRing R'}
    (h : ∀ r, ga (algebraMap R _ r) = algebraMap R' _ (φ r)) : ga = fracMap hφ :=
  IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (h r).trans (fracMap_algebraMap hφ r).symm)

theorem exists_fib_cancel {S S' S₀ S₁ : Scheme.{0}} {A : PolAV S} {A' : PolAV S'} {A₀ : PolAV S₀} {A₁ : PolAV S₁}
    {f : S' ⟶ S} {f₀ : S₀ ⟶ S} {g : S₁ ⟶ S₀} {g' : S₁ ⟶ S'} (sq : g' ≫ f = g ≫ f₀)
    {a : A'.A.left ⟶ A.A.left} {a₀ : A₀.A.left ⟶ A.A.left} {b : A₁.A.left ⟶ A₀.A.left}
    (ha : IsGrpPullback A'.A A.A f a) (la : LBIso A'.L (A.L.pull a))
    (ha₀ : IsGrpPullback A₀.A A.A f₀ a₀) (la₀ : LBIso A₀.L (A.L.pull a₀))
    (hb : IsGrpPullback A₁.A A₀.A g b) (lb : LBIso A₁.L (A₀.L.pull b)) :
    ∃ a₁ : A₁.A.left ⟶ A'.A.left, a₁ ≫ a = b ≫ a₀ ∧ IsGrpPullback A₁.A A'.A g' a₁ ∧ LBIso A₁.L (A'.L.pull a₁) := by
  have n := (hb.comp ha₀).congr sq.symm rfl
  have w : (b ≫ a₀) ≫ A.A.hom = (A₁.A.hom ≫ g') ≫ f := n.1.w.trans (Category.assoc _ _ _).symm
  have e := ha.1.lift_fst _ _ w
  refine ⟨ha.1.lift _ _ w, e, IsGrpPullback.cancel ha (n.congr rfl e.symm) (ha.1.lift_snd _ _ w), ?_⟩
  have l₁ : LBIso (A₀.L.pull b) (A.L.pull (b ≫ a₀)) :=
    la₀.chartPull (Geo.Tor.chartPullPull A₀.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a₀) _ b fun _ => rfl)
  have l₂ : LBIso (A'.L.pull (ha.1.lift _ _ w)) (A.L.pull (b ≫ a₀)) :=
    la.chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a) _ _ fun _ => e.symm)
  exact LBIso.trans A₁.isLB (pull_isLB A.isLB _) (pull_isLB A'.isLB _)
    (LBIso.trans A₁.isLB (pull_isLB A₀.isLB _) (pull_isLB A.isLB _) lb l₁) l₂.symm

theorem nonempty_lift (K F : Type) [Field K] [Field F] [IsAlgClosed F] [Algebra K F] :
    Nonempty (AlgebraicClosure K →ₐ[K] F) := ⟨IsAlgClosed.lift⟩

end GlobalTheory.LabTrans

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCancelTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ ψ : PsiOn D' (specOf φ ⁻¹ᵁ hD.W), ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val (ψ.psi x) r z J' := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val a r z J' := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
    swap
    · have v := DegPull.pmaps_val (fun _ => hψ) H r z hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one] at v
      exact v
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc hv using key
  exact ⟨⟨a, ha, hc⟩, hv⟩

end GlobalTheory.PullDegCancelTop

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
namespace PushCub
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β)

theorem push_one {T : Over S'} : pushHom h T 1 = toUnit _ ≫ η[G] := by
  rw [map_one, Hom.one_def]

theorem face0 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 0 =
    lift (pushHom h (G2 G') 1) (lift (pushHom h (G2 G') (fst G' G')) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face1 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 1 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') 1) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face2 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 2 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') (snd G' G')) (pushHom h (G2 G') 1)) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem pushPt_lift_cubeTriplePoint_of_isGrpPullback (i : Fin 3) : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫ x3 G i =
    pushHom h (G3 G') (x3 G' i) := by
  fin_cases i <;> simp [x3] <;> rfl

theorem pushPt_lift_cubeQuadruplePoint_of_isGrpPullback (i : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ x4 G i = pushHom h (G4 G') (x4 G' i) := by
  fin_cases i <;> simp [x4] <;> rfl

theorem padd_push (i j : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ padd G (x4 G i) (x4 G j) = pushHom h (G4 G') (x4 G' i * x4 G' j) := by
  rw [map_mul, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h i, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h j]
  exact MonObj.comp_mul _ _ _

theorem cubeMapOf_thirdFace_eq_pushPt_lift : (cubeMapOf h).F3 =
    (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left := rfl

theorem sw01 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 1) (lift (x3 G 0) (x3 G 2)) =
    lift (pushHom h (G3 G') (x3 G' 1)) (lift (pushHom h (G3 G') (x3 G' 0)) (pushHom h (G3 G') (x3 G' 2))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem sw12 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 0) (lift (x3 G 2) (x3 G 1)) =
    lift (pushHom h (G3 G') (x3 G' 0)) (lift (pushHom h (G3 G') (x3 G' 2)) (pushHom h (G3 G') (x3 G' 1))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem coc1 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0 * x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc2 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (x4 G 1) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

theorem coc3 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1 * x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc4 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 1) (lift (x4 G 2) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

end PushCub
end GlobalTheory.Mum

namespace GlobalTheory.Mum

open PushCub in
theorem cubicalStr_of_push_val : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  intro S S' G G' _ _ _ _ f β h L t ht i2 c2 i3 c3 i4 c4 hup
  have hv : ∀ {T : Over S'} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (V : Over.mk (T.hom ≫ f) ⟶ G3 G)
      (a b d : T ⟶ G'), V = lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d)) →
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t V.left z J =
        GlobalTheory.CubTransport.thV t z J (pushHom h T a) (pushHom h T b) (pushHom h T d) := by
    rintro T z J V a b d rfl; rfl
  refine ⟨{ t := t, isGen := ht, face := fun i => ?_, cubeSymmetric_swap_first := ?_, cubeSymmetric_swap_last := ?_, cocycle := ?_ }, rfl⟩
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i2 c2 fun z J hJ => ?_
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [← Over.comp_left]
    have C := hup (G2 G') z J hJ
    fin_cases i
    · exact (hv _ 1 (fst G' G') (snd G' G') (face0 h)).trans (C.face _ _)
    · exact (hv _ (fst G' G') 1 (snd G' G') (face1 h)).trans (C.face₂ _ _)
    · exact (hv _ (fst G' G') (snd G' G') 1 (face2 h)).trans (C.face₃ _ _)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s01 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 1) (x3 G' 0) (x3 G' 2) (sw01 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s12 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 0) (x3 G' 2) (x3 G' 1) (sw12 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i4 c4 fun z J hJ => ?_
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).symm)
    simp only [← Over.comp_left]
    have C := hup (G4 G') z J hJ
    exact (congrArg₂ (· * ·) (hv _ _ _ _ (coc1 h)) (hv _ _ _ _ (coc2 h))).trans ((C.coc _ _ _ _).trans
      (congrArg₂ (· * ·) (hv _ _ _ _ (coc3 h)) (hv _ _ _ _ (coc4 h))).symm)

end GlobalTheory.Mum
end
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelTor

theorem sFam_charZero_affineOpen : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (U : F.X.affineOpens),
    Nontrivial Γ(F.X, U) → CharZero Γ(F.X, U) := by
  intro g n F U hU
  have hW : IsAffineOpen (U : F.X.Opens) := U.2
  have : SmoothOfRelativeDimension (g * (g + 1) / 2) F.s := F.smooth
  have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ F.s)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra
  have : Module.Flat (cycAway n) Γ(F.X, U) := h₁
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have hk' : ((k : cycAway n) : ℂ) ≠ 0 := by simpa using h0
  have hne : (k : cycAway n) ≠ 0 := fun h => hk' (by rw [h]; rfl)
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n))
    (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)
  exact one_ne_zero this

end GlobalTheory.SiegelTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepSiegel

theorem isSeparated_toZ : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  intro g n F
  obtain ⟨N, i, hi, -, e⟩ := F.qproj
  have hs : IsSeparated F.s := by
    rw [← e]
    have : IsSeparated (PSpace.str (cycAway n) N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  have ht : toZ F.X = F.s ≫ toZ (Sp (cycAway n)) := by
    first
    | exact specULiftZIsTerminal.hom_ext _ _
    | exact specZIsTerminal.hom_ext _ _
  rw [ht]
  infer_instance

end GlobalTheory.SepSiegel

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigidCyc

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_pullback : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  intro h M hM S S' s s' c o f hamp φ ψ φ₂ ψ₂ g q w l g' q' w' l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have hMu : IsUnit ((M : ℕ) : cycAway M) := isUnit_natCast (show M ≠ 0 by omega)
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (M : K) ≠ 0 := by
      have hu := hMu.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hamp hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hM hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ M = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (GlobalTheory.LowChart.isUnit_zetaAway M hM) c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigidCyc
end
