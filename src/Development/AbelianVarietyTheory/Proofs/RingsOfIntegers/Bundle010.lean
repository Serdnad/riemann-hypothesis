module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtDiv

theorem pG_app_eq_zero_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (W : D.P.A.left.Opens) (f : Γ(D.P.A.left, W)) :
    (g.pG.left.app W).hom f = 0 ↔ ((fstG I e D.P.A).left.app W).hom f = 0 := by
  have := g.q_flat
  have := g.q_surj

  have hpG : g.pG.left = g.q.left ≫ (fstG I e D.P.A).left := rfl
  have gen : ∀ φ : (thickObj R I e G).left ⟶ D.P.A.left, φ = g.q.left ≫ (fstG I e D.P.A).left →
      ((φ.app W).hom f = 0 ↔ ((fstG I e D.P.A).left.app W).hom f = 0) := by
    rintro φ rfl
    change (g.q.left.app ((fstG I e D.P.A).left ⁻¹ᵁ W)).hom
      (((fstG I e D.P.A).left.app W).hom f) = 0 ↔ _
    constructor
    · intro h

      apply GlobalTheory.FunDescent.app_injective g.q.left
      rw [h, map_zero]
    · intro h
      rw [h, map_zero]
  exact gen _ hpG

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (e k : ℕ) (α : D.toPre.X) (f : D.toPre.SecB k α), (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔ ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) f g := by
  intro V _ _ _ ϖ hϖ D A G _ _ U e k α f

  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim.smooth
    infer_instance

  have hiff : (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔
      ∀ j, ((fstG (maximalIdeal V) e D.toPre.P.A).left.app _).hom (f.f j) = 0 :=
    forall_congr' fun j => pG_app_eq_zero_iff (U.gt e) _ (f.f j)
  rw [hiff]
  exact GlobalTheory.ThickDiv.main V ϖ hϖ D.toPre.P.A _ f e

end GlobalTheory.ExtDiv
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PsiZero

theorem cPoint_zero' {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) :
    cP D T 0 = 1 := by
  have := cPoint_add D T 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem val_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {z : (TK R).left}
    {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (D.psi 0) (𝟙 _) z J = (val D.rig (jK R) z J)⁻¹ := by
  have C : IsCub (th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    rfl
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ 0) (cP D _ 0) (cP D _ 0)).trans ?_
    rw [Category.id_comp, cPoint_zero']
    exact C.face _ _
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
  have hp : ∀ a : D.X, a = 0 → val (D.psi a) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [vc, vτ, vτ, vρ, hp (0 + 0 + 0) (by simp), hp (0 + 0) (by simp), _root_.mul_one, mul_inv_cancel,
    _root_.one_mul] at e
  have e' := mul_eq_left.1 e.symm
  rw [← mul_inv, inv_eq_one] at e'
  exact eq_inv_of_mul_eq_one_left e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), (D.TauBimult → D.PsiIn 0 ⊤) ∧ ∀ (χ : D.X) (J J' : Ideal R), J ≤ J' → D.PsiIn χ J → D.PsiIn χ J' := by
  intro R _ _ D
  refine ⟨fun hB j V hV hle h => ?_, fun χ J J' hJ H j V hV hle h => ?_⟩
  · have c0 : (D.c 0).left = eSec D.P.A := by
      have := cPoint_zero' D (𝟙_ _)
      rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
      rw [this]; rfl
    have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
    have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
      Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
      by rw [Ideal.map_top]; trivial, fn_ext fun y hy => ?_⟩
    have hy' : jK R y ∈ V := hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
      (fun k => Set.mem_iInter.1 (h hy) k)
    have e := val_psi_zero hB hJ
    rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
      val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
      ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
    rw [Category.id_comp]
    refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
    exact congrArg Units.val ((map_inv _ _).trans e.symm)
  · obtain ⟨r, hr, e⟩ := H j V hV hle h
    exact ⟨r, Ideal.map_mono hJ hr, e⟩

end GlobalTheory.PsiZero
end
end
