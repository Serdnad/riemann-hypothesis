module

import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevels
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  ReciprocityTheory.ChartRestriction.G.Out in
noncomputable local instance (priority := high) grpObjUniformizationThick070 {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] :
    GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaLin

theorem gs_scal_comp {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_linearEquiv {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    change (val u (𝟙 Y) y J).val * sval s (𝟙 Y ≫ τ) y J = sval w.sec (𝟙 Y) y J
    rw [hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]

section Twist

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  apply GlobalTheory.VVCompare.isTwistPull_of_sv <;> assumption

end Twist

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem lift_translT {T' : Over S} (ρ : T' ⟶ T) (x : T' ⟶ A) (c : T ⟶ A) :
    lift ρ x ≫ translT A c = lift ρ ((ρ ≫ c) * x) := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem translT_comp (c d : T ⟶ A) (h : d * c = 1) : translT A c ≫ translT A d = 𝟙 _ := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, lift_translT, e, ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul,
    lift_fst_snd]

end Transl

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl

end GlobalTheory.ThetaLin

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

section Germ
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem gm_eq_of_isWt {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V) (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  have hz : z ∈ W := ⟨h₁, h₂⟩
  let ρ : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  have hW : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have inj : Function.Injective (W.ι.appLE W ⊤ hW).hom := by
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.left.presheaf.mapIso (eqToIso (by simp : W.ι ''ᵁ ⊤ = W)).op).hom).1
  have e₁ : ((ρ ≫ t) ≫ i) * (ρ ≫ g) = ρ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have a : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) k',
      ((W.ι ≫ r).appLE U ⊤ k').hom x.val = (W.ι.appLE W ⊤ hW).hom (res k (pullU r U x)).val := fun r U k x k' =>
    (congrArg (fun q => q.hom x.val) (Scheme.Hom.appLE_comp_appLE W.ι r U W ⊤ k hW)).symm
  have b : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      gm (𝟙 Z.left) z W (res k (pullU r U x)) = gm r z U x := fun r U k x =>
    (gm_res (𝟙 Z.left) z k hz _).trans ((gm_pull (𝟙 Z.left) r z U (k hz) x).trans (by simp only [Category.id_comp]))
  have h := hu _ (ρ ≫ t) (ρ ≫ g) (by rw [e₁]; exact fun x _ => x.2.1) (fun x _ => x.2.2)
  have c : ∀ (r r' : Over.mk (W.ι ≫ Z.hom) ⟶ G) (_ : r = r') k k',
      (r.left.appLE V ⊤ k).hom u.val = (r'.left.appLE V ⊤ k').hom u.val := by
    rintro r _ rfl k k'; rfl
  have d : (ρ ≫ t).left.appTop = (W.ι ≫ t.left).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [c _ _ e₁ _ (fun x _ => x.2.1), d] at h
  have h' := ((a _ V inf_le_left u _).symm.trans h).trans
    ((congrArg₂ (· * ·) (a t.left ⊤ le_top (charUnit S X χ) _) (a g.left V inf_le_right u _)).trans
      (map_mul _ _ _).symm)
  rw [← b _ V inf_le_left, ← b t.left ⊤ le_top, ← b g.left V inf_le_right, ← map_mul]
  exact congrArg _ (Units.ext (inj h'))

end Germ

section Flat
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem mem_pull_linComb {y : Y'} {j : PUnit → K → L.ι} :
    y ∈ ((LB.LinComb L φ ε).pull F).U j ↔ y ∈ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 h) k,
    fun h => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)⟩

theorem gm_pull_linComb (y : Y') (j j' : PUnit → K → L.ι) (h : y ∈ ((LB.LinComb L φ ε).pull F).U j)
    (h' : y ∈ ((LB.LinComb L φ ε).pull F).U j') :
    gm (𝟙 Y') y _ (((LB.LinComb L φ ε).pull F).g j j') =
      gm (𝟙 Y') y _ ((LB.LinComb L (fun k => F ≫ φ k) ε).g (j PUnit.unit) (j' PUnit.unit)) := by
  have a := gm_pull_g (LB.LinComb L φ ε) F (𝟙 Y') y j j' h h'
  have m : ∀ j : PUnit → K → L.ι, y ∈ ((LB.LinComb L φ ε).pull F).U j →
      (𝟙 Y' ≫ F) y ∈ LB.wchart L φ (j PUnit.unit) := fun j h => by
    rw [Category.id_comp]; exact (mem_pull (L := LB.LinComb L φ ε)).1 h
  have b := gm_linComb L φ ε (𝟙 Y' ≫ F) y (j PUnit.unit) (j' PUnit.unit) (m j h) (m j' h')
  have c := gm_linComb L (fun k => F ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit) (mem_pull_linComb.1 h)
      (mem_pull_linComb.1 h')
  simp only [Category.assoc] at b
  exact a.trans (b.trans c.symm)

def flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε) :=
  ⟨fun j => res (show LB.wchart L (fun k => F ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull F).U (fun _ => j) from
    fun _ h => (mem_pull_linComb (ε := ε) (j := fun _ => j)).2 h) (u.s fun _ => j)⟩

def unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) : LB.Gen ((LB.LinComb L φ ε).pull F) :=
  ⟨fun j => res (fun _ h => mem_pull_linComb.1 h) (v.s (j PUnit.unit))⟩

theorem flatGen_isGen {u : LB.Gen ((LB.LinComb L φ ε).pull F)} (hu : u.IsGen) : (flatGen u).IsGen := fun j j' =>
  unit_ext fun y hy => by
    have m : y ∈ ((LB.LinComb L φ ε).pull F).U (fun _ => j) ⊓ ((LB.LinComb L φ ε).pull F).U (fun _ => j') :=
      ⟨(mem_pull_linComb (j := fun _ => j)).2 hy.1, (mem_pull_linComb (j := fun _ => j')).2 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hu (fun _ => j) (fun _ => j'))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m, gm_pull_linComb y _ _ m.1 m.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

theorem unflatGen_isGen {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) : (unflatGen v).IsGen :=
  fun j j' => unit_ext fun y hy => by
    have m : y ∈ (LB.LinComb L (fun k => F ≫ φ k) ε).U (j PUnit.unit) ⊓
        (LB.LinComb L (fun k => F ≫ φ k) ε).U (j' PUnit.unit) := ⟨mem_pull_linComb.1 hy.1, mem_pull_linComb.1 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hv (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull_linComb y _ _ hy.1 hy.2]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

end Flat

section Add
variable {S A Y : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A} {F : G.left ⟶ Y}
  (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
include hF

theorem val_flatGen {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ} {u : LB.Gen ((LB.LinComb L φ ε).pull F)}
    {χ : X} (hu : ∀ j, IsWt i _ (u.s j).val χ) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} {J}
    (hJ : Good L z J) : val (flatGen u) ((t ≫ i) * g).left z J =
      gm t.left z ⊤ (charUnit S X χ) * val (flatGen u) g.left z J := by
  have e : ∀ k, J (((t ≫ i) * g).left ≫ F ≫ φ k) = J (g.left ≫ F ≫ φ k) := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  have m₁ := hJ.mem (fun k => F ≫ φ k) ((t ≫ i) * g).left
  have m₂ := hJ.mem (fun k => F ≫ φ k) g.left
  rw [funext e] at m₁
  rw [val_of _ _ z J _ e]
  exact (gm_res _ z _ m₁ _).trans ((gm_eq_of_isWt (hu fun _ k => J (g.left ≫ F ≫ φ k)) t g z
    (mem_pull_linComb.2 m₁) (mem_pull_linComb.2 m₂)).trans
    (congrArg _ (gm_res _ z _ m₂ _).symm))

theorem isWt_unflatGen (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
      val v ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val v g.left z J) (j) :
    IsWt i _ ((unflatGen v).s j).val χ := isWt_of_gm _ _ fun Z t g z m₂ => by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have m₁ : ((t ≫ i) * g).left z ∈ ((LB.LinComb L φ ε).pull F).U j := by
    have := mem_pull.1 m₂
    refine mem_pull.2 ?_
    exact (congrArg (fun q => q z) (hF Z t g)).symm ▸ this
  have le : ((LB.LinComb L φ ε).pull F).U j ≤ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
    fun _ h => mem_pull_linComb.1 h
  have e₁ := (gm_res _ z le m₁ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₁) (hJ.mem _ _))
  have e₂ := (gm_res _ z le m₂ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₂) (hJ.mem _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg _ e₂.symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (h Z t g z J hJ)
  have e : ∀ k, ((t ≫ i) * g).left ≫ F ≫ φ k = g.left ≫ F ≫ φ k := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  refine Finset.prod_congr rfl fun k _ => ?_
  beta_reduce
  rw [e]

theorem exists_genWt_add (hL : L.IsLB) {K K' K'' K₀ : Type} [Fintype K] [Fintype K'] [Fintype K''] [Fintype K₀]
    {φ : K → (Y ⟶ A)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A)} {ε'' : K'' → ℤ}
    {φ₀ : K₀ → (Y ⟶ A)} {ε₀ : K₀ → ℤ} (hw : Triv (LB.LinComb L φ₀ ε₀))
    (hs : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ A) → U),
      (∏ k, f (φ k) ^ ε k) * (∏ k, f (φ' k) ^ ε' k) * ∏ k, f (φ₀ k) ^ ε₀ k = ∏ k, f (φ'' k) ^ ε'' k) {χ χ' : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ ε).pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ)
    (h' : ∃ u : LB.Gen ((LB.LinComb L φ' ε').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ') :
    ∃ u : LB.Gen ((LB.LinComb L φ'' ε'').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val (χ + χ') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨u', hu', hχ'⟩ := h'
  obtain ⟨v, hv, H⟩ := exists_gen (φ' := fun k => F ≫ φ'' k) (ε' := ε'') hL
    (fun U _ f => (Fintype.prod_sum_type _).trans ((congrArg (· * _) (Fintype.prod_sum_type _)).trans
      (hs U fun q => f (F ≫ q)))) _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (flatGen_isGen hu'))
      (DVR.pullGen_isGen _ _ _ _ hw F))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen hF hL hv fun Z t g z J hJ => ?_⟩
  rw [H _ _ z J hJ, H _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hF,
    val_flatGen hF hχ t g hJ, val_flatGen hF hχ' t g hJ, gm_charUnit, gm_charUnit, gm_charUnit, chV_add, map_mul]
  ac_rfl

end Add

theorem TQ.mul_comp_q {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem triv_square_sections {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    [IsCommMonObj B] {L : RigLB B} (κ : CubicalStr B L) (c c' : 𝟙_ _ ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left] ![1, 1, -1, -1]) := by
  obtain ⟨w, hw⟩ := GlobalTheory.Square.triv_square (t := 𝟙 (Spec (CommRingCat.of V))) κ c c'
  let ρ : B ⟶ 𝟙_ _ ⊗ B := lift (toUnit B) (𝟙 B)
  have e : ∀ x : 𝟙_ _ ⟶ B, ρ.left ≫ (translPt (T := 𝟙_ _) B x).left = ((toUnit B ≫ x) * 𝟙 B).left := fun x => by
    rw [← Over.comp_left]
    change (ρ ≫ ((fst _ B ≫ x) * snd _ B)).left = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e' : ρ.left ≫ (snd (𝟙_ _) B).left = 𝟙 B.left := by rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left]) (ε' := ![1, 1, -1, -1]) L.isLB (fun U _ f => Finset.prod_congr rfl fun k _ => by
      fin_cases k
      exacts [congrArg (fun q => f q ^ (1 : ℤ)) (e _), congrArg (fun q => f q ^ (1 : ℤ)) e',
        congrArg (fun q => f q ^ (-1 : ℤ)) (e _), congrArg (fun q => f q ^ (-1 : ℤ)) (e _)])
    _ (DVR.pullGen_isGen _ _ _ _ hw ρ.left)
  exact ⟨u, hu⟩

theorem repWt_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  intro V _ _ _ A G _ _ s t a χ χ' c c' e h h'
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom := by
  first | exact @GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | exact GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | (intros; apply GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.EvenTriv

theorem exists_even_cubTriv_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  intro _ V _ _ _ _ A G _ _ hG gen _ P w _ hw X _ _ _ Q₀ P₀ ⟨v, hv⟩
  have hp : IsProper (pullback.snd G.hom (jK V)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK V) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hm : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V ⧸ maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  have hS := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
  have := hS.smooth
  have := hS.geomConnected
  have := Q₀.i_hom
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V ⧸ maximalIdeal V ^ (0 + 1)) X (thickObj V (maximalIdeal V) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  exact exists_even_of_surjective (surjective_cube_of_generic G hG hp) P w hw P₀
    (IsPullback.of_hasPullback G.hom (thick V (maximalIdeal V) 0)) hv Q₀.i s

end GlobalTheory.EvenTriv
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  first | exact @GlobalTheory.SecLimit.existsUnique_sec_of_compatible | exact GlobalTheory.SecLimit.existsUnique_sec_of_compatible | (intros; apply GlobalTheory.SecLimit.existsUnique_sec_of_compatible <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_unit_val_eq_mul {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ c.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← Units.mul_inv_eq_iff_eq_mul, ← Units.val_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ,
    val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem exists_psiScal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V), ∃ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a := by
  intro V _ _ _ D
  choose ga hga using fun χ : D.X =>
    DVR.exists_gen_of_local (V := V) D.P.L D.P.isLB (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have key := fun χ : D.X => exists_unit_val_eq_mul D.P.isLB (D.psi_gen χ)
    (DVR.pullGen_isGen D.P.L _ _ (ga χ) (hga χ) (toUnit (TK V)).left)
  choose c hc using key
  refine ⟨ga, fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom.toMonoidHom (c χ),
    fun χ => ⟨hga χ, fun T κ z J hJ => ?_⟩⟩
  have e : κ.left ≫ (toUnit (TK V)).left = (toUnit T).left := by
    rw [← Over.comp_left, comp_toUnit]
  refine (hc χ T.left κ.left z J hJ).trans ?_
  refine congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_pull hJ (ga χ) _ κ.left).trans (by rw [e])))
  have e₂ : scal κ.left ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (c χ).val) =
      κ.left.appTop.hom (c χ).val :=
    congrArg κ.left.appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))) _)
  refine Eq.trans ?_ (congrArg (gs (𝟙 _) z ⊤) e₂).symm
  exact (congrArg (fun q => gs q z ⊤ (c χ).val) (Category.id_comp κ.left)).symm.trans
    (gs_pull (𝟙 _) κ.left z ⊤ trivial _).symm

end GlobalTheory
end
