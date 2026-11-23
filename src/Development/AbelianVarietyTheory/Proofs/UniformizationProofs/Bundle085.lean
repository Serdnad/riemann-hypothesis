module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjUniformizationPullback085
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  first | exact @GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | exact GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | (intros; apply GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaEigen

theorem gs_pow {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sval_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (pr : Y ⟶ X) (a b : ℤ) (l : ℕ)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => a)))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => b)))
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : sval t r z J = sval th r z J ^ l := by
  have key : ∀ j : L.ι, (t.f (fun _ => j) : Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j))) =
      (show Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) from th.f (fun _ => j)) ^ l := fun j =>
    fn_ext (V := LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) fun y hy => by
      obtain ⟨I, hI, e⟩ := exists_good L hL y (K := PUnit) (fun _ => 𝟙 Y ≫ pr) (fun _ => j) (fun _ _ _ => rfl)
        (fun _ => Set.mem_iInter.1 hy 0)
      have := hp y I hI
      rw [sval_of t _ y I (fun _ => j) (fun _ => e PUnit.unit),
        sval_of th _ y I (fun _ => j) (fun _ => e PUnit.unit)] at this
      exact this.trans (gs_pow _ y _ hy _ l).symm
  exact (congrArg (gs r z _) (key _)).trans (gs_pow r z _ (hJ.mem (fun _ : Fin 1 => pr) r) _ l)

theorem exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by
  obtain ⟨s₁, h₁⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => m) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, hm, Nat.cast_one])
    (DVR.pullSec L _ _ th τ)
  obtain ⟨s₂, h₂⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => pr) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, Nat.cast_one]) th
  obtain ⟨u, hu, h₃⟩ := exists_gen hL (K' := Fin 2) (φ' := ![m, pr]) (ε' := ![(l : ℤ), -(l : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv]
      exact _root_.mul_comm _ _)
    (DVR.scaleGen c (LB.invGen L _ _ α)) (DVR.scaleGen_isGen _ _ (DVR.invGen_isGen _ _ _ _ hα))
  have h₄ : ∀ y J, Good L y J → val u (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * (val α (𝟙 Y) y J)⁻¹ := fun y J hJ =>
    (h₃ _ _ y J hJ).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ y le_top (hJ.mem ![pr, m] (𝟙 Y)) c) (val_inv α (𝟙 Y))))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow X Y hN L hL m pr l hl s₁ s₂ u hu
    (by
      obtain ⟨y⟩ : Nonempty Y := inferInstance
      choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      refine ⟨fun _ => J (𝟙 Y ≫ pr), fun e => ?_⟩
      refine RootUnit.sec_gs_ne_zero th h0 y _ (hJ'.mem (fun _ : Fin 1 => pr) (𝟙 Y)) ?_
      refine (h₂ _ _ y J hJ').symm.trans ((congrArg (gs (𝟙 Y) y _) e).trans ?_)
      exact (RootUnit.gs_id y _ (hJ'.mem (fun _ : PUnit => pr) (𝟙 Y)) _).trans (map_zero _))
    (fun y J hJ => by
      have e₁ := (h₁ _ (𝟙 Y) y J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ th τ _ y hJ)
      have e₂ := h₂ _ (𝟙 Y) y J hJ
      have e := H y J hJ
      rw [hp y J hJ, sval_pow hL pr _ _ l th t hp _ y J hJ, gs_unit _ y ⊤ (by trivial)] at e
      refine (congrArg (· ^ l) e₁).trans (Eq.trans ?_ (congrArg₂ (fun a b => Units.val a * b ^ l) (h₄ y J hJ) e₂).symm)
      change _ = Units.val (_ * _) * _
      rw [Units.val_mul, mul_right_comm, e, mul_right_comm, Units.mul_inv, _root_.one_mul])
  exact ⟨r, hr⟩

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  intro S P F _ p l hl th t θ c h0 hp hθ
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  haveI := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  have hs : Smooth (fst (Over.mk p) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst p P.A.hom))
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hs).2.1
  let φ : F →+* Γ((Over.mk p ⊗ P.A).left, ⊤) :=
    (fst (Over.mk p) P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨r, hr⟩ := exists_gen_of_eigen (fun y => (hN y).2) P.isLB (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (by rw [← Over.comp_left, translT, lift_snd]) l hl th.sec t.sec
    (not_forall.1 fun h => h0 ((SecMod.eq_zero_iff th).2 h)) hp (Units.map φ.toMonoidHom c) θ.φ θ.isGen
    (fun y J hJ => (SecMod.sval_smul hJ (𝟙 _) c.val t).symm.trans (ThetaLin.sval_of_isTwistPull P.A hθ (𝟙 _) y hJ))
  exact P.ktriv F p θ.pt fun _ => ⟨⊤, trivial, exists_isGen_pull (translDiff P.A P.L θ.pt) r hr _⟩

end GlobalTheory.ThetaEigen

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.AddEig

theorem gen_ratio {F : Type} [CommRing F] {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (q : Y ⟶ Spec (CommRingCat.of F)) (hq : Function.Surjective q.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : F, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ (scal q c) * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hq (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (scal q c) := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem surj_fst_sq {S : Scheme.{0}} (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (T : Over S) : Function.Surjective (fst T (A ⊗ A)).left.appTop.hom := by
  let m : T ⊗ (A ⊗ A) ⟶ A ⊗ (A ⊗ T) := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  let n : A ⊗ (A ⊗ T) ⟶ T ⊗ (A ⊗ A) := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))
  have e₀ : m ≫ snd _ _ ≫ snd _ _ = fst T (A ⊗ A) := by simp [m]
  have e₁ : m ≫ n = 𝟙 _ := by ext <;> simp [m, n]
  rw [← e₀, Over.comp_left, Over.comp_left]
  refine surj_comp (fun a => ⟨n.left.appTop.hom a, ?_⟩) (surj_comp (surj_snd hG hA _) (surj_snd hG hA T))
  have e : m.left ≫ n.left = 𝟙 _ := by rw [← Over.comp_left, e₁]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem kappa_translate (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by
  have := P.isAb.comm
  let a : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ fst _ _
  let b : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ snd _ _
  let d : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := fst _ _ ≫ c
  have hd : d * d = 1 := by
    rw [← MonObj.comp_mul, ← pow_two, hc, MonObj.comp_one]
  have tp : translPt P.A c = (fst _ P.A ≫ c) * snd _ P.A := rfl
  obtain ⟨r, hr⟩ := gen_ratio (F := F) P.isLB (fun U _ h => by
      have e₁ : lift (fst _ _) a ≫ translPt P.A c = d * a := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₂ : lift (fst _ _) b ≫ translPt P.A c = d * b := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₃ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, _root_.mul_mul_mul_comm, hd,
          _root_.one_mul]
      have e₄ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
          _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← Over.comp_left, e₁, e₂, e₃, e₄, lift_snd,
        lift_snd_assoc, lift_fst]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      abel)
    (fst (Over.mk p) (P.A ⊗ P.A)).left (surj_fst_sq hG P.isAb _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) a).left) (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) b).left))
      (DVR.pullGen_isGen _ _ _ _ hκ (lift (fst _ _) (lift (d * a) (d * b))).left)) hκ
  refine ⟨r, fun T ρ x y z J hJ => ?_⟩
  have := hr _ (lift ρ (lift x y)).left z J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ThetaLin.gs_scal_comp] at this
  simp only [← Over.comp_left] at this
  have f₁ : lift ρ (lift x y) ≫ lift (fst _ _) a = lift ρ x := by simp [a]
  have f₂ : lift ρ (lift x y) ≫ lift (fst _ _) b = lift ρ y := by simp [b]
  have f₃ : lift ρ (lift x y) ≫ lift (fst _ _) (lift (d * a) (d * b)) =
      lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y)) := by simp [a, b, d, MonObj.comp_mul]
  rw [f₁, f₂, f₃, lift_fst] at this
  exact this

theorem tensor_eq_smul {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  have key := (GlobalTheory.tensor_sections_eq_zero_iff F _ L hL _ _ q q K K φ ε φ ε (n + n) (Fin.append u (fun i => (-r) • t i))
    (Fin.append u' t')).2 (by
      intro Z r₁ r₂ h z J hJ
      have ng : gs r₁ z ⊤ (scal q (-r)) = - gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) := by
        rw [ThetaLin.gs_scal_comp, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, scal, scal, map_neg, map_neg, map_neg,
          map_neg]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      simp only [SecMod.sval_smul hJ, ng, _root_.mul_assoc, neg_mul]
      rw [H Z r₁ r₂ h z J hJ, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel])
  rw [Fin.sum_univ_add] at key
  simp only [Fin.append_left, Fin.append_right, ← TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul,
    Finset.sum_neg_distrib] at key
  rw [Finset.smul_sum]
  exact add_neg_eq_zero.1 key

theorem main : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  intro hG S P F _ p th n t t' u u' ⟨κ, hκ, hA⟩ θ hθ hact
  have := P.isAb.comm
  obtain ⟨r, hr⟩ := kappa_translate hG P p κ hκ θ.pt hθ θ.φ θ.isGen
  refine ⟨r, ?_⟩
  have pt : ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u' i).sec (lift ρ y).left z J =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) *
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i).sec (lift ρ y).left z J := by
    intro T ρ x y z J hJ
    have hd : (ρ ≫ θ.pt) * (ρ ≫ θ.pt) = 1 := by
      rw [← MonObj.comp_mul, ← pow_two, hθ, MonObj.comp_one]
    have a₁ := hA T ρ x y z J hJ
    have a₂ := hA T ρ ((ρ ≫ θ.pt) * x) ((ρ ≫ θ.pt) * y) z J hJ
    rw [_root_.mul_mul_mul_comm (ρ ≫ θ.pt), hd, _root_.one_mul, _root_.mul_inv, _root_.mul_mul_mul_comm (ρ ≫ θ.pt),
      mul_inv_cancel, _root_.one_mul] at a₂
    have b := hr T ρ x y z J hJ
    have act : ∀ (v w : EA P p 2) (x : T ⟶ P.A), IsActOf P.A P.L ((2 : ℕ) : ℤ) θ v.sec w.sec →
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) w.sec (lift ρ x).left z J =
        (val (L := P.L) (K := Fin 2) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![2, -2])
          θ.φ (lift ρ x).left z J).val *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := fun v w x h => by
      refine (ThetaLin.sval_of_isTwistPull P.A h (lift ρ x).left z hJ).trans ?_
      rw [← Over.comp_left, ThetaLin.lift_translT]
    rw [a₁, ← _root_.mul_assoc, ← b, Units.val_mul, _root_.mul_assoc, ← a₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act _ _ x (hact i).1, act _ _ y (hact i).2, Units.val_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
  have : IsProper (fst (Over.mk p) P.A).left := by
    have := P.isAb.proper
    show IsProper (pullback.fst _ _)
    infer_instance
  refine tensor_eq_smul P.isLB (fst (Over.mk p) P.A).left (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left)
    (ε := fun _ => ((2 : ℕ) : ℤ)) u u' t t' r fun Z r₁ r₂ h z J hJ => ?_
  let T : Over S := Over.mk (r₁ ≫ (Over.mk p ⊗ P.A).hom)
  let R₁ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₁ rfl
  let R₂ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₂ (by
    show r₂ ≫ (Over.mk p ⊗ P.A).hom = r₁ ≫ (Over.mk p ⊗ P.A).hom
    rw [← Over.w (fst (Over.mk p) P.A), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ p) h.symm)
  have hR : R₂ ≫ fst _ _ = R₁ ≫ fst _ _ := Over.OverMorphism.ext h.symm
  have q := pt T (R₁ ≫ fst _ _) (R₁ ≫ snd _ _) (R₂ ≫ snd _ _) z J hJ
  rw [lift_comp_fst_snd, show lift (R₁ ≫ fst _ _) (R₂ ≫ snd _ _) = R₂ by rw [← hR, lift_comp_fst_snd]] at q
  exact q

end GlobalTheory.AddEig

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev CompMod (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  SecMod (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

theorem gs_scal {K : Type} [CommRing K] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (r : Z ⟶ Y) (z : Z)
    (c : K) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

theorem phiRaw_val (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') (α : D.X) (y : (DegPre.BF D F).left) (J) (hJ : Good D.P.L y J) :
    sval (s' α) (𝟙 _) y J = sval (s α) (DegPre.trPt D F g.b).left y J * (uVal D F k α g.b (𝟙 _) y J *
      val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (fst (TF (R := R) F) D.P.A).left y J).val := by
  obtain ⟨u, hu, hc⟩ := (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).1
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ
  have e' := hg.val_phi hG w hw α u hu hc _ (𝟙 _) y J hJ
  rw [Category.id_comp, Over.id_left] at e'
  rw [Category.id_comp] at e
  exact (congrArg (fun β => sval (s' β) (𝟙 _) y J) (add_zero α)).symm.trans
    (e.trans (congrArg (fun q => _ * Units.val q) e'))

theorem phiRaw_smul (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s s' t t' : ∀ α, CompMod D F k α} (h : PhiRaw D F k 0 g w (fun α => (s α).sec) fun α => (s' α).sec)
    (h' : PhiRaw D F k 0 g w (fun α => (t α).sec) fun α => (t' α).sec) (α : D.X) (c : F) (e : s α = c • t α) :
    s' α = c • t' α := by
  refine SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)
  have a := phiRaw_val hG hg hw h α y J hJ
  have b := phiRaw_val hG hg hw h' α y J hJ
  have t₁ : (DegPre.trPt D F g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left :=
    (congrArg (fun q => q.left) (tr_fst D F g.b)).trans (Category.id_comp _).symm
  change sval (s' α).sec (𝟙 _) y J = sval (c • t' α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, a, b, e, SecMod.value_smul hJ, gs_scal, gs_scal, _root_.mul_assoc]
  exact congrArg (fun q => gs q y ⊤ _ * _) t₁

theorem phiRaw_torus (hG : GlobalFnsSt) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) {g : GtPtF D F}
    (hτ : g = torusPt D F (Additive.ofMul τ)) (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ s s' : ∀ α, CompMod D F k α, PhiRaw D F k 0 g w (fun α => (s α).sec) (fun α => (s' α).sec) →
      ∀ α, s' α = ((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α := by
  have hb : g.b = 1 := hτ ▸ torusPt_b _
  obtain ⟨y₀, J₀, hJ₀⟩ := exists_good_chart D F
  obtain ⟨c, hc⟩ := (stalkUnits (F := F) y₀).surjective (val w (𝟙 _) y₀ J₀)
  have vv : ∀ (u : Fˣ) {Z : Scheme.{0}} (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val (GlobalTheory.UU.scaleGen (unitOn u) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) r z J = gm r z ⊤ (unitOn u) :=
    fun u Z r z J hJ => (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))
  have hwv : ∀ y J, Good D.P.L y J → val w (𝟙 _) y J = stalkUnits (F := F) y c := fun y J hJ => by
    obtain rfl := pt_eq y₀ y
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) hw
      (GlobalTheory.UU.scaleGen_isGen (unitOn c) oneGen_isGen) hJ₀ hJ (hc.symm.trans ((vv c _ _ _ hJ₀).trans (gm_unitOn _ c)).symm)).trans
      ((vv c _ _ _ hJ).trans (gm_unitOn _ c))
    rw [Fin.prod_univ_two, Fintype.prod_empty]
    show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ)) = 1
    rw [hb, zpow_neg, mul_inv_cancel]
  refine ⟨c, fun s s' h α => SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)⟩
  have cr : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s α) w)
      (GlobalTheory.UU.scaleGen (unitOn (c * τ (Multiplicative.ofAdd α))) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) :=
    corr_of_val D.P.isLB fun y J hJ => by
      have e : charVal g α y J = stalkUnits (F := F) y (τ (Multiplicative.ofAdd α)) := hτ ▸ torusPt_val τ α hJ
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e (hwv y J hJ))).trans
        (Eq.trans ?_ ((vv _ _ _ _ hJ).trans (gm_unitOn _ _)).symm)
      exact (mul_comm _ _).trans (map_mul (stalkUnits (F := F) y) _ _).symm
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have u₁ : uVal D F k α g.b (𝟙 _) y J = 1 := by
    rw [uVal_id, hb, MonObj.comp_one, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  have t₁ : DegPre.trPt D F g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tr_fst, Category.id_comp]
    · rw [tr_pr, hb, MonObj.comp_one, _root_.mul_one, Category.id_comp]
  have a := phiRaw_val hG hg hw h α y J hJ
  rw [u₁, _root_.one_mul, t₁, Over.id_left, (val_corr hJ cr _).trans (vv _ _ _ _ hJ)] at a
  change sval (s' α).sec (𝟙 _) y J = sval (((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, gs_scal, Category.id_comp, mul_comm]
  exact a.trans (congrArg _ (gs_unit _ y ⊤ trivial _).symm)

theorem exists_conj {K K' E M : Type} [CommRing K] [CommRing K'] [AddCommGroup E] [Module K E] [AddCommGroup M]
    [Module K' M] (σ : K ≃+* K') (j : E ≃+ M) (hj : ∀ (c : K) v, j (c • v) = σ c • j v) (Φ : M ≃ₗ[K'] M) :
    ∃ Ψ : E ≃ₗ[K] E, ∀ v, j (Ψ v) = Φ (j v) :=
  ⟨{ j.trans (Φ.toAddEquiv.trans j.symm) with
      map_smul' := fun c v => j.injective (by
        show j (j.symm (Φ (j (c • v)))) = j (c • j.symm (Φ (j v)))
        rw [hj, hj, map_smul, j.apply_symm_apply, j.apply_symm_apply]) }, fun _ => j.apply_symm_apply _⟩

abbrev TorsPt {S : Scheme.{0}} (P : PolAV S) (T : Over S) (N : ℕ) : Subgroup (T ⟶ P.A) :=
  (powMonoidHom N : (T ⟶ P.A) →* (T ⟶ P.A)).ker

theorem exists_projective_rep (hL : Laws) (hL₂ : Laws2) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {F : Type} [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt P (Over.mk p) N → (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃ₗ[F]
        SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))))
      (e : TorsPt P (Over.mk p) N → TorsPt P (Over.mk p) N → Fˣ),
      Module.finrank F (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))) = N ^ P.g ∧
      (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL₂ S P F p N hN
  let σ : F ≃+* Γ((Over.mk p).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃+ SecM P.A P.L N (Over.mk p) :=
    { toFun := fun v => SecM.ofSec P.A v.sec
      invFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (c • v) = σ c • j v := fun _ _ => rfl
  let u : Γ((Over.mk p).left, ⊤)ˣ ≃* Fˣ := Units.mapEquiv σ.symm.toMulEquiv
  have hu : ∀ r, σ (u r : F) = r.val := fun r => σ.apply_symm_apply _
  have hd := (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv σ j σ.bijective hj)).trans h₁
  choose Ψ hΨ using fun a : TorsPt P (Over.mk p) N => exists_conj σ j hj (Φ a)
  refine ⟨Ψ, fun a b => u (e a b), hd, fun a => ?_, fun a b => ?_, fun a b v => ?_,
    fun a h => Subtype.ext (h₅ a fun b => u.injective ((h b).trans (map_one u).symm))⟩
  · obtain ⟨θ, h, h'⟩ := h₂ a
    refine ⟨θ, h, fun v => ?_⟩
    have := h' (j v)
    rw [← hΨ] at this
    exact this
  · obtain ⟨r, hr⟩ := h₃ a b (a * b : TorsPt P (Over.mk p) N) rfl
    refine ⟨u r, fun v => j.injective ?_⟩
    rw [hj, hΨ, hΨ, hΨ, hu]
    exact hr (j v)
  · apply j.injective
    beta_reduce
    rw [hj, hΨ, hΨ, hΨ, hΨ]
    exact ((h₄ a b).2 (j v)).trans (congrArg (fun c => c • Φ b (Φ a (j v))) (hu (e a b)).symm)

end GlobalTheory.UU.Weight
end
end
