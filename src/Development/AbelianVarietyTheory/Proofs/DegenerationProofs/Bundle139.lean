module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory

namespace TauDescent

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {β : D'.P.A.left ⟶ D.P.A.left}

theorem cub_of_grpPullback (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) (hvg : v.IsGen) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw v ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hvg) D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A))
    (ε := thε) D'.cub.t D'.cub.isGen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ I : thK.{0}, gw v (r ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) *
        val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun I => (cubeMapOf gp).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf gp).psum_comm I.down))
    _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf gp).F3) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have C' : IsCub (cubV D'.cub y I') := isCub_cubV D'.cub hI'
      have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1
        (fun q => gw v q y (I (q ≫ β)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm
      have o : pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
      have q : e.left ≫ (cubeMapOf gp).F3 =
          (lift (pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt gp.1.w 1)
            (pushPt gp.1.w 1))).left := hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]
      refine (val_pull hI _ _ _).trans ?_
      rw [q, o]
      set_option backward.isDefEq.respectTransparency false in
        simpa only [cubV, _root_.mul_assoc, _root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] using
          (isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).face 1 1) _ (lift x (lift x' y)).left z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))


theorem tauBimult_down (hG : GlobalFnsSt) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X)
    (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hvg : v.IsGen)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hρ : RigCmp φ D D' β v)
    (gam : (TK R').left ⟶ (TK R).left) (hgam : gam ≫ jK R = jK R' ≫ spMap φ) (hψ : PsiCmp D D' β v xe gam)
    (hB : D'.TauBimult) : D.TauBimult := by
  intro a a' b
  obtain ⟨a, rfl⟩ := xe.surjective a
  obtain ⟨a', rfl⟩ := xe.surjective a'
  obtain ⟨b, rfl⟩ := xe.surjective b
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨y⟩ : Nonempty (TK R').left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R')))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB gam y (fun V hV => ?_) fun J hJ => ?_
  · obtain ⟨x, hx⟩ := hV
    rw [Subsingleton.elim (gam y) x]; exact hx
  choose J' hJ₀ using fun χ : (TK R').left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
  have hJ' : Good D'.P.L y J' := hJ₀
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk gam hgam
  let B : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, B (cP D' _ χ) = cP D _ (xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ β = ((TK R').hom ≫ spMap φ) ≫ (D.c (xe χ)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw v x.left y (J (x.left ≫ β)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (B a) (B b) (B c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_of_grpPullback hG gp v hvg (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (B a) (lift (B b) (B c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw v q y (J (q ≫ β)) (J' q))) rfl)
  have vψ : ∀ χ, val (D.psi (xe χ)) gam y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' := fun χ => by
    have h₁ : D'.xK χ ≫ β = gam ≫ D.xK (xe χ) := by
      show (jK R' ≫ (D'.c χ).left) ≫ β = gam ≫ jK R ≫ (D.c (xe χ)).left
      rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
    have e := CubTransport.val_pmaps (fun _ => h₁) (hψ χ) (𝟙 _) hJ hJ'
    rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
    exact e
  have vρ : val D.rigK gam y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have h₁ : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := by
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have o' : (toUnit (𝟙_ (Over (Sp R'))) ≫ η[D'.P.A]).left ≫ β =
          ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ≫ eSec D.P.A := o
      rw [toUnit_unit, Category.id_comp] at o'
      exact o'.trans (congrArg (· ≫ eSec D.P.A) (Category.id_comp _))
    have e := CubTransport.val_pmaps (fun _ => h₁) hρ (TK R').hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : gam ≫ (toUnit (TK R)).left = (TK R').hom ≫ spMap φ := hgam
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact e
  have key := (val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (hB a a' b) (𝟙 _)).trans (val_mul hJ' _ _ _))
  replace key := (congrArg₂ (· * ·) rfl
    (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).symm.trans key
  rw [Category.id_comp, Category.id_comp, Category.id_comp, TauPull.val_tau _ hJ', TauPull.val_tau _ hJ',
    TauPull.val_tau _ hJ'] at key
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  have cb : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D (TK R) (xe a)) (lift (cP D (TK R) (xe a')) (cP D (TK R) (xe b)))).left) gam y J =
      θ (cP D T (xe a)) (cP D T (xe a')) (cP D T (xe b)) := by
    refine (val_cub D.cub κ hJ (cP D _ (xe a)) (cP D _ (xe a')) (cP D _ (xe b))).trans ?_
    rw [comp_cP, comp_cP, comp_cP]
  refine (congrArg₂ (· * ·) rfl cb).trans ?_
  rw [← βc, ← βc, ← βc, cub, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, ← map_add (f := _), ← map_add (f := _),
    ← map_add, ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end TauDescent

theorem tauBimult_of_baseChange : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.TauBimult → D.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ _ v xe gp hv hc hρ gam hgam hψ hB =>
    TauDescent.tauBimult_down hG v xe gp hv hc hρ gam hgam hψ hB

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}

theorem inv_comp_of_isGrpPullback (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) :
    (ι[D'.P.A]).left ≫ β = β ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom gp D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ β) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem val_sym_comp (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hv₀ : v.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ β) z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := by
  have he : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hv₀) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw v (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw v (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ β)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => β ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ β) ^ (1 : ℤ) * k (𝟙 _ ≫ β) ^ (-1 : ℤ) =
        k (β ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (β ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_comp_of_isGrpPullback gp, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen β) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (spMap φ)
      rw [val_pull hI, val_one, ← he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

theorem psiEven_descend : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  intro hG R V _ _ _ _ φ D D' β v xe gp hv hc gam hgam hψ h χ
  obtain ⟨x, rfl⟩ := xe.surjective χ
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  have cx : ∀ a, D'.xK a ≫ β = gam ≫ D.xK (xe a) := fun a => by
    show (jK V ≫ (D'.c a).left) ≫ β = gam ≫ jK R ≫ (D.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  refine TauPull.corr_of_dense D.P.isLB gam z (fun U ⟨y, hy⟩ => Subsingleton.elim y (gam z) ▸ hy) fun J hJ => ?_
  choose J' hJ₀ using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have hJ' : Good D'.P.L z J' := hJ₀
  have vψ : ∀ a, val (D.psi (xe a)) gam z J =
      (gw v (D'.xK a) z (J (D'.xK a ≫ β)) (J' (D'.xK a)))⁻¹ * val (D'.psi a) (𝟙 _) z J' := fun a => by
    have := CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ hJ'
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have e := val_corr hJ' (h x) (𝟙 _)
  rw [val_mul hJ', val_pull hJ', Category.id_comp] at e
  rw [val_mul hJ, val_pull hJ, ← map_neg, vψ, vψ, ← cx, val_sym_comp hG gp hv _ z hJ hJ', ← cn]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PsiRing
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.IsoValConst
open GlobalTheory.TorusExt GlobalTheory.ArcTransport

theorem const_of_cube {A U : Type} [CommGroup A] [CommGroup U] (Ω : A → U)
    (hc : ∀ a b c, Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ = 1)
    (P : A → Prop) (hP : ∀ a b, P a → P b → Ω a = Ω b) (n : ℕ) (hd : ∀ x : A, ∃ y, y ^ n = x)
    (hg : ∀ a : A, ∃ t, t ^ n = 1 ∧ P (a * t)) (x : A) : Ω x = Ω 1 := by
  obtain ⟨h, hh⟩ : ∃ h : A → U, ∀ x, h x = Ω x / Ω 1 := ⟨_, fun _ => rfl⟩
  have h1 : h 1 = 1 := by rw [hh, div_self']
  let B : A → A →* U := fun z => MonoidHom.mk' (fun x => h (x * z) / (h x * h z)) fun x y => by
    have e := congrArg Additive.ofMul (hc x y z)
    apply Additive.ofMul.injective
    simp only [hh, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one] at e ⊢
    linear_combination (norm := abel) e
  have hB : ∀ z x, B z x = h (x * z) / (h x * h z) := fun _ _ => rfl
  have sy : ∀ z x, B z x = B x z := fun z x => by rw [hB, hB, mul_comm x, mul_comm (h x)]
  have tors : ∀ t, t ^ n = 1 → ∀ a, h (a * t) = h a * h t := fun t ht a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, sy, ← map_pow, ht, map_one]
  have pw : ∀ t, (∀ a, h (a * t) = h a * h t) → ∀ k : ℕ, h (t ^ k) = h t ^ k := fun t ht k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ k ih => rw [pow_succ, pow_succ, ht, ih]
  have key : ∀ a t, t ^ n = 1 → h (a * t) ^ n = h a ^ n := fun a t ht => by
    rw [tors t ht, mul_pow, ← pw t (tors t ht), ht, h1, _root_.mul_one]
  have kill : ∀ a, h a ^ n = 1 := fun a => by
    obtain ⟨t, ht, p⟩ := hg a
    obtain ⟨s, hs, q⟩ := hg 1
    rw [← key a t ht, hh, hP _ _ p q, ← hh, key 1 s hs, h1, one_pow]
  have mul : ∀ t a, h (a * t) = h a * h t := fun t a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, hB, div_pow, mul_pow, kill, kill, kill, _root_.mul_one, div_one]
  obtain ⟨y, rfl⟩ := hd x
  rw [← div_eq_one, ← hh, pw y (mul y), kill]

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm
end Val

theorem exists_iso_pull {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {w : LB.Iso L' (L.pull Φ)}
    (hw : w.IsGen) (h : Y ⟶ X') : ∃ w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U k →
        gw w' r z j (fun _ => k) = gw w (r ≫ h) z j k := by
  have le : ∀ p : (PUnit → L.ι) × (PUnit → L'.ι), (L.pull (h ≫ Φ)).U p.1 ⊓ (L'.pull h).U p.2 ≤
      h ⁻¹ᵁ ((L.pull Φ).U p.1 ⊓ L'.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (h ≫ Φ)).U p.1 from hy.1) :), mem_pull.1 hy.2⟩
  let w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)) := ⟨fun p => res (le p) (pullU h _ (w.s (p.1, p.2 PUnit.unit)))⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j (k : PUnit → L'.ι), Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U (k PUnit.unit) →
      gw w' r z j k = gw w (r ≫ h) z j (k PUnit.unit) := fun Z r z j k hj hk =>
    have m : r z ∈ (L.pull (h ≫ Φ)).U (fun _ => j) ⊓ (L'.pull h).U k := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
    (gm_res r z (le (fun _ => j, k)) m _).trans (gm_pull r h z _ (le (fun _ => j, k) m) _)
  refine ⟨w', (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k => v Z r z j fun _ => k⟩
  rw [v Z r z j k hj (mem_pull.1 hk), v Z r z j' k' hj' (mem_pull.1 hk'), gm_pull_g L' h r z k k' hk hk',
    ← Category.assoc]
  exact (isGen_iff _).1 hw Z (r ≫ h) z j j' _ _ hj hj' (mem_pull.1 hk :) (mem_pull.1 hk' :)

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  Units.ext ((congrArg (stalkConst z) (ν.θ_eq x y u)).trans (const_vF _ _ (good ν z)))

theorem stalk_th : ∃ ρ : ((Sp F).presheaf.stalk z)ˣ, ∀ x : N.A,
    stalkConst z (N.th x) * ρ.val = sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  ⟨_, fun x => (congrArg _ (const_vF _ _ (good ν z)).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))⟩

theorem sval_eq (s : H0 D.P.L 1) : ∃ κ : (Sp F).presheaf.stalk z, ∀ x : TF (R := R) F ⟶ D.P.A,
    sval (Z := Sp F) s x.left z ν.J = κ * sval (Z := Sp F) ν.th x.left z ν.J := by
  obtain ⟨r, hr⟩ := ν.th_gen s
  refine ⟨gs (Y := Sp F) (TF (R := R) F).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r), fun x => ?_⟩
  have m := (good ν z).mem (fun _ : Fin 1 => 𝟙 D.P.A.left) (show Sp F ⟶ _ from x.left)
  refine (congrArg (gs _ z _) (hr _)).trans ((gs_mul _ z _ m _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  refine (gs_res _ z le_top m _).trans ?_
  rw [← Over.w x]
  exact gs_pull (show Sp F ⟶ _ from x.left) D.P.A.hom z ⊤ trivial _
end Num

theorem exists_iso_val_const : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  intro hL R R' _ _ _ _ f D D' F _ _ _ N k β u ν ν' φ w gp hw he n hd hg
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) F).hom ≫ spMap f = (TF (R := R') F).hom := by
    rw [← Over.w (ν.eA 1), ← Over.w (ν'.eA 1), Category.assoc]
    exact (congrArg _ gp.1.w.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D'.P.A.hom) (he 1)))
  have hp : ∀ x : N.A, pushF gp hT (ν.eA x) = ν'.eA x := fun x => Over.OverMorphism.ext (he x)
  let Ω : N.A → ((Sp F).presheaf.stalk z)ˣ := fun x => wVal w z ν'.J ν.J (ν.eA x)
  have em : ∀ a b : N.A, ν.eA (a * b) = ν.eA a * ν.eA b := fun a b => map_mul ν.eA a b
  have e1 : ν.eA (1 : N.A) = 1 := map_one ν.eA
  have hΩ : ∀ x, Ω x = Ω 1 := by
    refine const_of_cube Ω (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ n hd hg
    · have e := thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ' hJ (ν.eA a) (ν.eA b) (ν.eA c)
      rw [hp, hp, hp, ← em, ← em, ← em, ← em, ← e1] at e
      exact mul_eq_right.1 (e.symm.trans ((stalk_θ ν' z a b c).symm.trans (stalk_θ ν z a b c)))
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D'.P.A.left) (h := φ) hw D'.P.isLB D.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν'.th
      obtain ⟨κ, hκ⟩ := sval_eq ν z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 → ρ'.val = (Ω a).val * (κ * ρ.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp F ⟶ _ from (ν.eA a).left) hJ' hJ
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp F).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ'.val = (Ω a).val * (κ * (stalkConst z (N.th a) * ρ.val)) :=
          (hρ' a).trans ((congrArg (fun q => sval (Z := Sp F) ν'.th q z ν'.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ a).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        ring
      intro a b ha hb
      have hu : IsUnit (κ * ρ.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ'.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
  obtain ⟨w', hw', hv⟩ := exists_iso_pull hw (snd (TF (R := R) F) D.P.A).left
  refine ⟨w', (stalkUnits z).symm (Ω 1), hw', fun x => (stalkConst z).injective ?_⟩
  have l : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [l]; exact hJ _
  have m₂ : (((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) ≫ φ) z ∈
      D'.P.L.U (ν'.J (ν'.eA x).left) := by rw [l, he]; exact hJ' _
  refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
    ((D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ)).U (fun _ => ν'.J (ν'.eA x).left) ⊓
      (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply, ← hΩ x]
  refine congrArg Units.val ((hv (Sp F) _ z _ _ m₂ m₁).trans ?_)
  rw [l, ← he]
  rfl

end GlobalTheory.IsoValConst
end
end
