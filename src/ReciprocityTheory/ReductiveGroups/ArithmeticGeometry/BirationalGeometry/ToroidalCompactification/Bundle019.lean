module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSCompScaleS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle018
public import Mathlib.RingTheory.PowerSeries.Inverse
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] {L : RigLB A}
  {L' : RigLB A'} (c : CubicalStr A L) (c' : CubicalStr A' L') {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A') (gp : IsGrpPullback A' A f Φ) (w : LB.Iso L'.L (L.L.pull Φ)) (hwg : w.IsGen)
include hG hA hwg

theorem cub_w₀ {T' : Over S'} {z : T'.left} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (x x' y : T' ⟶ A') :
    val (L := L.L) (φ := thφ A (x3 A)) (ε := thε) c.t ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ (cubeMapOf gp).F))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * cubV c' z J' x x' y := by
  have hPG : PGen w := (isGen_iff w).1 hwg
  obtain ⟨t, ht, htv⟩ := exists_up hPG L.isLB L'.isLB (φ' := thφ A' (x3 A')) (ε := thε) c'.t c'.isGen
  have hpt : ∀ I : thK.{0}, thφ A' (x3 A') I ≫ Φ = (cubeMapOf gp).F3 ≫ thφ A (x3 A) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have hFF : FormEq (fun I => thφ A' (x3 A') I ≫ Φ) thε
      (fun I => (cubeMapOf gp).F3 ≫ thφ A (x3 A) I) thε := by
    unfold FormEq
    intro U _ h
    simp only [hpt]
  have hu := pullGen_isGen L.L (thφ A (x3 A)) thε c.t c.isGen (cubeMapOf gp).F3
  have he : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (snd A' (A' ⊗ A')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, lift_fst_snd, Over.id_left]
  have hp := surj_snd hG hA (A' ⊗ A')
  have hE : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (cubeMapOf gp).F3 =
      (lift (1 : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A)
        (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf, pushPt] <;>
      exact congrArg (fun q => q.left) (map_one (pushHom gp (A' ⊗ A')))
  have hvt : ∀ (Z0 : Scheme.{0}) (r : Z0 ⟶ (G3 A').left) (z0 : Z0) (J0 : (Z0 ⟶ A.left) → L.L.ι)
      (J0' : (Z0 ⟶ A'.left) → L'.L.ι), Good L.L z0 J0 → Good L'.L z0 J0' →
      val t r z0 J0 = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z0 (J0 ((r ≫ thφ A' (x3 A') I) ≫ Φ))
        (J0' (r ≫ thφ A' (x3 A') I)) ^ thε I) *
        val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t r z0 J0' := by
    intro Z0 r z0 J0 J0' hJ0 hJ0'
    have hm1 : r z0 ∈ LB.wchart L.L (fun I => thφ A' (x3 A') I ≫ Φ)
        (fun I => J0 (r ≫ (thφ A' (x3 A') I ≫ Φ))) :=
      Set.mem_iInter.2 fun I => hJ0 (r ≫ (thφ A' (x3 A') I ≫ Φ))
    have hm2 : r z0 ∈ LB.wchart L'.L (thφ A' (x3 A')) (fun I => J0' (r ≫ thφ A' (x3 A') I)) :=
      Set.mem_iInter.2 fun I => hJ0' (r ≫ thφ A' (x3 A') I)
    refine (htv Z0 r z0 _ _ hm1 hm2).trans ?_
    simp only [pw, val, Category.assoc] <;> rfl
  have hcov : ∀ q : A'.left, ∃ i, q ∈ L'.L.U i := fun q => by
    have hq : q ∈ (⨆ i, L'.L.U i) := by
      rw [L'.isLB.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hq
  have ac : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = 1 := by
    intro U _ a b c d
    have e1 : a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = (a * a⁻¹) * (b⁻¹ * b) * (c⁻¹ * c) * (d * d⁻¹) := by
      ac_rfl
    rw [e1]
    simp
  have key := gen_unique' L.isLB hFF (snd A' (A' ⊗ A')).left
    (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left he hp hu ht
    (fun q Jq hJq => by
      obtain ⟨J'q, hJ'q⟩ : ∃ J'q : ((A' ⊗ A').left ⟶ A'.left) → L'.L.ι, Good L'.L q J'q :=
        ⟨fun ψ => Classical.choose (hcov (ψ q)), fun ψ => Classical.choose_spec (hcov (ψ q))⟩
      obtain ⟨hh, hhd⟩ : ∃ hh : ((A' ⊗ A').left ⟶ A'.left) → ((A' ⊗ A').left.presheaf.stalk q)ˣ,
          ∀ ψ, hh ψ = gw w ψ q (Jq (ψ ≫ Φ)) (J'q ψ) := ⟨_, fun _ => rfl⟩
      have f1 : cubV c (T := Over.mk ((A' ⊗ A').hom ≫ f)) q Jq 1
          (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')) = 1 := by
        have e := val_corr hJq (c.face 0) (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))) hJq (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f2 : val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t
          (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left q J'q = 1 := by
        have e := val_corr hJ'q (c'.face 0) (lift (fst A' A') (snd A' A')).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c' (lift (fst A' A') (snd A' A')) hJ'q (pzero A' _) (x2 A' 0) (x2 A' 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f3 := prod_cub (T := A' ⊗ A') (1 : A' ⊗ A' ⟶ A') (fst A' A') (snd A' A') hh
      erw [val_pull]
      rw [hE]
      refine f1.trans ?_
      refine Eq.trans ?_ (hvt _ _ q Jq J'q hJq hJ'q).symm
      rw [f2, _root_.mul_one]
      simp only [← hhd]
      rw [f3]
      simp only [_root_.one_mul]
      exact (ac _ _ _ _).symm
      all_goals exact hJq)
    T'.left (lift x (lift x' y)).left z J hJ
  erw [val_pull] at key
  refine key.trans ((hvt _ _ z J J' hJ hJ').trans ?_)
  rfl
  all_goals exact hJ


omit hG hA hwg [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] in
def Om {M : LB A.left} {M' : LB A'.left} (w : LB.Iso M' (M.pull Φ)) {Z : Scheme.{0}} {s' : Z ⟶ S'} (z : Z)
    (J : (Z ⟶ A.left) → M.ι) (J' : (Z ⟶ A'.left) → M'.ι) (x : Over.mk s' ⟶ A') : (Z.presheaf.stalk z)ˣ :=
  gw w (show Z ⟶ _ from x.left) z (J (x.left ≫ Φ)) (J' x.left)


omit hG hA hwg in
def cubZ {Z : Scheme.{0}} {s : Z ⟶ S} (z : Z) (J : (Z ⟶ A.left) → L.L.ι) (a b d : Over.mk s ⟶ A) : (Z.presheaf.stalk z)ˣ :=
  cubV c (T := Over.mk s) z J a b d


include gp in
theorem cub_w {Z : Scheme.{0}} {s' : Z ⟶ S'} {s : Z ⟶ S} {z : Z} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J')
    (a b d : Over.mk s' ⟶ A') (a₀ b₀ d₀ : Over.mk s ⟶ A) (ha : a.left ≫ Φ = a₀.left) (hb : b.left ≫ Φ = b₀.left)
    (hd : d.left ≫ Φ = d₀.left) : cubZ c z J a₀ b₀ d₀ =
      Om w z J J' (a * b * d) * (Om w z J J' (a * b))⁻¹ * (Om w z J J' (a * d))⁻¹ * (Om w z J J' (b * d))⁻¹ * Om w z J J' a *
        Om w z J J' b * Om w z J J' d * (Om w z J J' (1 : Over.mk s' ⟶ A'))⁻¹ * cubZ c' z J' a b d := by
  have hF3 : (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 = (lift a₀ (lift b₀ d₀)).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf]
    · exact ha
    · exact hb
    · exact hd
  have h0 := cub_w₀ (c := c) (c' := c') (hG := hG) (hA := hA) (gp := gp) (w := w) (hwg := hwg)
    (hJ := hJ) (hJ' := hJ') (x := a) (x' := b) (y := d)
  rw [hF3] at h0
  refine h0.trans ?_
  congr 1
  exact prod_cub a b d (fun ψ => gw w ψ z (J (ψ ≫ (cubeMapOf gp).F)) (J' ψ))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem away_ext {S : Type} [CommRing S] (u : S) {B : Type} [CommRing B] [Algebra S B]
    (f g : Localization.Away u →ₐ[S] B) : f = g := by
  first
  | exact Subsingleton.elim f g
  | exact (IsLocalization.algHom_subsingleton (Submonoid.powers u)).elim f g
  | exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers u)
      (by ext x; simp))

abbrev Rv {S : Type} [CommRing S] (a b c : S) : Type := Localization.Away (algebraMap S (Qv a b) c)

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]



theorem pair_compat (a b t : S) (C : Chart (Gs G a)) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away t)) ⟶ G}
    {za : sp (R₀ := S) (DualNumber (Localization.Away a)) ⟶ G} {zb : sp (R₀ := S) (DualNumber (Localization.Away b)) ⟶ G}
    (ha : TanS za) (hb : TanS zb) (N₁ : ℕ)
    (har : spMap (dualMapS (qL a t)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a t) t ^ N₁)) ≫ spMap (dualMapS (qR a t)) ≫ y₀)
    (hbr : spMap (dualMapS (qL b t)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Qv b t) t ^ N₁)) ≫ spMap (dualMapS (qR b t)) ≫ y₀) :
    ∃ M : ℕ, spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qR a b)) ≫ zb := by
  have ut : IsUnit (algebraMap S (Rv a b t) t) := by
    rw [IsScalarTower.algebraMap_apply S (Qv a b) (Rv a b t)]
    exact IsLocalization.Away.algebraMap_isUnit _
  have ua : IsUnit (algebraMap S (Rv a b t) a) :=
    unit_of_map (B := Qv a b) (unit_of_map (B := Localization.Away a) (away_unit a))
  have ub : IsUnit (algebraMap S (Rv a b t) b) := unit_of_map (B := Qv a b) (isUnit_qv a b)
  obtain ⟨ρa, -⟩ : ∃ f : Qv a t →ₐ[S] Rv a b t, True := ⟨qHom a t _ ua ut, trivial⟩
  obtain ⟨ρb, -⟩ : ∃ f : Qv b t →ₐ[S] Rv a b t, True := ⟨qHom b t _ ub ut, trivial⟩
  apply tanS_away_uniq C (A := Qv a b) t (tanS_restrict _ ha) (tanS_restrict _ hb)
  have e1 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρa.comp (qR a t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qL a b) = ρa.comp (qL a t) from away_ext _ _ _,
      ← res_res, har, res_scale, map_pow, AlgHom.commutes, res_res]
  have e2 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qR a b)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρb.comp (qR b t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qR a b) = ρb.comp (qL b t) from away_ext _ _ _,
      ← res_res, hbr, res_scale, map_pow, AlgHom.commutes, res_res]
  rw [e1, e2, show ρa.comp (qR a t) = ρb.comp (qR b t) from away_ext _ _ _]


theorem tan_extend {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤) (C : ∀ k, Chart (Gs G (s k)))
    (k0 : Fin n) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away (s k0))) ⟶ G} (hy₀ : TanS y₀) :
    ∃ N : ℕ, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k0)))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ N)) ≫ y₀ := by
  classical
  have h1 : ∀ k, ∃ N : ℕ, ∃ z : sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, TanS z ∧
      spMap (dualMapS (qL (s k) (s k0))) ≫ z =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ :=
    fun k => tanS_away_lift (C k) (A := Localization.Away (s k)) (s k0) (tanS_restrict _ hy₀)
  choose N z hz hzr using h1
  let N₁ := Finset.univ.sup N
  obtain ⟨z', hz', hz'r⟩ : ∃ z' : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, (∀ k, TanS (z' k)) ∧
      ∀ k, spMap (dualMapS (qL (s k) (s k0))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N₁)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ := by
    refine ⟨fun k => spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ (N₁ - N k))) ≫ z k,
      fun k => tanS_scale _ (hz k), fun k => ?_⟩
    rw [res_scale, hzr k, map_pow, AlgHom.commutes, scale_pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := N) (Finset.mem_univ k))]
  have h3 : ∀ k l, ∃ M : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qL (s k) (s l))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qR (s k) (s l))) ≫ z' l :=
    fun k l => pair_compat (s k) (s l) (s k0) (C k) (hz' k) (hz' l) N₁ (hz'r k) (hz'r l)
  have h4 : ∃ M₀ : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫ z' k0 =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫
          spMap (scaleS (algebraMap S (Localization.Away (s k0)) (s k0) ^ N₁)) ≫ y₀ := by
    apply tanS_away_uniq (C k0) (A := Localization.Away (s k0)) (s k0) (hz' k0) (tanS_scale _ hy₀)
    rw [hz'r k0, res_scale, map_pow, AlgHom.commutes, show qR (s k0) (s k0) = qL (s k0) (s k0) from away_ext _ _ _]
  choose M hM using h3
  obtain ⟨M₀, hM₀⟩ := h4
  let M₂ := max M₀ (Finset.univ.sup fun p : Fin n × Fin n => M p.1 p.2)
  obtain ⟨w, hwd⟩ : ∃ w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G,
      ∀ k, w k = spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ M₂)) ≫ z' k :=
    ⟨_, fun _ => rfl⟩
  have hw : ∀ k, TanS (w k) := fun k => by rw [hwd]; exact tanS_scale _ (hz' k)
  have hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l := by
    intro k l
    rw [hwd k, hwd l, res_scale, res_scale (qR (s k) (s l)), map_pow, map_pow, AlgHom.commutes, AlgHom.commutes]
    exact scale_pow_mono _ (le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => M p.1 p.2) (Finset.mem_univ (k, l)))
      (le_max_right _ _)) (hM k l)
  obtain ⟨v, hv, hres⟩ := glue_tan' s hs w hw hQ
  refine ⟨M₂ + N₁, v, hv, ?_⟩
  rw [hres k0, hwd k0, scale_pow_mono _ (le_max_left _ _) hM₀, scale_pow_add]

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem admissibleBase_powerSeries (k : Type) [Field k] : Out.AdmBase (PowerSeries k) (Ideal.span {PowerSeries.X}) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  have h := ReciprocityTheory.P1.isAdicComplete_ps (R := k)
  rwa [PowerSeries.maximalIdeal_eq_span_X] at h

theorem specOf_id (R : Type) [CommRing R] : Out.specOf (RingHom.id R) = 𝟙 _ := by
  simp [Out.specOf]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}



theorem ArcWit.uwMove (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ) (ψ : W.t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = W.m.φ) (hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A W.t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = W.P.U.LG ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA W.t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback W.t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj W.t.G) W'.t.G (Out.jK R)
      (pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback W.t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst W.t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical W.m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen W.t.G bc mbc W'.P.A rfl eA mE wA W.t.PP wL' he' gL rL
  have hbcact : ∀ x, W.t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (W.t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (W.t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (W.t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (W.t.act.act x)).left ≫ pullback.fst W.t.G.hom (Out.jK R) =
          pullback.fst W.t.G.hom (Out.jK R) ≫ (W.t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (W.t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (W.t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    W.t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin W.t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG.trans W.P.bundle.symm, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
