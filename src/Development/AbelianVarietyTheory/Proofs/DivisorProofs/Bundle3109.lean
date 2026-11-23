module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

theorem GlobalTheory.UPoinc.exists_endo_of_generic {Z W : Scheme.{0}} [IsIntegral W] {G : Over Z} [GrpObj G] {G₀ : Over W}
    [GrpObj G₀] (hab : IsAbelianScheme G₀) {q : W ⟶ Z} {Φ : G₀.left ⟶ G.left} (hΦ : IsGrpPullback G₀ G q Φ)
    {Ω : Type} [Field Ω] (pt : Sp Ω ⟶ W) (hd : Dense (Set.range pt)) (m : Sp Ω ⟶ Z) (hm : pt ≫ q = m)
    (hendo : ∀ f : (Over.pullback m).obj G ⟶ (Over.pullback m).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback m).map F = f)
    (f₀ : G₀ ⟶ G₀) (hf₀ : IsMonHom f₀) : ∃ F : G ⟶ G, IsMonHom F ∧ Φ ≫ F.left = f₀.left ≫ Φ := by
  have hgen := isGrpPullback_pullback G m
  have wk : pullback.fst G.hom m ≫ G.hom = (pullback.snd G.hom m ≫ pt) ≫ q := by
    rw [Category.assoc, hm, pullback.condition]
  let k : pullback G.hom m ⟶ G₀.left := hΦ.1.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pt) wk
  have hk : IsGrpPullback ((Over.pullback m).obj G) G₀ pt k :=
    hΦ.cancel (hgen.congr hm.symm (hΦ.1.lift_fst _ _ _).symm) (hΦ.1.lift_snd _ _ _)
  obtain ⟨e, he, hek⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hk f₀ hf₀
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := hendo e he
  obtain ⟨F₀, hF₀, hF₀e⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hΦ F hF
  have wθ : (pullback.fst G₀.hom pt ≫ Φ) ≫ G.hom = pullback.snd G₀.hom pt ≫ m := by
    rw [Category.assoc, hΦ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hm]
  let θ : pullback G₀.hom pt ⟶ pullback G.hom m := pullback.lift _ _ wθ
  have hθk : θ ≫ k = pullback.fst _ _ := by
    apply hΦ.1.hom_ext
    · rw [Category.assoc, hΦ.1.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hΦ.1.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  have hFm : ((Over.pullback m).map F).left ≫ pullback.fst G.hom m = pullback.fst G.hom m ≫ F.left := by
    first | exact pullback.lift_fst _ _ _ | (simp [Over.pullback, pullback.map]) | (erw [pullback.lift_fst])
  have key : F₀ = f₀ := by
    apply GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point W G₀ hab Ω pt hd
    apply hΦ.1.hom_ext
    · calc (pullback.fst G₀.hom pt ≫ F₀.left) ≫ Φ = pullback.fst G₀.hom pt ≫ Φ ≫ F.left := by
            rw [Category.assoc, hF₀e]
        _ = θ ≫ pullback.fst G.hom m ≫ F.left := by rw [← Category.assoc θ, pullback.lift_fst, Category.assoc]
        _ = θ ≫ e.left ≫ pullback.fst G.hom m := by rw [← hFm, hFe]
        _ = θ ≫ e.left ≫ k ≫ Φ := by rw [hΦ.1.lift_fst]
        _ = θ ≫ k ≫ f₀.left ≫ Φ := by rw [← Category.assoc e.left, hek, Category.assoc]
        _ = (pullback.fst G₀.hom pt ≫ f₀.left) ≫ Φ := by rw [← Category.assoc θ, hθk, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w F₀, Over.w f₀]
  exact ⟨F, hF, by rw [← hF₀e, key]⟩

theorem GlobalTheory.UPoinc.act_extends_ratModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  haveI := X₁.ar.char
  obtain ⟨hW, pt, hpt, hd⟩ := GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open X₁.o₁ X₁.Ω₁ M U₀ X₁.S.R out.u₀ hAdm.1.ne out.u₀_gen
  haveI := hW
  obtain ⟨G₁, _, α, β, hα, hβ, hL⟩ := X₁.pulled
  let s : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Sp (ratHull X₁.S.R) := pullback.snd _ _
  let G₀ : Over (pullback out.u₀ (spMap (toRat X₁.S.R))) := (Over.pullback s).obj G₁
  have h₀ : IsGrpPullback G₀ G₁ s (pullback.fst G₁.hom s) := isGrpPullback_pullback G₁ s
  let w : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Xo.XF c := s ≫ X₁.u
  have hβ₀ : IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) (pullback.fst G₁.hom s ≫ β) :=
    (h₀.comp hβ).congr (Category.assoc _ _ _).symm rfl
  obtain ⟨f₀, hf₀, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c _ w G₀ _ hβ₀
  have hα₀ := h₀.comp hα
  have wψ : (pullback.fst G₁.hom s ≫ α) ≫ X₁.ρ.P.A.hom = (G₀.hom ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ≫ out.u₀ := by
    rw [hα₀.1.w, Category.assoc, pullback.condition]
  let ψ : G₀.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift _ _ wψ
  have hψ : IsGrpPullback G₀ ((Over.pullback out.u₀).obj X₁.ρ.P.A) (pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ψ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (hα₀.congr pullback.condition.symm (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  have hΦ := hψ.comp out.cart
  have hm : pt ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R)) ≫ U₀.ι = M.pt := hpt
  have hab : IsAbelianScheme G₀ := PolPull.isAbelianScheme_of_isGrpPullback X₁.ρ.P.isAb hα₀
  choose F hF hFe using fun a => exists_endo_of_generic hab hΦ pt hd M.pt hm out.endo (f₀ a) (hf₀ a).1
  refine ⟨F, hF, ?_⟩
  intro K _ ξ₀ y hLies tK ⟨mm⟩
  obtain ⟨x', hx', hxy⟩ := hLies
  let x : Sp K ⟶ pullback out.u₀ (spMap (toRat X₁.S.R)) := pullback.lift ξ₀ x' hx'.symm
  have hxw : x ≫ w = y := by
    show x ≫ pullback.snd _ _ ≫ X₁.u = y
    rw [← Category.assoc, pullback.lift_snd, hxy]
  have mm' : SABMap tK Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _) := by rw [hxw]; exact mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hact⟩ := hT (Sp K) x tK mm'
  refine ⟨γ₀ ≫ ψ ≫ out.φ, (hγ₀.comp hΦ).congr (by rw [← Category.assoc, pullback.lift_fst]) rfl, ?_, fun a => ?_⟩
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hO := out.L.isLB
    have i1 : LBIso (out.L.L.pull out.φ) (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom out.u₀)) := ⟨out.w, out.w_gen⟩
    have i2 : LBIso (out.L.L.pull (ψ ≫ out.φ)) (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) :=
      GenSpread.lbIso_pull_comp ψ rfl (pullback.lift_fst _ _ _).symm i1
    have i3 : LBIso (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) (Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp (pullback.fst G₁.hom s) rfl rfl hL
    have i4 := LBIso.trans (pull_isLB hO _) (pull_isLB hP _) (pull_isLB hU _) i2 i3
    have i5 : LBIso (out.L.L.pull (γ₀ ≫ ψ ≫ out.φ)) (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp γ₀ rfl rfl i4
    have i6 : LBIso (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β))
        ((Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)).pull γ₀) := GenSpread.lbIso_pull_pull hU γ₀ rfl
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hO _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB hO _) i6.symm i5.symm)
  · rw [← Category.assoc, hact a, Category.assoc, Category.assoc, ← hFe a, Category.assoc]

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem lamVal_one_right_base : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift y (1 : T ⟶ B')).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (_root_.mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (𝟙 B') (1 : B' ⟶ B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.mul_one (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.mul_one (toBase hw₀ (𝟙 B'))]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift c (1 : T₀ ⟶ B')).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (𝟙 B') (1 : B' ⟶ B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.MumRigidZero

noncomputable section

namespace GlobalTheory.MumRigidZeroPull

theorem lamVal_one_left_pull : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') y).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB' f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (1 : B' ⟶ B') (𝟙 B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B') c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B' ⟶ B') (𝟙 B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB').2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZeroPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.GenOrigin

theorem jK_appTop_inj (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

theorem exists_unit_along {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w.IsGen) :
    ∃ u : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a →
      q' (t z) ∈ M'.U b → gw w (t ≫ e) z (fun _ => a) (fun _ => b) = gm t z ⊤ u := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (NormIso.mem_const M φ (e ≫ F) q hq x a ha), NormIso.mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (NormIso.gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (NormIso.gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  refine ⟨u, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  exact (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
    (gm_res t z le_top hm u))

theorem lamVal_origin_of_generic : ∀ {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → ∀ (f : Sp V ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) → ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  intro S V _ _ B B' _ _ _ _ M M' hM hM' f β β₂ w hpb hs hw hgen
  let O : Over (Sp V) := 𝟙_ (Over (Sp V))
  let e : O.left ⟶ (G2 B').left := (lift (1 : O ⟶ B') 1).left
  let q : O.left ⟶ B.left := (1 : Over.mk (O.hom ≫ f) ⟶ B).left
  let q' : O.left ⟶ B'.left := (1 : O ⟶ B').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum B (x2 B) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum B (x2 B) I.down).left) (NormIso.origin_square hpb hs O)).trans
      (congrArg (fun z => z.left) (NormIso.lift_one_psum B (T := Over.mk (O.hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)
  obtain ⟨u, hu⟩ := exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw
  have hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι),
      Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u := by
    intro T z J J' hJ hJ'
    have hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e := by
      show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left
      rw [comp_lift, MonObj.comp_one]
    have key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι),
        (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j →
        (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k →
        lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by
      rintro p _ _ rfl rfl
      rfl
    rw [hp]
    refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
      (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
    · rw [← hq I, Category.assoc, Category.assoc]
    · rw [← hq' I, Category.assoc]
  have hK : (toUnit (TK V)).left = jK V := by simpa using Over.w (toUnit (TK V))
  have h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1 := unit_ext fun x _ => by
    choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x)
    choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)
    have h := (hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)
    rw [hK] at h
    rw [map_one]
    exact (gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)
  have hu1 : u = 1 := Units.ext (jK_appTop_inj V (by
    have := congrArg Units.val h1
    simpa using this))
  intro T z J J' hJ hJ'
  rw [hval T z J J' hJ hJ', hu1]; exact map_one _

end GlobalTheory.GenOrigin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧ ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  exact @GlobalTheory.DataPos.tau_diag_pos
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem _root_.GlobalTheory.T.mumfordBundleIso_values_eq_of_rigidified : ∀ {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}, M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (w₁ w₂ : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), w₁.IsGen → w₂.IsGen → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₁ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B').left) (z : Z) J J', Good M z J → Good M' z J' → lamVal w₁ p z J J' = lamVal w₂ p z J J' := by
  first | exact @GlobalTheory.TautUniq.lamVal_eq_of_rig | exact GlobalTheory.TautUniq.lamVal_eq_of_rig | (intros; apply GlobalTheory.TautUniq.lamVal_eq_of_rig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_transport_mumfordBundleIso : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  first | exact @GlobalTheory.GenTransport.gen_transport | exact GlobalTheory.GenTransport.gen_transport | (intros; apply GlobalTheory.GenTransport.gen_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_periods_pulled_degeneration_data : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  first | exact @GlobalTheory.TauPullOn.tau_pull | exact GlobalTheory.TauPullOn.tau_pull | (intros; apply GlobalTheory.TauPullOn.tau_pull <;> assumption)
end
