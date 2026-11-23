module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section

namespace GlobalTheory.Mum.Two.Mix

theorem exists_frame_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) (j j' : ℕ) (g : GtPtF D₁ F) (b' : TF (R := R) F ⟶ D₂.P.A), b' = g.b ≫ b → ∀ (w : Frm D₂ F j b') (w' : Frm D₁ F j' g.b), w.IsGen → w'.IsGen → ∃ τ : LB.Gen (LB.LinComb (JN D₁ D₂) (fun i => g.b.left ≫ mixφ D₁ D₂ b α i) (MixedConv.mixε j j')), τ.IsGen ∧ ∀ z J, Good (JN D₁ D₂) z J → val τ (𝟙 _) z J = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s α) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹ := by
  intro R _ _ D₁ D₂ F _ _ b α j j' g b' hb w w' hw hw'
  subst hb
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  let ρ₁ : LB.Gen (LB.LinComb D₁.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) (fun _ => 1)) :=
    LB.pullGen D₁.P.L (fun _ : PUnit.{1} => eSec D₁.P.A) (fun _ => 1) D₁.rig (TF (R := R) F).hom
  have hρ₁ : ρ₁.IsGen := DVR.pullGen_isGen _ _ _ _ D₁.rig_gen _
  let ρ₂ : LB.Gen (LB.LinComb D₂.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) (fun _ => 1)) :=
    LB.pullGen D₂.P.L (fun _ : PUnit.{1} => eSec D₂.P.A) (fun _ => 1) D₂.rig (TF (R := R) F).hom
  have hρ₂ : ρ₂.IsGen := DVR.pullGen_isGen _ _ _ _ D₂.rig_gen _
  let t := LB.mulGen (JN D₁ D₂) _ _ _ _
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j)) (p₁.gen (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j')))
    (LB.invGen (JN D₁ D₂) _ _ (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₁.gen (g.s α))
      (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen w) (p₁.gen w'))))
  have ht : t.IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₂ _))
        (p₁.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁.gen_isGen (g.isGen α))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen hw) (p₁.gen_isGen hw'))))
  obtain ⟨τ, hτ, hv⟩ := exists_gen (jn_isLB D₁ D₂) (φ' := fun i => g.b.left ≫ mixφ D₁ D₂ b α i)
    (ε' := MixedConv.mixε j j') (fun U _ h => by
      have q₁ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) i ≫ coprod.inr) ^
          ((j : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₂.P.A).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₂ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) i ≫ coprod.inl) ^
          ((j' : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₁.P.A).left ≫ coprod.inl) ^ (j' : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₃ := prod_gt g.b α (fun f => h (f ≫ coprod.inl))
      have q₄ := CoefBasic.prod_line j (g.b ≫ b) (fun f => h (f ≫ coprod.inr))
      have q₅ := CoefBasic.prod_line j' g.b (fun f => h (f ≫ coprod.inl))
      have q₆ := prod_neg (fun i => h (Sum.elim (fun k => DegPre.gtφ D₁ F g.b α k ≫ coprod.inl)
        (Sum.elim (fun k => DegPre.lineφ D₂ F (g.b ≫ b) k ≫ coprod.inr) (fun k => DegPre.lineφ D₁ F g.b k ≫ coprod.inl)) i))
        (Sum.elim DegPre.gtε (Sum.elim (DegPre.lineε j) (DegPre.lineε j')))
        (DVR.prod_sum₂ (U := U) _ q₃ (DVR.prod_sum₂ (U := U) _ q₄ q₅))
      have q₇a : ∏ i : PUnit.{1}, h (g.b.left ≫ mixφ D₁ D₂ b α (.inl i)) ^ MixedConv.mixε j j' (.inl i) =
          h ((g.b ≫ b).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique]
        show h (g.b.left ≫ b.left ≫ coprod.inr) ^ (j : ℤ) = _
        rw [Over.comp_left, Category.assoc]
      have q₇b : ∏ i : Fin 4, h (g.b.left ≫ mixφ D₁ D₂ b α (.inr i)) ^ MixedConv.mixε j j' (.inr i) =
          ∏ i, (fun f => h (f ≫ coprod.inl)) (g.b.left ≫ D₁.famφB α i) ^ DegPre.famε j' i :=
        Finset.prod_congr rfl fun i _ => by
          show h (g.b.left ≫ D₁.famφB α i ≫ coprod.inl) ^ DegPre.famε j' i = _
          rw [← Category.assoc]
      have q₇c := MixedConv.prod_comp D₁ g.b α j' (fun f => h (f ≫ coprod.inl))
      refine Eq.trans (DVR.prod_sum₂ (U := U) _ (DVR.prod_sum₂ (U := U) _ q₁ q₂) q₆)
        (Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ q₇a (q₇b.trans q₇c)).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module) t ht
  refine ⟨τ, hτ, fun z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have g₁ := p₁.good hJ
  have g₂ := p₂.good hJ
  have e₂ : val (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j) (𝟙 _) z (rr J) = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j :=
    (map_pow _ _ _).trans (congrArg (· ^ j) ((val_pull g₂ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  have e₁ : val (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j') (𝟙 _) z (rl J) = rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' :=
    (map_pow _ _ _).trans (congrArg (· ^ j') ((val_pull g₁ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  rw [val_mul hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ,
    p₁.val_gen _ _ _ hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ]
  rw [← e₁, ← e₂]

end GlobalTheory.Mum.Two.Mix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem prod_mix_hom {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X)
    (j j' : ℕ) {U : Type} [CommGroup U] (h : (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U) :
    ∏ i, h (mixφ D₁ D₂ b α i) ^ MixedConv.mixε j j' i = h (b.left ≫ coprod.inr) ^ (j : ℤ) *
      (h (Over.Hom.left (𝟙 D₁.P.A) ≫ coprod.inl) ^ ((j' : ℤ) - 1) * h ((cP D₁ D₁.P.A α * 𝟙 D₁.P.A).left ≫ coprod.inl) *
        (h ((cP D₁ D₁.P.A α).left ≫ coprod.inl))⁻¹ * h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl)) :=
  DVR.prod_sum₂ (K := PUnit.{1}) (K' := Fin 4) (U := U) _ (Fintype.prod_unique _)
    (MixedConv.prod_comp D₁ (𝟙 _) α j' (fun q => h (q ≫ coprod.inl)))

theorem exists_mix_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  intro R _ _ D₁ D₂ b j j' χ χ' β α hα u hu f f'
  subst hα
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  obtain ⟨t, ht⟩ := exists_sec (jn_isLB D₁ D₂) (φ' := mixφ D₁ D₂ b (χ' + β)) (ε' := MixedConv.mixε j j')
    (fun U _ h => by
      have q₁ := prod_cub (cP D₁ D₁.P.A χ') (cP D₁ D₁.P.A β) (𝟙 D₁.P.A) (fun q => h (q ≫ coprod.inl))
      have q₂ := MixedConv.prod_comp D₂ b χ j (fun q => h (q ≫ coprod.inr))
      have q₃ := MixedConv.prod_comp D₁ (𝟙 _) β j' (fun q => h (q ≫ coprod.inl))
      have q₄ := prod_mix_hom D₁ D₂ b (χ' + β) j j' h
      have q₅ := MixedConv.prod_coord D₁ (𝟙 _) χ' (fun q => h (q ≫ coprod.inl))
      have q₆ := MixedConv.prod_coord_inv D₂ b χ (fun q => h (q ≫ coprod.inr))
      rw [DVR.cPoint_add] at q₄
      simp only [Over.id_left, Category.id_comp] at q₃ q₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := (Fin 4 ⊕ Fin 4) ⊕ thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₂ q₃)
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₅ q₆) q₁)) (Eq.trans ?_ q₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left, Category.id_comp]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec (p₂.sec (H1.SectionArithmetic.pullSec f b.left)) (p₁.sec f'))
      (Geo.Tor.genSec (LB.mulGen (JN D₁ D₂) _ _ _ _ u (p₁.gen (MixedConv.cubB D₁ χ' β)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (p₁.gen_isGen (MixedConv.cubB_isGen D₁ χ' β)))))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  exact (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((p₂.sval_sec _ _ z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (p₂.good hJ))) (p₁.sval_sec _ _ z hJ)))
    ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (p₁.val_gen _ _ z hJ)))))))

end GlobalTheory.Mum.Two.Mix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem imgLoc_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U U' : X.Opens} (i : U' ⟶ U)
    (j : a ⁻¹ᵁ U' ⟶ a ⁻¹ᵁ U) (y : Γ(X, U)) :
    (Y.presheaf.map j.op).hom ((a.app U).hom y) = (a.app U').hom ((X.presheaf.map i.op).hom y) := by
  have hj : j = (TopologicalSpace.Opens.map a.base).map i := Subsingleton.elim _ _
  subst hj
  have e := a.naturality i.op
  have := congrArg (fun f => f.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem imgLoc_exists {X Y : Scheme.{0}} (a : Y ⟶ X) (hinj : ∀ U : X.Opens, Function.Injective (a.app U).hom)
    (V : X.Opens) {B : Type} (W : B → X.Opens) (hV : V ≤ ⨆ b, W b) (x : Γ(Y, a ⁻¹ᵁ V))
    (hx : ∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) :
    ∃ y : Γ(X, V), (a.app V).hom y = x := by
  choose y hy using hx
  have hcov : V ≤ ⨆ b, V ⊓ W b := by
    calc V ≤ V ⊓ ⨆ b, W b := le_inf le_rfl hV
      _ = ⨆ b, V ⊓ W b := inf_iSup_eq _ _
  have key : ∀ b (U' : X.Opens) (i : U' ⟶ V ⊓ W b), (a.app U').hom ((X.presheaf.map i.op).hom (y b)) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (i.le.trans inf_le_left))).op).hom x := by
    intro b U' i
    rw [← imgLoc_app_res a i (homOfLE (extLI_preimage_mono a i.le)), hy b, extLI_res_res]
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun b => V ⊓ W b) y := by
    intro b c
    apply hinj
    exact (key b _ _).trans (key c _ _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun b => V ⊓ W b) V
    (fun b => homOfLE inf_le_left) hcov y compat
  have hcovY : a ⁻¹ᵁ V ≤ ⨆ b, a ⁻¹ᵁ (V ⊓ W b) := by
    intro z hz
    obtain ⟨b, hb⟩ := (TopologicalSpace.Opens.mem_iSup).1 (hcov hz)
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨b, hb⟩
  have hs' : ∀ b, (X.presheaf.map (homOfLE inf_le_left : V ⊓ W b ⟶ V).op).hom s = y b := hs
  refine ⟨s, ?_⟩
  refine Y.sheaf.eq_of_locally_eq' (fun b => a ⁻¹ᵁ (V ⊓ W b)) (a ⁻¹ᵁ V)
    (fun b => homOfLE (extLI_preimage_mono a inf_le_left)) hcovY _ _ (fun b => ?_)
  have h2 := imgLoc_app_res a (homOfLE inf_le_left : V ⊓ W b ⟶ V)
    (homOfLE (extLI_preimage_mono a inf_le_left)) s
  rw [hs' b, hy b] at h2
  exact h2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslRatio

theorem prod_gtφT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← comp_toUnit ρ, Category.assoc, ← MonObj.comp_mul, ← MonObj.comp_one ρ]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ (1 : T ⟶ D.P.A)).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem formEq_translate {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R)
    {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (hT : T ⟶ T) (p : T ⟶ D.P.A)
    (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (hp : hT ≫ p = (p₂ ≫ β) * (toUnit T ≫ b)) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => hT.left ≫ D.Oφ p χ k)
        (Sum.elim (fun k : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2)
          (fun k => (toUnit T).left ≫ DegPre.gtφT D _ b χ k)))
      (Sum.elim Oinvε (fun k => - Sum.elim (fun k : Fin 4 × Fin 3 => Oinvε k.1 * twε k.2) DegPre.gtε k))
      (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D.c χ) (D.c χ) k) ![1, -1, 1, -1] := by
  intro U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ twφ D₂ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k =
      ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ k : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2) ^ (Oinvε k.1 * twε k.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] :
        Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β * (toUnit T ≫ b) =
      (p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.assoc, hc, mul_right_comm]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (hT.left ≫ D.Oφ p χ k) ^ (Oinvε k) =
      (h ((p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h ((p₂ ≫ β) * (toUnit T ≫ b)).left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
    simp only [WeightPf.Oφ_comp]
    rw [Fin.prod_univ_four, ← hp]
    show h ((hT ≫ p) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (hT ≫ p).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one]
  have hS : ∏ k, h ((toUnit T).left ≫ DegPre.gtφT D _ b χ k) ^ (DegPre.gtε k) =
      (h ((toUnit T ≫ D.c χ) * (toUnit T ≫ b)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h (toUnit T ≫ b).left * (h (1 : T ⟶ D.P.A).left)⁻¹ :=
    prod_gtφT (toUnit T) b χ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, hC, hS, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, h0, h3, _root_.one_mul, Category.assoc, hc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio_gen : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ gp w hw χ₂ χ hc h hh hp
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let hT : T ⟶ T := Over.homMk h ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) hh))
  obtain ⟨t₁, ht₁, hv₁⟩ := GlobalTheory.Mum.GenTransport.exists_transport D.P.isLB D₂.P.isLB _ _ w hw _ _
    (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_translate D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) hT g.pG g₂.pG β gp.b
    (Over.OverMorphism.ext hp |>.trans (by
      show g₂.pG ≫ (β * (toUnit D₂.P.A ≫ gp.b)) = _
      rw [MonObj.comp_mul, comp_toUnit_assoc])) χ₂ χ hc
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) h) (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L _ _ (gp.s χ) ((thickObj R I e G).hom ≫ thick R I e)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ (DVR.pullGen_isGen _ _ _ _ (gp.isGen χ) _))))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r)
    ((val_inv _ r).trans (congrArg (·⁻¹) ((val_mul hJ _ _ r).trans
      (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r)))))))

end GlobalTheory.MumCmp.TranslRatio
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_generator_ratio_translationTwist_isos : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  first | exact @GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | exact GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | (intros; apply GlobalTheory.MumCmp.TwRatio.exists_twist_ratio <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  first | exact @GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | exact GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | (intros; apply GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.exists_generator_moved_to_trait_side : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen), ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  first | exact @GlobalTheory.ThetaMove.exists_down_three | exact GlobalTheory.ThetaMove.exists_down_three | (intros; apply GlobalTheory.ThetaMove.exists_down_three <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.exists_generator_moved_to_cover_side : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  first | exact @GlobalTheory.ThetaMove.exists_gen_up | exact GlobalTheory.ThetaMove.exists_gen_up | (intros; apply GlobalTheory.ThetaMove.exists_gen_up <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_integral_sections_uniformisedGroup_power : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  first | exact @GlobalTheory.Mum.sections_move_integral | exact GlobalTheory.Mum.sections_move_integral | (intros; apply GlobalTheory.Mum.sections_move_integral <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.locGen_ratio_anySec | exact GlobalTheory.Mum.locGen_ratio_anySec | (intros; apply GlobalTheory.Mum.locGen_ratio_anySec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.veryAmpleAlongPullback_transport_iso : ∀ {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn], gn ≫ pA = p → ∀ (π : Y ⟶ X) {L : LB X}, L.IsLB → ∀ {LA : LB XA}, LA.IsLB → ∀ {k m : ℕ} (b : Fin (m + 1) → H0 LA k), VeryAmpleAlong pA (𝟙 XA) LA b → ∀ (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ), (∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) → ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j = u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) → VeryAmpleAlong p π L σ := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_transport | exact GlobalTheory.Mum.veryAmpleAlong_transport | (intros; apply GlobalTheory.Mum.veryAmpleAlong_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  first | exact @GlobalTheory.Mum.exists_morphism_of_secRatio | exact GlobalTheory.Mum.exists_morphism_of_secRatio | (intros; apply GlobalTheory.Mum.exists_morphism_of_secRatio <;> assumption)
end
