module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GtTors.base_pow {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) : g.b ^ k = 1 := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => h₀.1
    | succ i ih =>
      exact fun hi => (hs ⟨i, by omega⟩).1.trans ((congrArg (· * g.b) (ih (by omega))).trans (pow_succ _ _).symm)
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [← key k (Nat.lt_succ_self k), hl']; exact hz.1

theorem GtTors.chain_val {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl

theorem GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc T ρ z J hJ

theorem val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ

theorem phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by
  intro hG R _ _ D F _ _ k g hg α mu w u p p' hw hu hp hp' hc hc' y J hJ
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ k = 1 :=
    (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _).symm.trans
      ((congrArg (preHom (fst (TF (R := R) F) D.P.A)) hg.base_pow).trans (map_one _))
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ g α mu k
  have t₃ := hg.chain_val (fst (TF (R := R) F) D.P.A) hJ mu
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ 1 1 1 t₁ (by rw [hy, C.face₂]) t₃
  have e₁ := hg.val_phi hG w hw (α + k • mu) p' hp' hc' _ (𝟙 _) y J hJ
  have e₂ := hg.val_phi hG w hw α p hp hc _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := val_delta hG k α mu u hu _ (𝟙 _) y J hJ
  have e₄ := val_delta hG k α mu u hu _ (DegPre.trPt D F g.b) y J hJ
  rw [Category.id_comp, Over.id_left, uVal_id, val_mul hJ, cPoint_add, cPoint_nsmul] at e₁
  rw [tr_fst, uVal_tr, val_mul hJ, hm] at e₂
  rw [Category.id_comp, Over.id_left, uVal_id, hm] at e₃
  rw [tr_fst, uVal_tr, hm] at e₄
  rw [hy, _root_.mul_one (cP D _ α)] at key
  refine (congrArg₂ (· * ·) e₁ e₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃
    ((congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => val p q.left y J) (trF_eq D F mu)).trans e₂)).symm)
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key' ⊢
  linear_combination (norm := abel) key'

end GlobalTheory.UU

end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UnitSec

section Gen
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  exact ⟨_, fun Z r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem exists_push {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]

end Gen

theorem unit_inv_snd {S : Scheme.{0}} (G : Over S) :
    (λ_ G).inv.left ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 G.left := by
  rw [← Over.comp_left, leftUnitor_inv_snd, Over.id_left]

theorem snd_unit_inv {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ (Over S)) G).left ≫ (λ_ G).inv.left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]

theorem famφT_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by
  fin_cases k
  · change (snd T D.P.A).left = (snd T D.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · change (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1
    simp only [padd]
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem same_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (G : Over (Spec (CommRingCat.of R))) (L : LB G.left), L.IsLB → ∀ k : ℕ, (∀ σ : H0 L k, ∃ σ', SameG σ σ') ∧ (∀ σ', ∃ σ : H0 L k, SameG σ σ') ∧ (∀ f : ∀ α, D.SecB k α, ∃ f', SameB f f') ∧ ∀ f', ∃ f : ∀ α, D.SecB k α, SameB f f' := by
  intro R _ _ D G L _ k
  refine ⟨fun σ => ?_, fun σ' => ?_, fun f => ?_, fun f' => ?_⟩
  · exact exists_pull (snd _ G).left (fun _ => (Category.comp_id _).symm) σ
  · exact exists_push (φ := fun _ : Fin 1 => 𝟙 G.left) (snd _ G).left (λ_ G).inv.left (unit_inv_snd G)
      (snd_unit_inv G) (fun _ => (Category.comp_id _).symm) σ'
  · choose f' hf' using fun α => exists_pull (snd _ D.P.A).left (famφT_eq D (𝟙_ _) α) (f α)
    exact ⟨f', hf'⟩
  · choose f hf using fun α => exists_push (snd _ D.P.A).left (λ_ D.P.A).inv.left (unit_inv_snd _)
      (snd_unit_inv _) (famφT_eq D (𝟙_ _) α) (f' α)
    exact ⟨f, hf⟩

end GlobalTheory.UnitSec
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AbPackage

theorem exists_unit_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val u r z J * (val u' r z J)⁻¹ :=
    (gm_res r z le trivial _).trans ((val_of t r z J PEmpty.elim (fun k => k.elim)).symm.trans
      ((hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_inv _ _)))))
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * val u' r z J) e.symm)

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]


omit [IsCommMonObj B] in
theorem exists_rigidified_sym {L : LB B.left} (hL : L.IsLB)
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec B)) (LB.oneGen L) := by
  have he : eSec B ≫ (ι[B]).left = eSec B :=
    congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)
  let n : B.left ⟶ B.left := (toUnit B).left ≫ eSec B
  have hn : eSec B ≫ n = eSec B := by
    rw [← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from
      congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(ι[B]).left, 𝟙 _]) (ε' := ![1, -1])
    (fun V _ k => by
      have e : n ≫ (ι[B]).left = n := by rw [Category.assoc, he]
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, e])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel, val_one]

theorem exists_cp (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (L : RigLB B)
    (h₁ : ∃ t : LB.Gen (Theta B L.L), t.IsGen)
    (h₂ : ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) :
    ∃ M : CP B, M.L = L := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised L.isLB t ht
  obtain ⟨u, hu, hr⟩ := exists_rigidified_sym L.isLB s hs
  exact ⟨CP.ofSurjective (surjective_cube hG hB) L (GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB L t' ht' hn) u hu hr, rfl⟩

theorem exists_isCPMap_of_iso (hG : GlobalFnsSt) {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B']
    [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B') {β : B'.left ⟶ B.left}
    {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen) : ∃ v, IsCPMap M' M f β hw v := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) hr M'.L.rigGen
  let b : Γ(B'.left, ⊤)ˣ := pullU B'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ B') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ β)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull β).U (fun _ => J (x.left ≫ β)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ β)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left B'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ β) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

theorem abelian_cp : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  intro hG S B _ _ hB
  refine ⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩
  exact exists_isCPMap_of_iso hG hB' M M'
    (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg

end GlobalTheory.AbPackage
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem TQ.exists_genWt_pull_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {Y : Scheme.{0}} (N : LB Y) (b : Q.B.left ⟶ Y) {χ : X} (u : LB.Gen (N.pull (Q.q.left ≫ b))) (hu : u.IsGen)
    (hw : ∀ j, IsWt Q.i _ (u.s j).val χ) : ∃ t, Q.GenWt (N.pull b) t χ := by
  have le : ∀ J : PUnit → PUnit → N.ι,
      ((N.pull b).pull Q.q.left).U J ≤ (N.pull (Q.q.left ≫ b)).U (J PUnit.unit) :=
    fun J y hy => mem_pull.2 ((mem_pull (L := N) (F := b)).1 ((mem_pull (L := N.pull b)).1 hy))
  refine ⟨⟨fun J => res (le J) (u.s (J PUnit.unit))⟩, fun i j => Geo.Tor.unit_ext fun y hy => ?_,
    fun J => (hw _).res (le J)⟩
  have hm : (𝟙 G.left : G.left ⟶ G.left) y ∈
      (N.pull (Q.q.left ≫ b)).U (i PUnit.unit) ⊓ (N.pull (Q.q.left ≫ b)).U (j PUnit.unit) := ⟨le i hy.1, le j hy.2⟩
  have h1 := congrArg (gm (𝟙 G.left) y _) (hu (i PUnit.unit) (j PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g N _ (𝟙 _) y _ _ hm.1 hm.2] at h1
  have h2 := (gm_pull_g (N.pull b) Q.q.left (𝟙 _) y i j hy.1 hy.2).trans
    (gm_pull_g N b (𝟙 _ ≫ Q.q.left) y _ _ ((mem_pull (L := N.pull b)).1 hy.1)
      ((mem_pull (L := N.pull b)).1 hy.2))
  rw [Category.assoc] at h2
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy]
  exact (gm_res (𝟙 _) y (le i) hy.1 _).trans
    (h1.trans (congrArg₂ (· * ·) h2.symm (gm_res (𝟙 _) y (le j) hy.2 _).symm))

theorem hasGen_sum_of_lbIso {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    KerPow.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  refine gen_chartPull (A' := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (h := 𝟙 Y)
    (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
    ⟨fun j => (j ∘ Sum.inl, j ∘ Sum.inr), le, fun y p q hp hq => ?_⟩ w hw
  refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
      ⟨le p hp, le q hq⟩).symm)
  refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem section_eq_of_lbIso {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {T : Over S} {Y : Scheme.{0}} {b : Y ⟶ B.left} {p : Y ⟶ T.left}
    (pb : IsPullback b p B.hom T.hom)
    (H : LBIso ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)
      ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)) :
    toUnit T ≫ c = toUnit T ≫ c' := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ (H.chartPull (chartPullIn _ _ _ _) (chartPullIn _ _ _ _))
  let x : T ⟶ B := toUnit T ≫ c
  let y : T ⟶ B := toUnit T ≫ c'
  let w : T ⊗ B ⟶ B := (fst T B ≫ y⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have key : ∀ d : 𝟙_ _ ⟶ B, w ≫ ((toUnit B ≫ d) * 𝟙 B) = translPt B ((toUnit T ≫ d) * y⁻¹) := fun d => by
    change _ = (fst T B ≫ ((toUnit T ≫ d) * y⁻¹)) * snd T B
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, _root_.mul_assoc, ← Category.assoc, ← Category.assoc,
      toUnit_unique (w ≫ toUnit B) (fst T B ≫ toUnit T)]
  have k₁ : w ≫ ((toUnit B ≫ c') * 𝟙 B) = snd T B := by
    rw [key, mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x * y⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans ?_) <;> fin_cases k
    exacts [congrArg (fun q => q.left) k₁, Category.comp_id _, congrArg (fun q => q.left) (key c), Category.comp_id _]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x * y⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK (x * y⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩)

theorem section_eq_of_isWt {S S' : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {X : Type} [AddCommGroup X] {G : Over S'} [GrpObj G] (Q : TQ G X) {f : S' ⟶ S}
    {b : Q.B.left ⟶ B.left} (pb : IsPullback b Q.B.hom B.hom f) (χ : X)
    (hc : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ)
    (hc' : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) :
    (toUnit (Over.mk f) ≫ c).left = (toUnit (Over.mk f) ≫ c').left := by
  obtain ⟨u, hu, hw⟩ := hc
  obtain ⟨u', hu', hw'⟩ := hc'
  obtain ⟨v, hv⟩ := Q.exists_genWt_pull_comp _ b u hu hw
  obtain ⟨v', hv'⟩ := Q.exists_genWt_pull_comp _ b u' hu' hw'
  have H := lbIso_of_genWt _ _ _ Q _ _ v v' χ (pull_isLB (DVR.linComb_isLB _ hL _ _) _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) hv hv'
  exact congrArg (fun q => q.left) (section_eq_of_lbIso hL hK c c' (T := Over.mk f) pb H)

theorem repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  intro _ V _ _ _ A G _ _ s t a hK χ c c' hc hc'
  have := s.cdvr.2.1
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff (IsLocalRing.maximalIdeal V) fun e => ?_)
  let f := thick V (IsLocalRing.maximalIdeal V) e
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj (F := Over.pullback f)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (t.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
end
