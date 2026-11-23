module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle106
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSections
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ
  have hodd := GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ
  have hw := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.EndData

theorem val_eq_of_flat {X Y Y' Y₁ Y₂ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₂ ⟶ X)} {ε : K → ℤ} (t₁ : LB.Gen (LB.LinComb L φ₁ ε))
    (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) (m₁ : Y ⟶ Y₁) (m₂ : Y ⟶ Y₂) (hm : ∀ k, m₁ ≫ φ₁ k = m₂ ≫ φ₂ k)
    (π : Y' ⟶ Y) [Flat π] [Surjective π]
    (h : ∀ x J, Good L x J → val t₁ (π ≫ m₁) x J = val t₂ (π ≫ m₂) x J) (y : Y) (J) (hJ : Good L y J) :
    val t₁ m₁ y J = val t₂ m₂ y J := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  let j : K → L.ι := fun k => J (m₁ ≫ φ₁ k)
  have h₁ : m₁ y ∈ LB.wchart L φ₁ j := hJ.mem φ₁ m₁
  have e₂ : ∀ k, J (m₂ ≫ φ₂ k) = j k := fun k => congrArg J (hm k).symm
  have h₂ : m₂ y ∈ LB.wchart L φ₂ j := (funext e₂ : _ = j) ▸ hJ.mem φ₂ m₂
  have key := UnifCompare.gm_eq_of_flat_surjective π (pullU m₁ (LB.wchart L φ₁ j) (t₁.s j))
    (pullU m₂ (LB.wchart L φ₂ j) (t₂.s j)) (fun x hx₁ hx₂ => by
      obtain ⟨J', hJ', e⟩ := exists_good L hL x (fun k => (π ≫ m₁) ≫ φ₁ k) j
        (fun a b e => congrArg J (by simpa only [Category.assoc, cancel_epi] using e))
        (fun k => Set.mem_iInter.1 hx₁ k)
      have := h x J' hJ'
      rw [val_of t₁ _ x J' j e, val_of t₂ _ x J' j (fun k => by
        rw [Category.assoc, ← hm, ← Category.assoc]; exact e k)] at this
      exact (gm_pull π m₁ x _ hx₁ _).trans (this.trans (gm_pull π m₂ x _ hx₂ _).symm)) (𝟙 Y) y h₁ h₂
  have k₁ := gm_pull (𝟙 Y) m₁ y _ h₁ (t₁.s j)
  have k₂ := gm_pull (𝟙 Y) m₂ y _ h₂ (t₂.s j)
  rw [Category.id_comp] at k₁ k₂
  rw [val_of t₂ m₂ y J j e₂]
  exact k₁.symm.trans (key.trans k₂)

theorem val_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    (hf : FormEq (K' := PEmpty) φ ε PEmpty.elim PEmpty.elim) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (h : ∀ e z J, Good L z J → val c (thick R I e) z J = 1) (y) (J) (hJ : Good L y J) :
    val c (𝟙 _) y J = 1 := by
  obtain ⟨c', -, hv⟩ := exists_gen hL hf c hc
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L z J →
      val c r z J = gm r z ⊤ (res le (c'.s PEmpty.elim)) := fun Z r z J hJ =>
    (hv Z r z J hJ).symm.trans ((val_of c' r z J PEmpty.elim (fun k => k.elim)).trans
      (gm_res r z le trivial _).symm)
  have one : res le (c'.s PEmpty.elim) = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (SecAlg.eq_of_forall_mk I fun e => ?_))
    have key : ((thick R I e).app ⊤).hom (res le (c'.s PEmpty.elim)).val = ((thick R I e).app ⊤).hom 1 := by
      refine fn_ext fun z hz => ?_
      choose J hJ using fun ψ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hL (ψ z)
      rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp, gs_unit _ z ⊤ trivial,
        ← ev _ _ z J hJ, h e z J hJ, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
    have nat := fun x => congrArg (fun φ => φ.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
    exact (nat _).symm.trans ((congrArg _ key).trans (nat 1))
  rw [ev _ _ y J hJ, one, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem prod_unit (D : DegPre R) (p : D.P.A ⟶ D.P.A) [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U]
    (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oε k = 1 ∧ ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  have o : η[D.P.A] ≫ p = (1 : T ⟶ D.P.A) := by simp [Hom.one_def, T]
  have e0 : ∀ k, eSec D.P.A ≫ D.Oφ p χ k = D.Oφ (1 : T ⟶ D.P.A) χ k :=
    fun k => (WeightPf.Oφ_comp η[D.P.A] p χ k).trans (congrArg (D.Oφ · χ k) o)
  simp only [e0]
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  constructor
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp

omit [IsDomain R] in
theorem map_fst (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst G'.hom (thick R I e) =
      pullback.fst G.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _

omit [IsDomain R] in
theorem trans_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)


omit [IsDomain R] in
theorem trans_map (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map a).left =
      ((Over.pullback (thick R I e)).map a).left ≫ thickMap R I e G' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, map_fst, trans_fst, map_fst, ← Category.assoc, trans_fst]
  · have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    have l : ∀ n, ((Over.pullback (thick R I n)).map a).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
      fun n => pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, l, k, k, ← Category.assoc, l]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_abelian (hL : LL) (hR : AdmBase R I) (U : UnifPre I D A G) (aG : G ⟶ G) [IsMonHom aG] :
    ∃ aB : D.toPre.P.A ⟶ D.toPre.P.A, IsMonHom aB ∧ ∀ e,
      (Over.pullback (thick R I e)).map aG ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map aB := by
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).2.exists
  have hql : ∀ e, (U.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map aG).left ≫ (U.gt e).q.left :=
    fun e => (congrArg (·.left) (hq e)).symm
  obtain ⟨aB, haB⟩ := T.exists_endomorphism_algebraising_thickenings R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _))
    (fun e => (b e).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w])
    (fun e => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      have : Epi (U.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U.gt (e + 1)).q.left, hql, ← Category.assoc (U.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.toPre.P.isAb
    D.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact hq e

theorem exists_endU : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro hL R _ _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

end GlobalTheory.EndData
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  first | exact @GlobalTheory.InducedTranslation.exists_translT_indAt | exact GlobalTheory.InducedTranslation.exists_translT_indAt | (intros; apply GlobalTheory.InducedTranslation.exists_translT_indAt <;> assumption)
end
