module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle007
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootUnit

open TopologicalSpace

theorem gs_id {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = (Y.presheaf.germ U y h).hom a := gs_eq (𝟙 Y) y U h a

theorem gs_ne_zero {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))

theorem exists_unit_of_stalks {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy

theorem exists_unit_of_stalks' {Y : Scheme.{0}} [IsIntegral Y] (W U V : Y.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, U)) (b : Γ(Y, V)) (hb : ∀ y ∈ W, gs (𝟙 Y) y V b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y U a = v.val * gs (𝟙 Y) y V b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y U a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y V b := by
  obtain ⟨r, hr⟩ := exists_unit_of_stalks W ((Y.presheaf.map (homOfLE hU).op).hom a)
    ((Y.presheaf.map (homOfLE hV).op).hom b)
    (fun y hy => by rw [gs_res (𝟙 Y) y hV hy]; exact hb y hy)
    (fun y hy => by rw [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy]; exact h y hy)
  refine ⟨r, fun y hy => ?_⟩
  have := hr y hy
  rwa [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy] at this

theorem sec_gs_ne_zero {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]

theorem trF_pull {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_gen_of_pow : ∀ (X Y : Scheme.{0}) [IsIntegral Y], (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → ∀ (L : LB X), L.IsLB → ∀ (f₁ f₂ : Y ⟶ X) (l : ℕ), 1 ≤ l → ∀ (s₁ : LB.Sec (L.pull f₁)) (s₂ : LB.Sec (L.pull f₂)) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![(l : ℤ), -(l : ℤ)])), u.IsGen → (∃ j, s₂.f j ≠ 0) → (∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J ^ l = (val u (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J ^ l) → ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![1, -1]), r.IsGen ∧ ∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J = (val r (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J := by
  intro X Y _ hN L hL f₁ f₂ l hl s₁ s₂ u _ hs H
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₂ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have main : ∀ j : Fin 2 → L.ι, ∃ r : Γ(Y, LB.wchart L ![f₁, f₂] j)ˣ, ∀ y ∈ LB.wchart L ![f₁, f₂] j,
      gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0)) (s₁.f fun _ => j 0) =
        (gm (𝟙 Y) y _ r).val *
          gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1)) (s₂.f fun _ => j 1) := by
    intro j
    exact exists_unit_of_stalks' (LB.wchart L ![f₁, f₂] j) _ _ (l₁ j) (l₂ j) _ _
      (fun y hy => sec_gs_ne_zero s₂ hs y _ (l₂ j hy))
      (fun y hy => by
        choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
        have hJ' : Good L y J := hJ
        haveI := hN y
        have as : Associated (sval s₂ (𝟙 Y) y J) (sval s₁ (𝟙 Y) y J) :=
          (Associated.pow_iff (by omega : l ≠ 0)).1 ⟨val u (𝟙 Y) y J, (_root_.mul_comm _ _).trans (H y J hJ').symm⟩
        obtain ⟨v, hv⟩ := as
        have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ j hy) (hJ'.mem (K := PUnit) (fun _ => f₁) (𝟙 Y))
        have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ j hy) (hJ'.mem (K := PUnit) (fun _ => f₂) (𝟙 Y))
        change _ = _ * sval s₁ (𝟙 Y) y J at e₁
        change _ = _ * sval s₂ (𝟙 Y) y J at e₂
        rw [e₁, e₂, ← hv]
        generalize trF (L := L) (K := PUnit) (fun _ => f₁) (fun _ => 1) (𝟙 Y) y _ _ = t₁
        generalize trF (L := L) (K := PUnit) (fun _ => f₂) (fun _ => 1) (𝟙 Y) y _ _ = t₂
        refine ⟨t₁ * v * t₂⁻¹, ?_⟩
        rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
        ring)
  choose r hr using main
  refine ⟨⟨r⟩, fun i j => unit_ext fun y hy => ?_, fun y J hJ => hr _ y (hJ.mem ![f₁, f₂] (𝟙 Y))⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) (gm_res _ y _ hy _))).symm)
  have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ i hy.1) (l₂ j hy.2)
  have hb := sec_gs_ne_zero s₂ hs y _ (l₂ j hy.2)
  rw [hr i y hy.1, hr j y hy.2, e₂, trF_pull, trF_pull, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul] at e₁
  have e := Units.ext (mul_right_cancel₀ hb e₁)
  rw [Fin.prod_univ_two]
  change gm (𝟙 Y) y _ (r i) = gm (𝟙 Y ≫ f₁) y _ (L.g (i 0) (j 0)) ^ (1 : ℤ) *
    gm (𝟙 Y ≫ f₂) y _ (L.g (i 1) (j 1)) ^ (-1 : ℤ) * gm (𝟙 Y) y _ (r j)
  rw [zpow_one, zpow_neg_one, mul_right_comm, ← e, mul_inv_cancel_right]

end GlobalTheory.RootUnit
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPullIso

theorem gs_sec_trans {X Z : Scheme.{0}} {L : LB X} (s : LB.Sec L) (r : Z ⟶ X) (z : Z) {j j' : L.ι}
    (hj : r z ∈ L.U j) (hj' : r z ∈ L.U j') :
    gs r z (L.U j) (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z (L.U j') (s.f j') := by
  have hm : r z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  have e : r z ∈ X.basicOpen a ↔ z ∈ Z.basicOpen ((r.app U).hom a) := by
    rw [← Scheme.preimage_basicOpen]; rfl
  rw [e]
  exact (Scheme.mem_basicOpen Z _ z h).symm

theorem exists_pull {X X' : Scheme.{0}} (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ))
    (hH : H.IsLB) (hH' : H'.IsLB) (hw : w.IsGen) (s : LB.Sec H) :
    ∃ s' : LB.Sec H', ∀ z (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ (s.f k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
  have hp := (isGen_iff w).1 hw
  have ind : ∀ (z : X') (k j : H.ι) (k' j' : H'.ι), φ z ∈ H.U k → φ z ∈ H.U j → z ∈ H'.U k' → z ∈ H'.U j' →
      ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) =
        (gm (𝟙 X') z _ (H'.g k' j')).val * (((Geo.Tor.gw w (𝟙 _) z j j')⁻¹).val * gs φ z _ (s.f j)) := by
    intro z k j k' j' hk hj hk' hj'
    have a := hp _ (𝟙 X') z k j k' j' hk hj hk' hj'
    rw [Category.id_comp] at a
    rw [a, gs_sec_trans s φ z hk hj, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    generalize gm φ z _ (H.g k j) = A
    generalize gm (𝟙 X') z _ (H'.g k' j') = B
    generalize Geo.Tor.gw w (𝟙 _) z j j' = C
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : H'.ι, ∃ a : Γ(X', H'.U k'), ∀ (z : X') (k : H.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs (𝟙 X') z _ a = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) := by
    intro k'
    let W : H.ι → X'.Opens := fun k => (H.pull φ).U (fun _ => k) ⊓ H'.U k'
    have l₁ : ∀ k, W k ≤ φ ⁻¹ᵁ H.U k := fun k x hx => mem_pull.1 hx.1
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (z : X') k, z ∈ W k →
        gs (𝟙 X') z (W k) (u k) = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) :=
      ⟨fun k => ((show Γ(X', W k)ˣ from w.s (fun _ => k, k'))⁻¹).val *
          (X'.presheaf.map (homOfLE (l₁ k)).op).hom ((φ.app _).hom (s.f k)), fun z k hz =>
        (gs_mul (𝟙 X') z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit (𝟙 X') z _ hz _).trans (congrArg Units.val (map_inv _ _)))
          ((gs_res (𝟙 X') z _ hz _).trans ((gs_pull (𝟙 X') φ z _ (l₁ k hz) _).trans (by rw [Category.id_comp]))))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (H'.U k')
      (fun k => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hH (φ y)
        exact Opens.mem_iSup.2 ⟨k, mem_pull.2 hk, hy⟩) u
      (fun k j => fn_ext (V := W k ⊓ W j) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu y k hy.1, hu y j hy.2, ind y k j k' k' (l₁ k hy.1) (l₁ j hy.2) hy.1.2 hy.1.2,
          gm_self hH' (𝟙 X') y hy.1.2, Units.val_one, _root_.one_mul])
    refine ⟨a, fun z k h₁ h₂ => ?_⟩
    have hz : z ∈ W k := ⟨mem_pull.2 h₁, h₂⟩
    exact (gs_res (𝟙 X') z inf_le_right hz a).symm.trans ((congrArg (gs (𝟙 X') z (W k)) (ha k)).trans
      (hu z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun z k k' hk hk' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hH (φ y)
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X') y _ hy _) (gs_res (𝟙 X') y _ hy _))).symm)
    rw [ha j y k hk hy.1, ha j' y k hk hy.2]
    exact ind y k k j j' hk hk hy.1 hy.2
  · show _ = _ * gs (𝟙 X') z _ (a k')
    rw [ha k' z k hk hk', Units.mul_inv_cancel_left]

theorem section_pull : ∀ (X X' : Scheme.{0}) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ)), H.IsLB → H'.IsLB → w.IsGen → ∀ s : LB.Sec H, (∃! s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k'))) ∧ ∀ s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) → nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  intro X X' φ H H' w hH hH' hw s
  constructor
  · obtain ⟨s', hs'⟩ := exists_pull φ H H' w hH hH' hw s
    refine ⟨s', hs', fun t ht => ?_⟩
    obtain ⟨f, hf⟩ := t
    obtain ⟨g, hg⟩ := s'
    obtain rfl : f = g := funext fun k' => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact (Units.mul_right_inj _).1 ((ht z k k' hk hz).symm.trans (hs' z k k' hk hz))
    rfl
  · intro s' hs'
    have key : ∀ (z : X') (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
        (φ z ∈ X.basicOpen (s.f k) ↔ z ∈ X'.basicOpen (s'.f k')) := fun z k k' hk hk' => by
      rw [← isUnit_gs_iff φ z hk, hs' z k k' hk hk', Units.isUnit_units_mul]
      exact isUnit_gs_iff (𝟙 X') z hk' _
    ext z
    constructor
    · intro hz
      obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 hz
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact Opens.mem_iSup.2 ⟨k, (key z k k' hk (X'.basicOpen_le _ hk')).2 hk'⟩
    · intro hz
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show φ z ∈ nonzeroLocus s from hz)
      obtain ⟨k', hk'⟩ := exists_chart hH' z
      exact Opens.mem_iSup.2 ⟨k', (key z k k' (X.basicOpen_le _ hk) hk').1 hk⟩

end GlobalTheory.SecPullIso
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_comp_stalkMap {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm

theorem values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by
  intro X Y Z Z' L K _ φ ε r ρ z J hJ
  have hJ' : Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) := fun ψ => hJ (ρ ≫ ψ)
  have hm := hJ'.mem φ r
  refine ⟨hJ', fun s => ?_, fun t => ?_, fun c => gs_comp_stalkMap r ρ z ⊤ trivial c⟩
  · rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact gs_comp_stalkMap r ρ z _ hm _
  · rw [val_of t (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact (gs_unit (ρ ≫ r) z _ hm _).symm.trans ((gs_comp_stalkMap r ρ z _ hm _).trans
      (congrArg (ρ.stalkMap z).hom (gs_unit r (ρ z) _ hm _)))

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_smul_sub_smul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (c' c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval d r z J = gs r z ⊤ c' * sval s r z J - gs r z ⊤ c * sval t r z J := by
  have gsub : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)),
      gs r z U (a - b) = gs r z U a - gs r z U b := fun Z r z U h a b => by
    simp only [gs_eq r z U h, map_sub]
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j)
        ((Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j)) =
      gs r z ⊤ c' * gs r z (LB.wchart L φ j) (s.f j) - gs r z ⊤ c * gs r z (LB.wchart L φ j) (t.f j) :=
    fun Z r z j hj => (gsub Z r z _ hj _ _).trans (congrArg₂ (· - ·)
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _)))
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _))))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j),
      fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [sec_trans s (𝟙 Y) y hy.1 hy.2, sec_trans t (𝟙 Y) y hy.1 hy.2]
  simp only [trF]
  ring

theorem exists_sec_relation_defect : ∀ (Y : Scheme.{0}) (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y ⟶ X)) (εu : K'' → ℤ) (τ : Y ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → ∃ d : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval d r z J = gs r z ⊤ c' * sval s' r z J - gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val) := by
  intro Y X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (hF U h).symm : FormEq _ _ φ' ε') (pullMulSec s τ u hu)
  obtain ⟨d, hd⟩ := exists_sec_smul_sub_smul s' t c' c
  exact ⟨d, fun Z r z J hJ => by rw [hd Z r z J hJ, ht Z r z J hJ, sval_pullMulSec s τ u hu r z hJ]⟩

end GlobalTheory
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

end Refine

section Present

variable {S : Scheme.{0}}


end Present

section Data

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)

end Data

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

variable {q a p}

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

section Datum

variable {S : Scheme.{0}}

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

attribute [local instance] SplitExt.free SplitExt.finite

end Datum

end GlobalTheory.GtCoordCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_sval_eq_zero_of_app_injective {X Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (hr : ∀ U : Y.Opens, Function.Injective (r.app U).hom) (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j : K → L.ι) : d.f j = 0 := by
  apply hr (LB.wchart L φ j)
  refine fn_ext fun z hz => ?_
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hz' : r z ∈ LB.wchart L φ j := hz
  have e₁ : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    (sec_trans d r z hz' (Good.mem hI φ r)).trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  have e₂ : gs r z (LB.wchart L φ j) 0 = 0 := by
    rw [gs_eq r z _ hz', map_zero, map_zero]
  refine (gs_pull (𝟙 Z) r z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 Z) r z _ hz' _).symm)
  rw [Category.id_comp]
  exact e₁.trans e₂.symm

theorem sec_eq_zero_of_sval_whiskerRight_eq_zero :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (z : (T' ⊗ B).left) (J), Good L z J → sval d (ψ ▷ B).left z J = 0) → ∀ j, d.f j = 0 := by
  intro S B T T' _ _ _ ψ hψ X L hL K _ φ ε d h j
  exact sec_eq_zero_of_sval_eq_zero_of_app_injective (ψ ▷ B).left
    (app_whiskerRight_injective_of_flat S B T T' ψ hψ) L hL φ ε d h j

end GlobalTheory
end
