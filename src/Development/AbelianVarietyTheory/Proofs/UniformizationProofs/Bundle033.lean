module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecPull

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem mem_wchart_comp {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) {p : K → L.ι} {y : Y'}
    (hy : y ∈ LB.wchart L (fun k => φ' k ≫ F) p) : h y ∈ LB.wchart L φ p :=
  Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    show (h ≫ φ k) y ∈ L.U (p k)
    rw [← hc]; exact this

theorem trF_comp {Z : Scheme.{0}} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (p p' : K → L.ι) :
    trF φ ε (r ≫ h) z p p' = trF (fun k => φ' k ≫ F) ε r z p p' := by
  simp only [trF, hc, Category.assoc]

theorem exists_down_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L' φ' q) (a.f q) =
          (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ a : Γ(Y', LB.wchart L' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
    intro q
    let W : (K → L.ι) → Y'.Opens := fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    have le : ∀ p, W p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun p y hy => mem_wchart_comp hc hy.1
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(Y', W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
        gs r z (W p) (v p) = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) :=
      ⟨fun p => (u p q)⁻¹.val * (Y'.presheaf.map (homOfLE (le p)).op).hom ((h.app _).hom (s.f p)),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q Z r z hz)))))
          ((gs_res r z (le p) hz _).trans (gs_pull r h z _ (le p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y'.sheaf.existsUnique_gluing' W (LB.wchart L' φ' q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) v
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y') y inf_le_right hy _).symm)
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, sec_trans s (𝟙 Y' ≫ h) y (le p hy.1) (le p' hy.2), trF_comp hc,
          pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.1.2, trF_self hL' _ ε (𝟙 Y') y hy.1.2, inv_one, mul_one,
          ← mul_assoc, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨a, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ W p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z (W p)) (ha p)).trans (hv Z r z p hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha q Z r z p⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (gs_res (𝟙 Y') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val (gm_linComb L' φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y') y _ hy _))).symm)
  refine (ha j _ (𝟙 Y') y p m hy.1).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y') y p m hy.2)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y') y m m hy.1 hy.2, trF_self hL _ ε (𝟙 Y') y m, one_mul, mul_inv, inv_inv, Units.val_mul,
    mul_assoc]
  rfl

theorem existsUnique_secPull (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (F : X' ⟶ X) (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) (K : Type) [Fintype K] (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃! a : LB.Sec (LB.LinComb L' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain ⟨a, ha⟩ := exists_down_sec ((isGen_iff w).1 hw) hL hL' φ' φ ε h hc s
  refine ⟨a, fun Z r z p q hp hq => ?_, fun b hb => ?_⟩
  · rw [ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)]
    exact (Units.mul_inv_cancel_left (pw w φ' ε r z p q) _).symm
  · have e : b.f = a.f := funext fun q => fn_ext fun y hy => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      refine Eq.trans ?_ (ha _ (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy).symm
      rw [hb _ (𝟙 Y') y p q hp (Set.mem_iInter.1 hy)]
      exact (Units.inv_mul_cancel_left (pw w φ' ε (𝟙 Y') y p q) _).symm
    cases a; cases b; cases e; rfl

end GlobalTheory.SecPull
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif.RigidifyIso

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_ratio {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (f : Y' ⟶ Y) (hφ : ∀ k, φ' k ≫ F = f ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm (r ≫ f) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ c * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have le : ∀ p, LB.wchart L (fun k => φ' k ≫ F) p ≤ f ⁻¹ᵁ LB.wchart L φ p := fun p y hy =>
    Set.mem_iInter.2 fun k => (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (p k)) (hφ k)).mp (Set.mem_iInter.1 hy k)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res (inf_le_left.trans (le p)) (pullU f _ (t.s p)) * (u p q * res inf_le_right (a.s q))⁻¹) =
        gm (r ≫ f) z (LB.wchart L φ p) (t.s p) * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q))⁻¹ :=
    fun Z r z p q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hz _).trans (gm_pull r f z _ (le p hz.1) _))
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (hu p q Z r z hz) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y'.Opens)
    (fun i : (K → L.ι) × (K → L'.ι) => LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩)
    (fun i => res (inf_le_left.trans (le i.1)) (pullU f _ (t.s i.1)) * (u i.1 i.2 * res inf_le_right (a.s i.2))⁻¹)
    (fun i i' y hy => by
      have e : trF φ ε (𝟙 Y' ≫ f) y i.1 i'.1 = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y i.1 i'.1 := by
        simp only [trF, hφ, Category.assoc]
      rw [hv _ _ y _ _ hy.1, hv _ _ y _ _ hy.2, pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2,
        gen_trans ha (𝟙 Y') y hy.1.2 hy.2.2, gen_trans ht (𝟙 Y' ≫ f) y (le _ hy.1.1) (le _ hy.2.1), e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun Z r z p q h₁ h₂ => ?_⟩
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
  have e := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hv Z r z p q hz))
  rw [e, inv_mul_cancel_right]

theorem exists_scaled {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (π : X' ⟶ B) (c : Γ(B, ⊤)ˣ) : ∃ w' : LB.Iso L' (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
      (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k → gw w' r z j k = gm (r ≫ π) z ⊤ c * gw w r z j k := by
  refine ⟨⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩, fun Z r z j k hj hk => ?_⟩
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r π z ⊤ trivial c)) rfl)

theorem exists_rigidified_iso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (he : eSec G' ≫ Ψ = f ≫ eSec G) (L : RigLB G) (L' : RigLB G'), (∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen) → ∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) := by
  rintro S S' f G _ _ G' _ _ Ψ he L L' ⟨w, hw⟩
  have hw := (isGen_iff w).1 hw
  obtain ⟨c, hc⟩ := exists_ratio (K := PUnit) (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1)
    hw L.isLB L'.isLB f (fun _ => he) L'.rig L'.rigGen L.rig L.rigGen
  obtain ⟨w', hw'⟩ := exists_scaled (B := (𝟙_ (Over S')).left) w G'.hom c
  have hs : eSec G' ≫ (show G'.left ⟶ (𝟙_ (Over S')).left from G'.hom) = 𝟙 _ := Over.w η[G']
  refine ⟨w', (isGen_iff w').2 fun Y r y j j' k k' hj hj' hk hk' => ?_,
    (maps_iff w' _ (fun _ => eSec G) _ L'.rig L.rig f _ (rigPull_le Ψ f he L.L) (fun _ => rfl)).2
      fun Z r z p q hp hq => ?_⟩
  · rw [hw' Y r y j k hj hk, hw' Y r y j' k' hj' hk', hw Y r y j j' k k' hj hj' hk hk', mul_left_comm]
  · refine (hc Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)).trans ?_
    rw [← _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one,
      hw' Z (r ≫ eSec G') z _ _ (hp _) (hq _), Category.assoc]
    exact congrArg (fun g => gm g z ⊤ c * _) ((congrArg (r ≫ ·) hs).trans (Category.comp_id r)).symm

end GlobalTheory.Unif.RigidifyIso
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInPow

open PsiInPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_of_gs (D : DegPre R) (χ : D.X) (J : Ideal R)
    (H : ∀ (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
      V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q → ∀ z : Spec (CommRingCat.of (FractionRing R)), jK R z ∈ V →
      ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
        (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val) :
    D.PsiIn χ J := by
  intro j' V hV hle h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  by_cases hne : ∃ z, jK R z ∈ V
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r', hr', e'⟩ := H q V hV hle z hz
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z
  exact (gs_pull (𝟙 _) (jK R) y V hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

theorem gs_of_psiIn (D : DegPre R) (χ : D.X) (J : Ideal R) (H : D.PsiIn χ J)
    (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q) (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val := by
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => q) :=
    fun y hy => mem_wchart _ _ _ _ (hle hy)
  obtain ⟨r, hrJ, hr⟩ := H (fun _ => q) V hV hle h
  refine ⟨r, hrJ, ?_⟩
  exact (gs_pull (𝟙 _) (jK R) z V hz r).symm.trans ((congrArg (gs (𝟙 _) z _) hr).trans
    ((gs_res (𝟙 _) z h hz _).trans (gs_unit _ _ _ (h hz) _)))

theorem val_psi_zero (D : DegPre R) (hB : D.TauBimult) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    val (D.psi 0) (𝟙 _) y J = (val D.rigK (𝟙 _) y J)⁻¹ := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 0
  have z0 : val (D.tau (0 + 0) 0) (𝟙 _) y J = val (D.tau 0 0) (𝟙 _) y J :=
    congrArg (fun a => val (D.tau a 0) (𝟙 _) y J) (add_zero 0)
  rw [z0, cPoint_zero, C.face, _root_.mul_one] at t
  have t0 : val (D.tau 0 0) (𝟙 _) y J = 1 := mul_eq_left.1 t.symm
  have e : val (D.tau 0 0) (𝟙 _) y J = val (D.psi (0 + 0)) (𝟙 _) y J * (val (D.psi 0) (𝟙 _) y J)⁻¹ *
      (val (D.psi 0) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [t0, add_zero, mul_inv_cancel, _root_.one_mul] at e
  exact (inv_mul_eq_one.1 e.symm)

end PsiInPow

end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpandsLinear

def scalOn {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    R →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem scalOn_apply {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (r : R) : resTop W (scal p r) = scalOn p W r := rfl

theorem scal_comp_specMap {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

theorem app_resTop_scal {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

def secComb {Y : Scheme.{0}} {L : LB Y} {n : ℕ} (a : Fin n → Γ(Y, ⊤)) (s : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (a i) * (s i).f j
  compat := fun j j' => by

    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (s i)).compat j j'

theorem secScal_comb {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {X Y Y' : Scheme.{0}} (L : LB X)
    {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ)
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y) (π : Y' ⟶ Spec (CommRingCat.of C))
    (π' : Y' ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ Spec (CommRingCat.of R))
    (hπ : π' = π ≫ Spec.map (CommRingCat.ofHom φ)) (hp : h ≫ p = π') {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (t : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (r a : Fin n → R) (d : R) (c : Fin n → C) (hc : ∀ i, φ (a i) * φ (r i) = φ d * c i)
    (H : ∀ i, GeneratorPullback.SecScal L φ₁ ε₁ (s i) φ₂ ε₂ (t i) h (scal π' (r i)))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (hs : ∀ j, s₀.f j = ∑ i, resTop _ (scal π (c i)) * (s i).f j) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₀ φ₂ ε₂ (secComb (fun i => scal p (a i)) t) h (scal π' d) := by
  intro j₁ j₂ hco
  erw [hs]
  dsimp only [secComb]
  erw [map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have Hi := H i j₁ j₂ hco
  erw [map_mul, map_mul, map_mul, Hi, app_resTop_scal, SecOps.resTop_res, SecOps.resTop_res]
  rw [hp, hπ, scal_comp_specMap, scal_comp_specMap, scal_comp_specMap, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [scalOn_apply]
  rw [← map_mul, hc, map_mul]

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {N : Type} (S : Finset N) (s : N → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

end ExpandsLinear


open ExpandsLinear in
theorem expands_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by
  intro R _ _ I _ D A G _ _ _ U k n b F c s hE hs
  choose r hr σ f hσ hf hE using hE
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun i => c i / algebraMap R (FractionRing R) (r i))
  choose a ha using hd
  have hc : ∀ i, algebraMap R (FractionRing R) (a i) * algebraMap R (FractionRing R) (r i) =
      algebraMap R (FractionRing R) d * c i := fun i => by
    have h0 : algebraMap R (FractionRing R) (r i) ≠ 0 :=
      fun h => hr i ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
    rw [ha i, Algebra.smul_def, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  refine ⟨d, nonZeroDivisors.ne_zero d.2, ExpandsLinear.secComb (fun i => scal G.hom (a i)) σ,
    fun α => ExpandsLinear.secComb (fun i => scal D.toPre.P.A.hom (a i)) (fun i => f i α), ?_, fun α => ?_, fun e => ?_⟩
  · exact ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _ (pullback.snd G.hom (jK R)) _ G.hom rfl
      pullback.condition b σ r a d c hc hσ s hs
  · refine ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_
      (Over.w (DegPre.prB D.toPre (FractionRing R))) (fun i => (F i).s α) (fun i => f i α) r a d c hc
      (fun i => hf i α) _ fun j => ?_
    · rw [← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      congr 1
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [ExpandsLinear.fam_sum_f]
      rfl
  · exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionTheta

theorem exists_theta_acts : KerPowSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ), 1 ≤ n → ∀ x : Over.mk t ⟶ P.A, x ^ n = 1 → ∃ θ : ThetaGrp P.A P.L (n : ℤ) (Over.mk t), θ.pt = x ∧ ∀ s : LB.Sec (LPow P.A P.L (n : ℤ) (Over.mk t)), ∃ s', IsActOf P.A P.L (n : ℤ) θ s s' := by
  intro hK S _ P F _ t n hn x hx

  have : Unique (Over.mk t).left := inferInstanceAs (Unique (PrimeSpectrum F))
  obtain ⟨θ, hθ⟩ := GlobalTheory.BoxTheta.exists_theta hK P hn x hx

  exact ⟨θ, hθ, fun s => GlobalTheory.VVRank.exists_isTwistPull P.A P.isLB θ.isGen s⟩

end GlobalTheory.TorsionTheta
end
