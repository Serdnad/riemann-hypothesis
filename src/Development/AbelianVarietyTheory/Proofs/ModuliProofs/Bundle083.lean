module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleMap

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gm r z (LB.wchart L φ j) (u.s j) = gm r z ⊤ a * gm r z (LB.wchart L φ j) (u'.s j) := by
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      gm r z (LB.wchart L φ j) (u.s j * (u'.s j)⁻¹) =
        gm r z (LB.wchart L φ j) (u.s j) * (gm r z (LB.wchart L φ j) (u'.s j))⁻¹ := fun Z r z j =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (φ k y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp⟩) (fun j => u.s j * (u'.s j)⁻¹)
    (fun j j' y hy => by
      rw [hv, hv, gen_trans hu (𝟙 Y) y hy.1 hy.2, gen_trans hu' (𝟙 Y) y hy.1 hy.2, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨a, fun Z r z j hj => ?_⟩
  rw [← gm_res r z le_top hj a, ha j, hv, inv_mul_cancel_right]

theorem exists_rigidified {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) (e : S ⟶ X) (e' : S' ⟶ X') (p : X' ⟶ S')
    (hp : e' ≫ p = 𝟙 _) (f : S' ⟶ S) (he : e' ≫ F = f ≫ e) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) ρ' ρ f := by
  obtain ⟨ρ₀, h₀, H⟩ := DegPull.exists_pmaps hw hL hL' (K := PUnit) (φ' := fun _ => e') (φ := fun _ => e)
    (ε := fun _ => 1) f (fun _ => he) ρ hρ
  obtain ⟨a, ha⟩ := exists_ratio hL' h₀ hρ'
  let w' : LB.Iso L' (L.pull F) := ⟨fun j => res le_top (pullU p ⊤ a) * w.s j⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ a * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _
      (show r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k from ⟨mem_pull.2 hj, hk⟩) _).trans
        (gm_pull r p z ⊤ trivial a)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [key Z r z j k hj hk, key Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · rw [H Z r z j k hj hk, ha Z r z k (Set.mem_iInter.2 hk), Fintype.prod_unique, Fintype.prod_unique,
      key Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id, zpow_one, zpow_one,
      ← _root_.mul_assoc, mul_comm (gm r z ⊤ a)]

theorem pmaps_cubical {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  obtain ⟨a, ha⟩ := exists_ratio L'.isLB ht c'.isGen
  have a1 : a = 1 := rigid a fun y => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' L'.isLB y
    let o : 𝟙_ (Over S') ⟶ G' := 1
    have e := DegPull.pmaps_val hψ H (lift o (lift o o)).left y hJ hJ'
    have q : (lift o (lift o o)).left ≫ (cubeMapOf gp).F3 =
        (lift (pushHom gp _ o) (lift (pushHom gp _ o) (pushHom gp _ o))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    have e₁ : cubV c y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by
      rw [map_one]
      exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
    have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
    have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
    have e₄ := ha _ (lift o (lift o o)).left y _ (hJ'.mem (thφ G' (x3 G')) _)
    have e₅ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) e₂ (e₄.trans (congrArg _ e₃))))
    simp only [o, _root_.mul_one, mul_inv_cancel, inv_mul_cancel_right, mul_inv_cancel_right, _root_.one_mul, inv_mul_cancel] at e₅
    exact e₅.symm
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, ha Z r z q (Set.mem_iInter.2 hq), a1, map_one, _root_.one_mul]

end TripleMap

theorem exists_sabMap_of_lbIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (φ : t'.G.left ⟶ t.G.left), (IsReduced X' ∧ genericPoints X' ⊆ abLocus t'.G) → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ ν : SABMap t' t f, ν.φ = φ := by
  intro E _ _ _ H X X' t t' f φ ⟨hr, hab⟩ gp hact ⟨w, hw⟩
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have sm := t'.semi.smooth
  have gc := t'.semi.geomConnected
  have gi := grpObj_geometricallyIntegral_of_smooth X' t'.G
  obtain ⟨s₂, i₂, l₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G t'.G sm sm gi gi
  obtain ⟨s₃, i₃, l₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G (t'.G ⊗ t'.G) sm s₂ gi i₂
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over X') ⟶ t'.G) (lift (1 : 𝟙_ (Over X') ⟶ t'.G) (1 : 𝟙_ (Over X') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  refine Units.ext (eq_one_of_appLE_section_eq_one X' (G3 t'.G) o.left (Over.w o) s₃ i₃
    ⟨hr, fun x hx => l₃ ⟨hab hx, l₂ ⟨hab hx, hab hx⟩⟩⟩ ⊤ a.val le_rfl ?_)
  exact (congrArg (fun q => q.hom a.val) (o.left.appLE_eq_app (U := ⊤))).trans (congrArg Units.val h₁)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PartialBundleGlue

theorem iso_isGen_iff {X : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) :
    w.IsGen ↔ ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a → x ∈ M.U a' → x ∈ L.U b → x ∈ L.U b' →
      gm (𝟙 X) x (M.U a ⊓ L.U b) (w.s (a, b)) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
          gm (𝟙 X) x (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have key : ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') →
      gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ := by
    intro x a a' b b' hm
    show gm (𝟙 X) x _ (res _ (M.g a a') * (res _ (L.g b b'))⁻¹) = _
    rw [map_mul, map_inv, gm_res (𝟙 X) x _ hm, gm_res (𝟙 X) x _ hm]
  constructor
  · intro h x a a' b b' ha ha' hb hb'
    have hm : x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ha', hb'⟩
    have := congrArg (gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) (h (a, b) (a', b'))
    rw [← key x a a' b b' hm]
    exact (gm_res (𝟙 X) x _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hm _))))
  · rintro h ⟨a, b⟩ ⟨a', b'⟩
    apply unit_ext
    intro x hx
    have := h x a a' b b' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    rw [← key x a a' b b' hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

theorem pull_isGen_of {X S : Scheme.{0}} {L : LB X} {e : S ⟶ X} (r : (L.pull e).Gen)
    (h : ∀ (x : S) (a b : L.ι), e x ∈ L.U a → e x ∈ L.U b →
      gm (𝟙 S) x ((L.pull e).U fun _ => a) (r.s fun _ => a) =
        gm e x (L.U a ⊓ L.U b) (L.g a b) * gm (𝟙 S) x ((L.pull e).U fun _ => b) (r.s fun _ => b)) :
    r.IsGen := by
  intro J J'
  obtain ⟨a, rfl⟩ : ∃ a, J = fun _ => a := ⟨J PUnit.unit, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, J' = fun _ => b := ⟨J' PUnit.unit, rfl⟩
  apply unit_ext
  intro x hx
  have ha : e x ∈ L.U a := mem_pull.1 hx.1
  have hb : e x ∈ L.U b := mem_pull.1 hx.2
  have eg : gm (𝟙 S) x ((L.pull e).U (fun _ => a) ⊓ (L.pull e).U (fun _ => b))
      ((L.pull e).g (fun _ => a) (fun _ => b)) = gm e x (L.U a ⊓ L.U b) (L.g a b) := by
    show gm (𝟙 S) x _ (∏ _k : PUnit, (res _ (pullU e _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 S) x _ hx _).trans (gm_pull (𝟙 S) e x (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, eg]
  exact h x a b ha hb

theorem exists_glue : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  intro X S p e I U M hep hrig hU hM hself hr hiso
  choose r hr using hr
  choose w hw hn using fun i j => GlobalTheory.T.exists_partialBundle_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j)
    (hr i) (hr j) (hiso j i)
  have hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c →
      gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) *
        gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) =
        gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c)) := by
    intro i j k
    refine GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig
      (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_
    intro x a b c ha hb hc
    have h₁ := hn i j x a b ha hb
    have h₂ := hn j k x b c hb hc
    have h₃ := hn i k x a c ha hc
    rw [h₁, h₂, ← _root_.mul_assoc] at h₃
    exact mul_right_cancel h₃
  let L : LB X := ⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩
  · rintro ⟨i, a⟩
    apply unit_ext
    intro x hx
    rw [map_one]
    exact (gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact hc i j k x a b c hx.1.1 hx.1.2 hx.2
  · apply pull_isGen_of
    rintro x ⟨i, a⟩ ⟨j, b⟩ ha hb
    exact hn i j x a b ha hb
  · intro i
    refine ⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩
    rintro x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'
    have h₁ := hc j j' i x b b' a hb hb' ha
    have h₂ := (iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'
    rw [hself j' b' x hb', _root_.one_mul] at h₂
    rw [h₂, ← _root_.mul_assoc] at h₁
    exact h₁.symm

end GlobalTheory.PartialBundleGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  unfold res
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma U_le_pull_id_U {X : Scheme.{0}} (N : LB X) (i : N.ι) :
    N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := by
  intro x hx
  unfold LB.pull LB.LinComb LB.wchart
  simpa using hx

private lemma res_pullU_id_moduli {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U)
    (a : Γ(X, U)ˣ) : res h (pullU (𝟙 X) U a) = res h' a := by
  unfold res pullU
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rfl

private lemma res_self_moduli {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  unfold res
  ext
  simp

theorem exists_gen_of_pull_id {X : Scheme.{0}} (N : LB X) (t : (N.pull (𝟙 X)).Gen) (ht : t.IsGen) :
    ∃ t : N.Gen, t.IsGen := by
  refine ⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩
  intro i j
  have key := congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, res_res_lemma, res_res_lemma] at key
  simp only [res_res_lemma]
  refine key.trans ?_
  congr 1
  have hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [LB.pull, LB.LinComb, LB.wchart] at h1 h2
    have a : x ∈ N.U i := by simpa using h1
    have b : x ∈ N.U j := by simpa using h2
    exact ⟨a, b⟩
  have hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j)) := by
    show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [hG, res_res_lemma]
  exact (res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)

private theorem val_mul_val_comm_of_fst_eq (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) (A : Over S) [GrpObj A]
    (N : LB A.left) (hA : IsAbelianScheme A) (hN : N.IsLB)
    (w : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen) (hw : w.IsGen)
    (e' : S' ⟶ pullback A.hom π) (he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A)
    (he'q : e' ≫ pullback.snd A.hom π = 𝟙 S')
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ pullback A.hom π)
    (hg : g₁ ≫ pullback.fst A.hom π = g₂ ≫ pullback.fst A.hom π) (z : Z) (J : (Z ⟶ A.left) → N.ι)
    (hJ : Good N z J) :
    val w g₁ z J * val w (g₂ ≫ pullback.snd A.hom π ≫ e') z J =
      val w g₂ z J * val w (g₁ ≫ pullback.snd A.hom π ≫ e') z J := by
  have hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
  let FinalForm : Over S := Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)
  have hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π) :=
    (Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm
  let a : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)
  let a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)
  let p0 : (A ⊗ FinalForm).left ⟶ Z := (snd A FinalForm).left
  let e : Z ⟶ (A ⊗ FinalForm).left := (lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left
  have he : e ≫ p0 = 𝟙 Z := by
    simp only [e, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π := by
    simp only [a, a', pullback.lift_fst]
  have hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π :=
    (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
  have hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a, e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU]
      rfl
    · simp only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a', e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]
      rfl
    · simp only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  let x : FinalForm ⟶ A := Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])
  let ρ : Z ⟶ (A ⊗ FinalForm).left := (lift x (𝟙 FinalForm)).left
  have hρp : ρ ≫ p0 = 𝟙 Z := by
    simp only [ρ, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hρa : ρ ≫ a = g₁ := by
    apply pullback.hom_ext
    · simp only [a, ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst]
      rfl
    · simp only [a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  have hρa' : ρ ≫ a' = g₂ := by
    apply pullback.hom_ext
    · simp only [a', ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst, ← hg]
      rfl
    · simp only [a', Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  let u := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))
  let u' := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))
  have hu : u.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hu' : u'.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1))
      (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) := by
    intro U _ h
    simp [Fintype.prod_sum_type, hap]
  have key := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ
  · simp only [u, u'] at key
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
    have hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, hρp, Category.id_comp]
    rw [hρp', hρp', hea', hea, hρa, hρa'] at key
    exact key
  · intro y J' hJ'
    simp only [u, u']
    rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
    have he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, he, Category.id_comp]
    rw [he', he', mul_comm]

theorem exists_gen_of_rigidified_of_flat_baseChange :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG S S' π A _ N hA hN hfl hsu hqc hr hw
  obtain ⟨r, hr⟩ := hr
  obtain ⟨w, hw⟩ := hw
  have := hfl
  have := hsu
  have := hqc
  have hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π := by
    rw [Category.assoc, Category.id_comp]
    have h0 : (η[A]).left ≫ A.hom = 𝟙 S := Over.w (η[A])
    unfold eSec
    rw [h0, Category.comp_id]
  let e' : S' ⟶ pullback A.hom π := pullback.lift (π ≫ eSec A) (𝟙 S') hz
  have he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A := pullback.lift_fst _ _ _
  have he'q : e' ≫ pullback.snd A.hom π = 𝟙 S' := pullback.lift_snd _ _ _
  let w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen := w
  have hw' : w'.IsGen := hw
  let r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen := r
  have hr' : r'.IsGen := hr
  let v := LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π))
    (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))
  have hv : v.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw'
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w' hw' _)))
  obtain ⟨t', ht', hvv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ))
    (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv
  refine Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π)
    (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)
  · intro Z g₁ g₂ z J hJ hg
    rw [hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]
    simp only [v, val_mul hJ, val_pull hJ, val_inv]
    have hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
    rw [hq]
    have key := val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ
    rw [mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]
    congr 1
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact key

end GlobalTheory
end
