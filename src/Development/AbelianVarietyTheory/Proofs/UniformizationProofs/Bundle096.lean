module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

local instance (priority := high) grpObjPullbackForWeightTower {S T : Scheme.{0}}
    (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

theorem gm_linCombIso {X Y Z : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) =
      ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem exists_gen_of_iso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen B, t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : B.ι) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) (t'.s j) = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
  have tr : ∀ (y : Y) (j j' : B.ι) (i i' : A.ι), y ∈ B.U j → y ∈ B.U j' → y ∈ A.U i → y ∈ A.U i' →
      gm (𝟙 Y) y (B.U j ⊓ A.U i) (w.s (j, i)) * gm (𝟙 Y) y (A.U i) (t.s i) =
        gm (𝟙 Y) y _ (B.g j j') * (gm (𝟙 Y) y (B.U j' ⊓ A.U i') (w.s (j', i')) * gm (𝟙 Y) y (A.U i') (t.s i')) := by
    intro y j j' i i' hj hj' hi hi'
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U j ⊓ A.U i ⊓ (B.U j' ⊓ A.U i') := ⟨⟨hj, hi⟩, hj', hi'⟩
    have hn : (𝟙 Y : Y ⟶ Y) y ∈ A.U i ⊓ A.U i' := ⟨hi, hi'⟩
    have e := (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (j, i) (j', i'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y (j, i) (j', i') hm) (gm_res _ y _ hm _))))
    have e' := (gm_res _ y _ hn _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht i i')).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hn _))))
    refine (congrArg₂ (· * ·) e e').trans ?_
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel_right]
    rfl
  have glue : ∀ j : B.ι, ∃ s : Γ(Y, B.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) s = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
    intro j
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι), r z ∈ B.U j ⊓ A.U i →
        gm r z (B.U j ⊓ A.U i) (@id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) =
          gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := fun Z r z i h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res r z _ h _))
    obtain ⟨s, hs⟩ := glue_unit (B.U j) (fun i => B.U j ⊓ A.U i) (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hA x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩)
      (fun i => @id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) (fun i i' x hx => by
        rw [v _ _ x i hx.1, v _ _ x i' hx.2, tr x j j i i' hx.1.1 hx.1.1 hx.1.2 hx.2.2, gm_self hB _ x hx.1.1,
          _root_.one_mul])
    refine ⟨s, fun Z r z i hj hi => ?_⟩
    have hm : r z ∈ B.U j ⊓ A.U i := ⟨hj, hi⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs i)).trans (v Z r z i hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z j i => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := exists_chart hA y
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  exact (hs j _ _ y i hy.1 hi).trans ((tr y j j' i i hy.1 hy.2 hi hi).trans (congrArg _ (hs j' _ _ y i hy.2 hi).symm))

theorem triv_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) :
    Triv B := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht', -⟩ := exists_gen_of_iso hA hB w hw t ht
  exact ⟨t', ht'⟩

variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_genWt_of_lbIso {G : Over S} [GrpObj G] (Q : TQ G X) {N N' : LB Q.B.left} (hN : N.IsLB) (hN' : N'.IsLB)
    (h : LBIso N N') {u : LB.Gen (N.pull Q.q.left)} {χ : X} (hu : Q.GenWt N u χ) :
    ∃ u' : LB.Gen (N'.pull Q.q.left), Q.GenWt N' u' χ := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨u', hu', hv⟩ := exists_gen_of_iso (pull_isLB hN _) (pull_isLB hN' _)
    (LB.linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _) u hu.1
  refine ⟨u', hu', fun J => isWt_of_gm _ _ fun Z t g z hz => ?_⟩
  have e : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := congrArg (·.left) (WtBundle.act_comp Q t g)
  have m : ∀ (M : LB Q.B.left) (I : PUnit → M.ι), g.left z ∈ (M.pull Q.q.left).U I →
      ((t ≫ Q.i) * g).left z ∈ (M.pull Q.q.left).U I := fun M I h =>
    (mem_pull (F := Q.q.left)).2 ((congrArg (fun a : Z.left ⟶ Q.B.left => a z ∈ M.U (I PUnit.unit)) e).mpr
      ((mem_pull (F := Q.q.left)).1 h))
  obtain ⟨I, hI⟩ := exists_chart (pull_isLB hN Q.q.left) (g.left z)
  have a₁ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) g.left z ⟨hz, hI⟩
  have a₂ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) ((t ≫ Q.i) * g).left z
    ⟨m _ _ hz, m _ _ hI⟩
  rw [e, ← a₁] at a₂
  rw [hv _ _ z J I (m _ _ hz) (m _ _ hI), hv _ _ z J I hz hI, WtBundle.gm_of_isWt (hu.2 I) t g z (m _ _ hI) hI,
    gm_charUnit, mul_left_comm]
  exact congrArg (fun x => _ * (x * _)) a₂

theorem exists_genWt_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (Q : TQ G X) (Q' : TQ G' X) {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) (hi : TorusCompat f F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left}
    (hβ : Q'.q.left ≫ β = F ≫ Q.q.left) {N : LB Q.B.left} {u : LB.Gen (N.pull Q.q.left)} {χ : X}
    (hu : Q.GenWt N u χ) : ∃ u' : LB.Gen ((N.pull β).pull Q'.q.left), Q'.GenWt (N.pull β) u' χ :=
  let c := chartPullLinComb N β (K := PUnit) (fun _ => Q'.q.left) (fun _ => Q.q.left) (fun _ => 1) F fun _ => hβ
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).pull hF hi (c.le J)⟩

theorem exists_gen_comp {G : Over S} [GrpObj G] (Q : TQ G X) {Y : Scheme.{0}} (b : Q.B.left ⟶ Y) {O : LB Y}
    {u : LB.Gen ((O.pull b).pull Q.q.left)} {χ : X} (hu : Q.GenWt (O.pull b) u χ) :
    ∃ u' : LB.Gen (O.pull (Q.q.left ≫ b)), u'.IsGen ∧ ∀ j, IsWt Q.i _ (u'.s j).val χ :=
  let c := chartPullIn O (K := PUnit) (fun _ => b) (fun _ => 1) Q.q.left
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).res (c.le J)⟩

theorem psum_eq_lift {B T : Over S} [GrpObj B] [IsCommMonObj B] (x : Fin 2 → (T ⟶ B)) (I : Finset (Fin 2)) :
    (psum B x I).left = (lift (x 0) (x 1)).left ≫ (psum B (x2 B) I).left := by
  have e : (fun i => preHom (lift (x 0) (x 1)) (x2 B i)) = x := funext fun i => by
    fin_cases i
    exacts [lift_fst (x 0) (x 1), lift_snd (x 0) (x 1)]
  have := psum_hom (preHom (lift (x 0) (x 1))) (x2 B) I
  rw [e] at this
  exact congrArg (·.left) this.symm

theorem triv_lam_pull {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {f : S' ⟶ S} {b : B'.left ⟶ B.left} (hb : IsGrpPullback B' B f b) {O : LB B.left} {N : LB B'.left} (hO : O.IsLB)
    (hN : N.IsLB) (h : LBIso N (O.pull b)) (ht : Triv (abelian₂ B' N)) {T : Over S'} (U : Over.mk (T.hom ≫ f) ⟶ B ⊗ B) :
    Triv ((abelian₂ B O).pull U.left) := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → (T ⟶ B'), ∀ i, pushPt hb.1.w (x i) = U ≫ x2 B i :=
    ⟨fun i => Over.homMk (hb.1.lift (U ≫ x2 B i).left T.hom (Over.w (U ≫ x2 B i))) (hb.1.lift_snd _ _ _),
      fun i => Over.OverMorphism.ext (hb.1.lift_fst _ _ _)⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := ht
  have t₁ : Triv (cubeLB B' x N) :=
    gen_chartPull (chartPullSame N (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (lift (x 0) (x 1)).left
      fun I => psum_eq_lift x I.down) t ht
  have l₁ : (cubeLB B' x N).IsLB := LB.isLB_linComb hN _ _
  have l₂ : (cubeLB B' x (O.pull b)).IsLB := LB.isLB_linComb (pull_isLB hO b) _ _
  have l₃ : (abelian₂ B O).IsLB := LB.isLB_linComb hO _ _
  have t₂ : Triv (cubeLB B' x (O.pull b)) := triv_of_lbIso l₁ l₂ ⟨_, DVR.linCombIso_isGen w hw _ _⟩ t₁
  have c : ChartPull (cubeLB B' x (O.pull b)) (abelian₂ B O) U.left :=
    chartPullLinComb O b (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) U.left
      fun I => psum_push hb x (x2 B) U hx I.down
  exact triv_of_lbIso l₂ (pull_isLB l₃ _)
    (LBIso.chartPull c (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B O) U.left U.left rfl) (GtBaseChange.lbIso_refl l₃)) t₂

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (e : ℕ) : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isLocalRing_quotient_pow (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isProjBy_of_relAmple {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) {L : LB B.left}
    (hL : L.IsLB) (h : RelAmple B L) : IsProjBy B.hom := by
  obtain ⟨d, -, n, σ, hσ⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  exact ⟨_, isLB_pw hL _, n, σ, hσ⟩

theorem triv_lam_of_levels (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {O : LB B.left} (hO : O.IsLB)
    (h : ∀ e, Triv ((abelian₂ B O).pull (fstG (IsLocalRing.maximalIdeal V) e (B ⊗ B)).left)) : Triv (abelian₂ B O) :=
  AbTriv.triv_of_forall_thick hG V (B ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB)
    (isProjBy_tensor V _ _ hp hp) _ (LB.isLB_linComb hO _ _) h

end GlobalTheory.WtTower
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift
open GlobalTheory.CompleteBaseExpansion

theorem exists_lift : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  intro A A' S _ _ _ g' g hlift X X' XS f f' fS β σ hs hp pb' pbS W L K _ φ φ' ε hL hφ hH s'
  obtain rfl : (fun k => β ≫ φ k) = φ' := funext hφ
  have hN := DVR.linComb_isLB L hL φ ε
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A X f hs hp _ hN
  have pb₀ : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec A (RingHom.id A) X (𝟙 _) f pb₀
  obtain ⟨E, H⟩ := P.sec A' g' X' β f' pb'
  obtain ⟨t', ht'⟩ := exists_in (φ := φ) β s'
  obtain ⟨v, hv, hv'⟩ := hlift P.a P.b P.c P.D₀ P.D₁ P.comp (P.exact S g XS σ fS pbS hH) _ (E.symm t').2
  have hv₀ : (P.D₀.map (RingHom.id A)).mulVec v = 0 := hv
  have hs' := (GlobalTheory.SecAlg.sval_eq_iff (P := P) hN H₀ H g' (RingHom.comp_id _) β (Category.comp_id _) pb'.w
    (E₀ ⟨v, hv₀⟩) t').2 (fun k => by rw [E₀.symm_apply_apply]; exact hv' k)
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) (E₀ ⟨v, hv₀⟩)
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hG : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) := fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' z _ hG).trans ((ht' _ _ z _ (hG.mem (fun _ : PUnit => β) _)).trans ?_))
  · exact (sval_of (E₀ ⟨v, hv₀⟩) _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of s' _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

end GlobalTheory.SecLift
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlgLinComb
open GlobalTheory.CompleteBaseExpansion GlobalTheory.BaseExpansionExists

theorem exists_sec_linComb : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  intro R _ _ I hI Y hsm hp W L K _ φ ε φ' hL hφ f hf
  obtain rfl : φ' = fun e k => (fstG I e Y).left ≫ φ k := funext fun e => funext fun k => (hφ e k).symm
  choose f' hf' using fun e => exists_in (φ := φ) (fstG I e Y).left (f e)
  obtain ⟨s', hs', -⟩ := GlobalTheory.SecAlg.existsUnique_sec R I hI Y hsm hp _ (DVR.linComb_isLB _ hL _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) Y).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _)).symm)
      have E : thickMap R I e Y ≫ (fstG I (e + 1) Y).left = 𝟙 _ ≫ (fstG I e Y).left :=
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval hL _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φ i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  have key : ∀ e z J, Good L z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
    refine fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)
    have hN : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) :=
      fun ψ => hJ.mem _ ψ
    refine Eq.trans ?_ ((hs' e z _ hN).trans
      ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e Y).left) _)).trans ?_))
    · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
    · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm
  refine ⟨s, fun e Z r z J hJ => (sval_eq_of_id (key e) r z hJ).trans ?_⟩
  exact congrArg (fun p => sval (f e) p z J) (Category.comp_id _)

end GlobalTheory.SecAlgLinComb
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 := by
  first | exact @GlobalTheory.FormVan.form_eq_zero | exact GlobalTheory.FormVan.form_eq_zero | (intros; apply GlobalTheory.FormVan.form_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  first | exact @GlobalTheory.TrivSubscheme.exists_closed_locTriv | exact GlobalTheory.TrivSubscheme.exists_closed_locTriv | (intros; apply GlobalTheory.TrivSubscheme.exists_closed_locTriv <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpFrac

def sc {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem gs_inv {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (a : F) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) = sc p z a := by
  rw [gs_eq p z ⊤ trivial]; rfl

theorem gs_scal {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (z : Z)
    (a : F) : gs r z ⊤ (scal p a) = sc (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (gs_inv _ z a)

theorem sc_map {F F' : Type} [CommRing F] [CommRing F'] (φ : F →+* F') {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of F')) (z : Z) (a : F) :
    sc (p ≫ Spec.map (CommRingCat.ofHom φ)) z a = sc p z (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [sc, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, e]

theorem jFK_self (R : Type) [CommRing R] [IsDomain R] :
    jFK (R := R) (FractionRing R) = 𝟙 (Spec (CommRingCat.of (FractionRing R))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem clear_sum {R S : Type} [CommRing R] [IsDomain R] [CommRing S] (χ : FractionRing R →+* S) {n : ℕ} (r : R)
    (a : Fin n → R) (c : Fin n → FractionRing R) (h : ∀ i, algebraMap R (FractionRing R) (a i) = r • c i)
    (v : Fin n → S) :
    ∑ i, χ (algebraMap R _ (a i)) * v i = χ (algebraMap R _ r) * ∑ i, χ (c i) * v i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i, Algebra.smul_def, map_mul, _root_.mul_assoc]

theorem expands_of_expF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨n, c, σs, fs, hT, hA, hB⟩ := hE
  obtain ⟨⟨r, hr⟩, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose a ha using ha
  obtain ⟨σ', f', hT', hσ', hf'⟩ := ExpLin.expT_linear R I D.toPre A G U (𝟙_ _) k n
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) σs fs hT
  obtain ⟨-, e₁, -, e₂⟩ := UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ, hτ⟩ := e₁ σ'
  obtain ⟨f, hf⟩ := e₂ f'
  have hAt := fun τ' => expandsAt_of_expT R I D A G U U' hM k τ' τ σ' f f'
  have hG : GeneratorPullback.SecScal U.P.L.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) τ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) := by
    refine BoxFamScalar.secScal_of_pointwise U.P.L.isLB fun y J hJ => ?_
    obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (𝟙 _ ≫ pullback.fst G.hom (jK R))
    choose JA hJA using fun ψ : pullback G.hom (jK R) ⟶ A.A.left => exists_chart A.isLB (ψ y)
    have w : pullback.snd G.hom (jK R) ≫ (TFK (R := R) (FractionRing R)).hom = U.gen.hom.left ≫ A.A.hom :=
      ((congrArg (pullback.snd G.hom (jK R) ≫ ·) (jFK_self R)).trans (Category.comp_id _)).trans
        (Over.w U.gen.hom).symm
    obtain ⟨rA, hA₁, hA₂⟩ : ∃ rA : pullback G.hom (jK R) ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left,
        rA ≫ (fst _ A.A).left = pullback.snd G.hom (jK R) ∧ rA ≫ (snd _ A.A).left = 𝟙 _ ≫ U.gen.hom.left :=
      ⟨pullback.lift _ _ w, pullback.lift_fst _ _ w, (pullback.lift_snd _ _ w).trans (Category.id_comp _).symm⟩
    have e₃ := (hK _ rA (𝟙 _) hA₂ y JA J hJA hJ).symm.trans (hA _ rA (𝟙 _) rG hA₂ hG₁ y JA J hJA hJ)
    have e₄ : rG ≫ (fst _ G).left = pullback.snd G.hom (jK R) ≫ jK R :=
      hG₂.trans ((congrArg (· ≫ G.hom) (Category.id_comp _)).trans pullback.condition)
    refine ((congrArg (fun q => sval τ q y J) hG₁).symm.trans (hτ _ rG y J hJ).symm).trans
      ((hσ' _ rG y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (pullback.snd G.hom (jK R)) y) r a c ha (fun i => sval (σs i) rG y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · rw [gs_scal, Category.id_comp, sc_map]
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) hA₁)).symm
  have hF : ∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r) := by
    intro α
    refine BoxFamScalar.secScal_of_pointwise D.toPre.P.isLB fun y J hJ => ?_
    obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left)
    have e₃ := hB α _ (𝟙 _) rB hB₁ y J hJ
    have e₅ : (DegPre.BF D.toPre (FractionRing R)).hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm.trans (congrArg
        ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ ·)
        ((congrArg (· ≫ jK R) (jFK_self R)).trans (Category.id_comp _)))
    have e₄ : rB ≫ (fst _ D.toPre.P.A).left = (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      hB₂.trans ((congrArg (· ≫ D.toPre.P.A.hom) (Category.id_comp _)).trans
        ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans e₅))
    refine ((congrArg (fun q => sval (f α) q y J) hB₁).symm.trans (hf α _ rB y J hJ).symm).trans
      ((hf' α _ rB y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y) r a c ha
      (fun i => sval (fs i α) rB y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · exact ((gs_scal _ _ y _).trans ((congrArg (fun q => sc q y r) ((Category.id_comp _).trans e₅)).trans
          (sc_map _ _ y _))).symm
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) (Category.id_comp _))).symm
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  have hL := hM.LG
  dsimp only at hL
  subst hL
  obtain rfl := eq_of_heq hσ
  exact ⟨r, nonZeroDivisors.ne_zero hr, τ, f, hG, hF, hAt τ HEq.rfl hτ hf hT'⟩

end GlobalTheory.UU.ExpFrac
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_integral_addition_formula_group : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  first | exact @GlobalTheory.UU.exists_addG | exact GlobalTheory.UU.exists_addG | (intros; apply GlobalTheory.UU.exists_addG <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.familyFunctionalEquation_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  first | exact @GlobalTheory.famFE_field_change | exact GlobalTheory.famFE_field_change | (intros; apply GlobalTheory.famFE_field_change <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaPowers_expansion_support_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  first | exact @GlobalTheory.UU.exists_pow_exp_supp | exact GlobalTheory.UU.exists_pow_exp_supp | (intros; apply GlobalTheory.UU.exists_pow_exp_supp <;> assumption)
end
