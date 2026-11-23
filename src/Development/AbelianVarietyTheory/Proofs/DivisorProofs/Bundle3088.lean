module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTLevelLift

theorem existsUnique_torsion_lift_thick (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) (n : ℕ) (hn : IsUnit (n : C))
    (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A]
    (i : A₀.left ⟶ A.left) (hA : IsAbelianScheme A) (hpb : IsGrpPullback A₀ A (spMap π) i)
    (s₀ : 𝟙_ (Over (Sp C₀)) ⟶ A₀) (hs₀ : s₀ ^ n = 1) :
    ∃! s : 𝟙_ (Over (Sp C)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp C₀) := 𝟙_ (Over (Sp C₀))
  let T : Over (Sp C) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp C)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp C)}, ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_surjective f (CommRingCat.ofHom π) hπ hnil (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp C))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp C)) ⟶ A)
  let s : 𝟙_ (Over (Sp C)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp C)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp C)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

theorem map_nsmul_pow {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ x y, f (x + y) = f x * f y)
    (n : ℕ) (x : La) : f (n • x) = f x ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem level_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → N.Coprime p → ∀ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB → IsSquare i φ₂ → LBIso o₀.P (P.pull φ₂) → ∃ eta : D.La → (𝟙_ (Over (Sp C)) ⟶ A), (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ (∀ x, eta (N • x) = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∃ I : GlobalTheory.UPel.HT.TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) ∧ ∀ y, (o₀.eta y).left ≫ i = spMap π ≫ (eta y).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hN P φ₂ hP hsqr hLB
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, hsq⟩
  have hNu : IsUnit (N : C) := by simpa using (b.unit N hN).map tR
  have hlift := fun y => existsUnique_torsion_lift_thick C C₀ π hπ hnil N hNu o₀.A A i hA h (o₀.eta y)
      (by rw [← map_nsmul_pow o₀.eta o₀.eta_add, o₀.eta_ker])
  choose eta hspec huniq using hlift
  let TT : Over (Sp C) := Over.mk ((𝟙_ (Over (Sp C₀))).hom ≫ spMap π)
  let u : TT ⟶ 𝟙_ (Over (Sp C)) := toUnit TT
  have hu : u.left = spMap π := by simpa [TT] using Over.w u
  have hcomp : ∀ s : 𝟙_ (Over (Sp C)) ⟶ A, (u ≫ s).left = spMap π ≫ s.left := fun s => by
    rw [Over.comp_left, hu]
  have hadd : ∀ x y, eta (x + y) = eta x * eta y := by
    intro x y
    refine (huniq (x + y) _ ⟨by rw [mul_pow, (hspec x).1, (hspec y).1, _root_.one_mul], ?_⟩).symm
    have e := h.2 (𝟙_ (Over (Sp C₀))) (o₀.eta x) (o₀.eta y) (u ≫ eta x) (u ≫ eta y)
      (by rw [hcomp, (hspec x).2]) (by rw [hcomp, (hspec y).2])
    rw [o₀.eta_add, ← e, ← MonObj.comp_mul, hcomp]
  refine ⟨eta, hadd, ?_, ?_, ?_, fun y => (hspec y).2⟩
  · intro c x
    haveI := act.hom c
    haveI := o₀.act.hom c
    refine (huniq (c • x) _ ⟨by rw [← MonObj.pow_comp, (hspec x).1, MonObj.one_comp], ?_⟩).symm
    rw [o₀.eta_lin, Over.comp_left, Category.assoc, hact, ← Category.assoc, (hspec x).2, Over.comp_left,
      Category.assoc]
  · intro x
    rw [map_nsmul_pow eta hadd, (hspec x).1]
  · intro k _ _ x β hxβ
    obtain ⟨φ, hφx⟩ := Spec.map_surjective x
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := by
      intro a ha
      have h2 : a * a ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha ha
      rw [hsq] at h2
      have h3 : φ.hom (a * a) = 0 := by
        rw [show a * a = 0 from h2, map_zero]
      rw [RingHom.mem_ker]
      rw [map_mul] at h3
      exact mul_self_eq_zero.mp h3
    let φ₀ : C₀ →+* k := π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨φ.hom, hker⟩
    have hφ : φ₀.comp π = φ.hom := RingHom.liftOfRightInverse_comp _ _ _ _
    have hx : x = spMap φ₀ ≫ spMap π := by
      rw [← hφx]
      show Spec.map φ = Spec.map (CommRingCat.ofHom φ₀) ≫ Spec.map (CommRingCat.ofHom π)
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [← hφ]
    subst hx
    obtain ⟨I₀, hI₀⟩ := o₀.geom k (spMap φ₀) β (by rw [← Category.assoc]; exact hxβ)
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (spMap φ₀)) (spMap φ₀ ≫ spMap π) rfl
    have hd : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ φ₂ = i ≫ (lift (𝟙 A) (𝟙 A)).left :=
      GlobalTheory.AxisTrivExt.lift_match hsqr.1 hsqr.2 (𝟙 o₀.A) (𝟙 o₀.A) (𝟙 A) (𝟙 A) (by simp) (by simp)
    have a3 : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)
        ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pullback hLB _
    have b1 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pull_pull hP _ hd.symm
    have b2 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      GenSpread.lbIso_pull_pull hP i rfl
    have iD : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
        (LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) a3 b1.symm) b2
    have lin : ∀ (c : D.O) (g : Over.mk (spMap φ₀) ⟶ o₀.A), e (g ≫ o₀.act.act c) = e g ≫ act.act c := fun c g =>
      Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    refine ⟨{ ζ := I₀.ζ
              ζ_prim := I₀.ζ_prim
              ζ_pow := I₀.ζ_pow
              ev := fun n y => e (I₀.ev n y)
              add := fun n y y' => by simp only [I₀.add, map_mul]
              lin := fun n c y => by simp only [I₀.lin, lin]
              ker := fun n hn hp y => by
                rw [← I₀.ker n hn hp y]
                exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              onto := fun n hn hp q => by
                obtain ⟨q, rfl⟩ := e.surjective q
                rw [← map_pow]
                refine Iff.trans ?_ ((I₀.onto n hn hp q).trans ?_)
                · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
                · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
              tower := fun n m hn hm hp y => by rw [← map_pow, I₀.tower n m hn hm hp y]
              isom := fun n hn hp y y' =>
                (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ A o₀.A (spMap π) i _ _ (pull_isLB hP _)
                  (pull_isLB o₀.isLB _) h iD (Over.mk (spMap φ₀)) n _ _ (e (I₀.ev n y)) (e (I₀.ev n y')) _
                  (he _) (he _)).1 (I₀.isom n hn hp y y') }, fun y => ?_⟩
    show toUnit _ ≫ eta y = e (I₀.ev N y)
    rw [← hI₀ y]
    have e₁ : (toUnit (Over.mk (spMap φ₀))).left = spMap φ₀ := by simpa using Over.w (toUnit (Over.mk (spMap φ₀)))
    have e₂ : (toUnit (Over.mk (spMap φ₀ ≫ spMap π))).left = spMap φ₀ ≫ spMap π := by
      simpa using Over.w (toUnit (Over.mk (spMap φ₀ ≫ spMap π)))
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, (hspec y).2, e₁, e₂, Category.assoc]

end GlobalTheory.HTLevelLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleIso_mumford_of_generic_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  first | exact @GlobalTheory.Mum.lbIso_lam_of_extLam | exact GlobalTheory.Mum.lbIso_lam_of_extLam | (intros; apply GlobalTheory.Mum.lbIso_lam_of_extLam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegLev

section
variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h n ζ s}
  {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {d d' d'' : ℕ}

theorem sRel_trans (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c d' d f) (e : ℕ) : SRel c' c (d' * e) (d * e) f :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.2 e

end

theorem spMap_id_eq (o : Type) [CommRing o] : spMap (RingHom.id o) = 𝟙 _ := Spec.map_id _

theorem sFam_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N →
    Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  intro h n N o _ _ b hn hN hnN ⟨F⟩
  set ζ : o := (b.ζ : o) ^ (N / n)

  obtain ⟨c₀, h₀₁, h₀₂⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X F.X (F.s ≫ spMap (RingHom.id o)) F.s (𝟙 _) rfl
    (by simp)).2.2 F.univ
  have r₀₁ : SRel F.univ c₀ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₁
  have r₀₂ : SRel c₀ F.univ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₂
  have p₀ : c₀.Principal := sRel_principal r₀₂ F.princ
  obtain ⟨S₁, π, C, hfin, het, hsurj, hlow, huniv⟩ :=
    GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N o o ζ b (RingHom.id o) F.X F.s c₀ hn hN hnN rfl p₀
  have hN0 : N ≠ 0 := hN.pos.ne'
  have pC : C.Principal := sRel_principal hlow p₀
  refine ⟨{
    X := S₁
    s := π ≫ F.s
    smooth := by
      haveI := F.smooth
      have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
      rwa [zero_add] at this
    qproj := GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase o _ _ π F.s hfin F.qproj
    univ := C
    princ := pC
    rep := ?_
    inj := ?_ }⟩
  · intro T s' c hred hdense hp
    obtain ⟨cl, hcl1, hcl2⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o ζ (b.ζ : o) (RingHom.id o) T s' c hN0 b.unit hnN rfl
    have pl : cl.Principal := sRel_principal hcl2 hp
    obtain ⟨f, hf, hfp⟩ := F.rep T (s' ≫ spMap (RingHom.id o)) cl hred
      (by rw [spMap_id_eq, Category.comp_id]; exact hdense) pl
    rw [spMap_id_eq, Category.comp_id] at hf
    subst hf
    have r1 : SRel c F.univ (N / n) 1 (𝟙 _ ≫ f) := sRel_trans ((sRel_one_one_iff _ _ _).2 hfp) hcl1
    have r2 : SRel c c₀ (N / n) 1 ((𝟙 _ ≫ f) ≫ 𝟙 _) := sRel_trans r₀₁ r1
    obtain ⟨t₁, ⟨ht₁, hC⟩, -⟩ := huniv T f c (by simpa using r2)
    exact ⟨t₁, by rw [← Category.assoc, ht₁], hC⟩
  · intro R _ _ x y s' c hxy hx hy
    have rx : SRel c C 1 1 x := (sRel_one_one_iff _ _ _).2 hx
    have ry : SRel c C 1 1 y := (sRel_one_one_iff _ _ _).2 hy
    have kx : SRel c c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale rx (N / n))
    have ky : SRel c c₀ (N / n) 1 (y ≫ π) := sRel_trans hlow (by simpa using sRel_scale ry (N / n))

    obtain ⟨cx, hcx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X (Sp R) (F.s ≫ spMap (RingHom.id o))
      ((x ≫ π) ≫ F.s) (x ≫ π) rfl (by simp)).1 c₀
    have e1 : SRel cx c₀ 1 1 (x ≫ π) := (sRel_one_one_iff _ _ _).2 hcx
    have e2 : SRel cx c 1 (N / n) (𝟙 _) := sRel_cancel (f' := 𝟙 _) kx (by simpa using e1)
    have e3 : SRel cx c₀ 1 1 (𝟙 _ ≫ y ≫ π) := sRel_trans ky e2
    have fx : SiegPB cx F.univ (x ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e1)
    have fy : SiegPB cx F.univ (y ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e3)
    have hπ : x ≫ π = y ≫ π := F.inj R (x ≫ π) (y ≫ π) _ cx (by simpa using hxy) fx fy

    obtain ⟨Cx, hCx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h N o o (b.ζ : o) (b.ζ : o) (RingHom.id o) S₁ (Sp R) (π ≫ F.s)
      ((x ≫ π) ≫ F.s) x rfl (by rw [spMap_id_eq]; simp)).1 C
    have g1 : SRel Cx C 1 1 x := (sRel_one_one_iff _ _ _).2 hCx
    have g2 : SRel Cx c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale g1 (N / n))
    have g3 : SRel Cx c 1 1 (𝟙 _) := sRel_cancel (f' := 𝟙 _) rx (by simpa using g1)
    have g4 : SiegPB Cx C y := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans ry g3)
    exact (huniv (Sp R) (x ≫ π) Cx g2).unique ⟨rfl, hCx⟩ ⟨hπ.symm, g4⟩

end GlobalTheory.SiegLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

variable {O : Type} [Ring O] {bar : O → O}

theorem isPeriod_comp_symm {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D' : PLat O bar}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) :
    IsPeriod D' ρ (P.comp w.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hr : (P.comp w.symm.toAddEquiv.toAddMonoidHom).range = P.range := by
    ext z
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [h1]
  · exact h2.comp w.symm.injective
  · rw [hr]; exact h3
  · have : Set.range (P.comp w.symm.toAddEquiv.toAddMonoidHom) = Set.range P := by
      rw [← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    rw [this]; exact h4
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hEF, ← hw]
    simp

def unifClass {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (y : Sp ℂ ⟶ F.X) : Set ((D' : PLat O bar) × (Λ → D'.La)) :=
  {p | C p.1 p.2 ∧ ∃ P e, UnifAt F (RingHom.id ℂ) ρ N p.1 p.2 P y e}

theorem unifClass_eq {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) {N : ℕ}
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (hN : 0 < N) {y : Sp ℂ ⟶ F.X} {D₀ : PLat O bar}
    {t₀ : Λ → D₀.La} {P₀ : D₀.La →+ (Fin g → ℂ)} {e₀ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F (RingHom.id ℂ) ρ N D₀ t₀ P₀ y e₀) :
    unifClass F ρ N C y = {p | C p.1 p.2 ∧ ∃ w, IsMarkedIsom N D₀ p.1 t₀ p.2 w} := by
  ext ⟨D', t'⟩
  constructor
  · rintro ⟨hC, P, e, hU'⟩
    obtain ⟨w, -, hw, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ P y e₀ e hN hU hU'
    exact ⟨hC, w, hw⟩
  · rintro ⟨hC, w, hw⟩
    exact ⟨hC, P₀.comp w.symm.toAddEquiv.toAddMonoidHom, _,
      GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ (P₀.comp w.symm.toAddEquiv.toAddMonoidHom) y e₀ w
        (LinearEquiv.refl ℂ _) hN hU hw (fun x => by simp) (isPeriod_comp_symm hU.2.1 w hw.1)⟩

theorem exists_finite_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hF
  have : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
  have hlft : LocallyOfFiniteType F.s := inferInstance

  have hloc : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
      (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∀ b₀ ∈ B,
      ∀ᶠ b in nhds b₀, unifClass F ρ N C (y b) = unifClass F ρ N C (y b₀) := by
    intro B y hB hy hhol b₀ hb₀
    obtain ⟨D₀, t₀, P₀, e₀, -, hU₀⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb₀', -, -, -, -, hU⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D₀ t₀ d B y b₀ P₀ e₀ hN heta hlft hB hb₀ hy hhol hU₀
    filter_upwards [hB'.mem_nhds hb₀'] with b hb
    rw [unifClass_eq F ρ C hN (hU b hb), unifClass_eq F ρ C hN hU₀]
  have hfin := GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families
    GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d _ (unifClass F ρ N C) hsm hqc hloc
  set T := unifClass F ρ N C '' {x | x ≫ F.s = spMap (RingHom.id ℂ)} with hT
  haveI := hfin.fintype
  let E := (Fintype.equivFin T).symm
  have hch : ∀ c : T, ∃ (p : (D' : PLat O bar) × (Λ → D'.La)) (y : Sp ℂ ⟶ F.X), unifClass F ρ N C y = c.1 ∧ p ∈ unifClass F ρ N C y := by
    rintro ⟨c, y, hy, rfl⟩
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    exact ⟨⟨D', t'⟩, y, rfl, hC, P, e, hU⟩
  choose p y hcls hmem using hch
  refine ⟨Fintype.card T, fun i => (p (E i)).1, fun i => (p (E i)).2, fun i => ?_, ?_, ?_⟩
  · obtain ⟨hC, P, e, hU⟩ := hmem (E i)
    exact ⟨hC, P, hU.2.1⟩
  · rintro D' t' hC ⟨P, hP⟩
    obtain ⟨y', e', hU'⟩ := hF.occ D' t' P hC hP
    let c : T := ⟨unifClass F ρ N C y', y', hU'.1, rfl⟩
    refine ⟨E.symm c, ?_⟩
    have h1 : p (E (E.symm c)) ∈ unifClass F ρ N C y' := by
      have := hmem (E (E.symm c))
      have h2 : ((E (E.symm c)) : Set ((D' : PLat O bar) × (Λ → D'.La))) = unifClass F ρ N C y' :=
        congrArg Subtype.val (E.apply_symm_apply c)
      rwa [hcls, h2] at this
    rw [unifClass_eq F ρ C hN hU'] at h1
    exact h1.2
  · intro i j w hw
    apply E.injective
    apply Subtype.ext
    obtain ⟨hCi, Pi, ei, hUi⟩ := hmem (E i)
    obtain ⟨hCj, Pj, ej, hUj⟩ := hmem (E j)
    have hj' : p (E j) ∈ unifClass F ρ N C (y (E i)) := by
      rw [unifClass_eq F ρ C hN hUi]
      exact ⟨hCj, w, hw⟩
    obtain ⟨-, Pj', ej', hUj'⟩ := hj'
    rw [← hcls, ← hcls, unifClass_eq F ρ C hN hUj', unifClass_eq F ρ C hN hUj]

end GlobalTheory.PELU
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  first | exact @GlobalTheory.Mum.exists_open_theta_descent | exact GlobalTheory.Mum.exists_open_theta_descent | (intros; apply GlobalTheory.Mum.exists_open_theta_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ → ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) → ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) → ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  first | exact @GlobalTheory.Mum.GalFibre.exists_act_apply_eq | exact GlobalTheory.Mum.GalFibre.exists_act_apply_eq | (intros; apply GlobalTheory.Mum.GalFibre.exists_act_apply_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  first | exact @GlobalTheory.InvAlg.completion_invariants_agree | exact GlobalTheory.InvAlg.completion_invariants_agree | (intros; apply GlobalTheory.InvAlg.completion_invariants_agree <;> assumption)
end
