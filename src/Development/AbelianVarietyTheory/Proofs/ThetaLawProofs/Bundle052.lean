module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.LamOfDouble

open GlobalTheory.CechPic

theorem isIso_of_factor {X Y Z : Scheme.{0}} (y : X ⟶ Z) (j : Z ⟶ Y) [Mono j] [Flat (y ≫ j)]
    [Surjective (y ≫ j)] [QuasiCompact (y ≫ j)] : IsIso j := by
  have : IsRegularEpi (y ≫ j) := inferInstance
  have : StrongEpi (y ≫ j) := inferInstance
  have : StrongEpi j := strongEpi_of_strongEpi y j
  exact isIso_of_mono_of_strongEpi j

theorem triv_of_pull_pow (hL : Out.Laws) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB) (ha : Out.RelAmple A M) (n : ℕ) (hn : 1 ≤ n)
    (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h0 : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (h1 : ∃ t : (N.pull (((𝟙 A) ^ n : A ⟶ A) ▷ A).left).Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen := by
  have hproj : IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A M hA hM ha R (𝟙 _) A.left (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv hL.globalFns R A A hA hproj N hN
  obtain ⟨t, ht⟩ := h1
  obtain ⟨y, hy⟩ := (hH A ((𝟙 A) ^ n)).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow hL R A hA M hM ha n hn
  have e : y.left ≫ j.left = ((𝟙 A) ^ n : A ⟶ A).left := congrArg (·.left) hy
  rw [← e] at f₁ f₂ f₃
  have : IsIso j.left := isIso_of_factor y.left j.left
  have hw : inv j.left ≫ H.hom = A.hom := by rw [← Over.w j, IsIso.inv_hom_id_assoc]
  have hloc := (hH A (𝟙 A)).2 ⟨Over.homMk (inv j.left) hw, Over.OverMorphism.ext (IsIso.inv_hom_id j.left)⟩
  have key : ∃ t : (N.pull (𝟙 A ▷ A).left).Gen, t.IsGen := by
    refine GlobalTheory.exists_gen_of_local_of_section (A ⊗ A).left A.left (fst A A).left
      (lift (𝟙 A) (1 : A ⟶ A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 A) (1 : A ⟶ A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ A hA _ _ A.hom _ _
        (GlobalTheory.SeesawGlobal.isPullback_tensor A A))
      hloc ?_
    rw [← cls_eq_zero_iff (pull_isLB (pull_isLB hN _) _), cls_pull (pull_isLB hN _), cls_pull hN, ← pull_comp,
      ← Over.comp_left, id_whiskerRight, Category.comp_id]
    exact (cls_eq_zero_iff (pull_isLB hN _)).2 h0
  rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, id_whiskerRight, Over.id_left, pull_id] at key
  exact (cls_eq_zero_iff hN).1 key

section Pair

variable {S : Scheme.{0}} {A T : Over S}

def ev (c : Pic (A ⊗ A).left) (x y : T ⟶ A) : Pic T.left := pull (lift x y).left c

theorem pull_ev {T' : Over S} (h : T' ⟶ T) (c : Pic (A ⊗ A).left) (x y : T ⟶ A) :
    pull h.left (ev c x y) = ev c (h ≫ x) (h ≫ y) := by
  rw [ev, ev, ← pull_comp, ← Over.comp_left, comp_lift]

variable [GrpObj A] [IsCommMonObj A]

def Biadd (c : Pic (A ⊗ A).left) : Prop :=
  ∀ (T : Over S) (x x' y : T ⟶ A), ev c (x * x') y = ev c x y + ev c x' y ∧ ev c y (x * x') = ev c y x + ev c y x'

theorem biadd_of_axes (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB)
    (ha : Out.RelAmple A M) (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h₁ : ∃ t : (N.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) : Biadd (cls N hN) := by
  intro T x x' y
  obtain ⟨a, b⟩ := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A M hA hM ha N hN h₁ h₂ T x x' y
  rw [← cls_eq_zero_iff (LB.isLB_linComb hN _ _), cls_linComb hN] at a b
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul,
    neg_smul] at a b
  constructor
  · unfold ev
    rw [← sub_eq_zero, ← a]
    abel
  · unfold ev
    rw [← sub_eq_zero, ← b]
    abel

end Pair

theorem lam_iso_of_pull_two : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → L.IsLB → LBIso (lbPow c.diag 2) (L.pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left) → LBIso (abelian₂ c.A L) c.P := by
  intro hL h k o _ ζ R _ _ _ β c L hc hLB hiso
  have hM : c.diag.IsLB := pull_isLB c.isLB _
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ c.A L) c.P).IsLB := LB.isLB_div hΛ c.isLB
  have hPow : (lbPow c.diag 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls c.P c.isLB with hp
  have eΛ : cls _ hΛ = lam l (fst c.A c.A) (snd c.A c.A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ c.isLB, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ev p (1 : c.A ⟶ c.A) (𝟙 c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₁
  have r₂ : ev p (𝟙 c.A) (1 : c.A ⟶ c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₂
  have n₁ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (𝟙 c.A) (1 : c.A ⟶ c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₂, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ hN n₁ n₂
  have bP : Biadd p := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ c.isLB c.rig₁ c.rig₂
  have sy : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev p x y = ev p y x := by
    intro T x y
    have e : p = ev p (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    calc ev p x y = pull (lift x y).left (ev p (snd c.A c.A) (fst c.A c.A)) := by rw [← e]; rfl
      _ = ev p y x := by rw [pull_ev, lift_fst, lift_snd]
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ c.A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 c.A) (𝟙 c.A) = pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₁ : ev p (1 : T ⟶ c.A) (1 : T ⟶ c.A) = 0 := by
        have := (bP T 1 1 1).1
        rw [_root_.mul_one] at this
        exact left_eq_add.1 this
      have o₂ := dbl T 1
      rw [_root_.mul_one, o₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL c.A c.ab _ hM hc.1 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst c.A c.A) (snd c.A c.A)))
    have e : ((𝟙 c.A) ^ 4 : c.A ⟶ c.A) ▷ c.A = lift (fst c.A c.A ^ 4) (snd c.A c.A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ c.isLB, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ c.isLB).1 fin

end GlobalTheory.LamOfDouble

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegDim

theorem card_torsion_of_level {G J : Type} [Group G] [Fintype J] (k : ℕ) (hk : k ≠ 0) (l : (J → ℤ) → G)
    (hadd : ∀ a b, l (a + b) = l a * l b) (htors : ∀ a, l a ^ k = 1)
    (hker : ∀ a, l a = 1 ↔ ∃ b, a = k • b) (hsurj : ∀ g : G, g ^ k = 1 → ∃ a, l a = g) :
    Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card J := by
  classical
  have : NeZero k := ⟨hk⟩
  have key : ∀ a b, l a = l b ↔ ∀ i, ((a i : ℤ) : ZMod k) = (b i : ℤ) := fun a b => by
    have e : l b = l a * l (b - a) := by rw [← hadd]; congr 1; abel
    rw [e, left_eq_mul, hker]
    constructor
    · rintro ⟨c, hc⟩ i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨c i, by simpa using congrFun hc i⟩
    · intro H
      choose c hc using fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (H i)
      exact ⟨c, funext fun i => by simpa using hc i⟩
  let F : (J → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨l fun i => ((c i).val : ℤ), htors _⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' e
      funext i
      simpa using (key _ _).1 (congrArg Subtype.val e) i
    · rintro ⟨g, hg⟩
      obtain ⟨a, rfl⟩ := hsurj g hg
      exact ⟨fun i => (a i : ZMod k), Subtype.ext ((key _ _).2 fun i => by simp)⟩
  rw [← Nat.card_eq_of_bijective F hF]
  simp [Nat.card_pi]

noncomputable def pointsEquiv {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) where
  toFun y := Over.homMk (y.left ≫ φ) (by simp [hp.1.w])
  invFun q := Over.homMk (hp.1.lift q.left T.hom (Over.w q)) (hp.1.lift_snd _ _ _)
  left_inv y := Over.OverMorphism.ext (hp.1.hom_ext (by simp) (by simp))
  right_inv q := Over.OverMorphism.ext (by simp)
  map_mul' y y' := Over.OverMorphism.ext (hp.2 T y y' _ _ rfl rfl).symm

theorem dim_geometric_fibre {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) {K : Type} [Field K] [IsAlgClosed K] (hK : (k : K) ≠ 0)
    (x : Sp K ⟶ S) {d : ℕ} (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj c.A).hom) : d = h := by
  let T := 𝟙_ (Over (Sp K))
  let β : o →+* K := (Spec.preimage ((T.hom ≫ x) ≫ s)).hom
  have hβ : (T.hom ≫ x) ≫ s = spMap β := (Spec.map_preimage ((T.hom ≫ x) ≫ s)).symm
  obtain ⟨h₁, h₂, -⟩ := c.geom K (T.hom ≫ x) β (hζ.map β).unit hβ rfl
  have n₁ := card_torsion_of_level k (by omega) (fun a => toUnit (Over.mk (T.hom ≫ x)) ≫ c.lev a)
    (fun a b => by rw [c.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]) h₁ h₂
  have := c.ab.comm
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback x).obj c.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd c.A.hom x); infer_instance
      proper := by change IsProper (pullback.snd c.A.hom x); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd c.A.hom x); infer_instance }
  have n₂ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional K _ d k hab hd hK
  let e := pointsEquiv (isGrpPullback_pullback c.A x) T
  have n₃ := Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun y => y ^ k = 1) (q := fun y => y ^ k = 1)
    fun y => by
      change _ ↔ e y ^ k = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  have n₄ : k ^ (2 * d) = k ^ (h + h) := by
    rw [← n₂, n₃, n₁]; simp
  have := Nat.pow_right_injective hk n₄
  omega

theorem smoothOfRelativeDimension :
    Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)), 2 ≤ k → IsUnit ζ → SmoothOfRelativeDimension h c.A.hom := by
  intro _ h k o _ ζ R _ _ β c hk hζ
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := (Sp R).residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ Sp R := spMap (algebraMap κ K) ≫ (Sp R).fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast ((Spec.preimage x).hom.comp (algebraMap ℚ R)) k
    rw [← this]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 (by omega))
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegDim
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.lam_iso_of_doubling_pullback_eq_diagonal_sq : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → L.IsLB → LBIso (lbPow c.diag 2) (L.pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left) → LBIso (abelian₂ c.A L) c.P := by
  first | exact @GlobalTheory.LamOfDouble.lam_iso_of_pull_two | exact GlobalTheory.LamOfDouble.lam_iso_of_pull_two | (intros; apply GlobalTheory.LamOfDouble.lam_iso_of_pull_two <;> assumption)

end
end
