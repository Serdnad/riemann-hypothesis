module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.LocSecOfImm

theorem bij_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) [IsOpenImmersion q] (U : Y.Opens) (hU : U ≤ q.opensRange)
    (V : X.Opens) (h : V ≤ q ⁻¹ᵁ U) (h' : q ⁻¹ᵁ U ≤ V) : Function.Bijective (q.appLE U V h).hom := by
  obtain rfl : V = q ⁻¹ᵁ U := le_antisymm h h'
  have := q.isIso_app U hU
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (q.app U)

theorem appLE_res {X Y : Scheme.{0}} (q : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (e' : V ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : (q.appLE U' V e).hom (resG Y h a) = (q.appLE U V e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)

theorem res_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V' ≤ V) (e : V ≤ q ⁻¹ᵁ U)
    (e' : V' ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : resG X h ((q.appLE U V e).hom a) = (q.appLE U V' e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)

theorem appLE_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hr : p ≫ q = r) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ p ⁻¹ᵁ V) (e₃ : W ≤ r ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (p.appLE V W e₂).hom ((q.appLE U V e₁).hom a) = (r.appLE U W e₃).hom a := by
  subst hr
  exact congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)

theorem valF_ne_zero_of_le {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (a : Γ(X, U))
    (hle : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a) : valF x U a ≠ 0 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dite_eq_left h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  intro h0
  rw [e3, h0, map_zero, Scheme.basicOpen_zero] at hle
  exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem exists_point {X Y : Scheme.{0}} {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  intro S G _ L R _ χ _ σ hft hnz
  let q : (Over.mk χ ⊗ G).left ⟶ G.left := (snd (Over.mk χ) G).left
  have hq : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))
  have ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ :=
    (Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm
  have hN : ∀ y, G.hom (q y) ∈ χ.opensRange := fun y => by
    rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange := fun y hy =>
    (Scheme.Pullback.range_snd χ G.hom).ge hy
  have hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤
      q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩
  have hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange)
      ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom := fun i =>
    bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1
  choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)
  have hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact hs i
  refine ⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩
  · have hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤
        q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun y hy =>
      ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩
    refine (bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy =>
      ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_
    have hc := σ.compat (fun _ => i) (fun _ => j)
    rw [← hs i, ← hs j] at hc
    rw [map_mul]
    refine (appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans
      (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm
      simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    · exact (res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm
  · rintro _ ⟨y, rfl⟩
    exact ⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · show genPull _ s j = (SecAt.pull G L σ i).f j
    unfold genPull SecAt.pull VVRank.pullS VVRank.pullTo
    dsimp only
    rw [← hs' j]
    exact (appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm
  · obtain ⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange := hx ⟨_, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hnz s₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    rw [← hs' j] at hj
    have hb := ((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2
    obtain ⟨y, hy, hy'⟩ := exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by
      rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]
      exact hs₀)
    refine ⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩
    rintro _ ⟨a, rfl⟩
    exact G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))

end GlobalTheory.UMin.LocSecOfImm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem cross_resG_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V W : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (s : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom s) = (f.appLE U W (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem cross_resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    resG X h2 (resG X h1 s) = resG X (h2.trans h1) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

theorem cross_resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) : resG X h s = s := by
  change (X.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cross_appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (s : Γ(Y, U')) :
    (f.appLE U V e).hom (resG Y h s) = (f.appLE U' V (e.trans fun _ hx => h hx)).hom s := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem cross_ratio_val {k Ω : Type} [CommRing k] [Field Ω] {n : ℕ} {x : Sp Ω ⟶ PSpace k n}
    {c : Fin (n + 1) → Ω} (hc : PCrd x c) {U : (PSpace k n).Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) {a : Fin (n + 1)}
    (ha : U ≤ chart k n a) :
    c a ≠ 0 ∧ ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b * (c a)⁻¹) := by
  obtain ⟨τ, -, H⟩ := hc
  have h1 : ((O1 k n).pull x).U (fun _ => a) ≤ x ⁻¹ᵁ (O1 k n).U a :=
    LB.wchart_le (O1 k n) (fun _ => x) (fun _ => a) PUnit.unit
  have h2 : ⊤ ≤ ((O1 k n).pull x).U (fun _ => a) :=
    fun y hy => Set.mem_iInter.2 fun _ => ha (hU hy)
  set t : Γ(Sp Ω, ⊤) := resG _ h2 (τ.s (fun _ => a)).val with ht
  have key : ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b) * t := by
    intro b
    have e := congrArg (resG _ h2) (H b (fun _ => a) h1)
    rw [map_mul, cross_resG_appLE] at e
    have e2 : ratioOn U a ha b = resG _ ha (ratio k n a b) := rfl
    rw [e2, cross_appLE_resG]
    refine e.trans (congrArg (· * t) ?_)
    exact (cross_resG_resG _ _ _).trans (cross_resG_self _ _)
  have ka := key a
  rw [ratioOn_self, map_one] at ka
  have hne : c a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ka
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ka
    rw [map_one, map_zero] at this
    exact one_ne_zero (α := Ω) this
  refine ⟨hne, fun b => ?_⟩
  rw [key, map_mul]
  congr 1
  have : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) = 1 := by
    rw [← map_mul]
    exact (congrArg _ (inv_mul_cancel₀ hne)).trans (map_one _)
  calc t = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) * t) := by rw [← _root_.mul_assoc, this, _root_.one_mul]
    _ = _ := by rw [← ka, _root_.mul_one]

theorem cross_pull_base {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    {N : S.Opens} (hN : ⊤ ≤ ξ ⁻¹ᵁ N) {V : G.left.Opens} (hV : V ≤ G.hom ⁻¹ᵁ N) {W : (Over.mk ξ ⊗ G).left.Opens}
    (hW : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ V) (r : Γ(S, N)) :
    ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) := by
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  have e1 : ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      (G.hom.appLE N V hV ≫ (snd (Over.mk ξ) G).left.appLE V W hW).hom r := rfl
  have e2 : liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) =
      (ξ.appLE N ⊤ hN ≫ (fst (Over.mk ξ) G).left.appLE ⊤ W le_top).hom r := rfl
  rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  simp only [e]

theorem cross_ratio_sections : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  intro k Ω _ _ _ M G _ L n c h v hc huniq a b sa sb ha hb i
  by_cases hne : ((h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · have hbot : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) = ⊥ :=
      eq_bot_iff.2 fun y hy => hne ⟨_, hy.2⟩
    have : Subsingleton Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨ha1, ha2⟩ := ha (hne.mono (show (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) ≤ h ⁻¹ᵁ chart k n a from fun _ hx => hx.1))
  obtain ⟨hb1, hb2⟩ := hb (hne.mono (show (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) ≤ h ⁻¹ᵁ chart k n b from fun _ hx => hx.2))
  have htop := M.top_le_preimage_pt hne
  have hr : Set.range M.pt ⊆ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) :=
    (top_le_preimage_iff _ _).1 htop
  have htop' : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (chart k n a ⊓ chart k n b) := htop
  obtain ⟨hca, hra⟩ := cross_ratio_val hc htop' inf_le_left
  obtain ⟨hcb, -⟩ := cross_ratio_val hc htop' inf_le_right
  let s₂ : LocSec G L (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) := fun i =>
    resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i)
  have g₂ : GenIs M.pt s₂ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v) := by
    refine ⟨hr, funext fun j => ?_⟩
    have e3 := congrFun hb2 j
    simp only [genPull, s₂] at e3 ⊢
    rw [map_mul, cross_pull_base G M.pt htop]
    refine (congrArg (_ * ·) ((cross_appLE_resG _ _ _ _).trans e3)).trans ?_
    have e4 : (M.pt.appLE _ ⊤ htop).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b)) =
        ((M.pt ≫ h).appLE _ ⊤ htop').hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e4, hra]
    change liftHom G _ _ * (liftHom G _ _ * v.1 j) = liftHom G _ _ * v.1 j
    rw [← _root_.mul_assoc, ← map_mul]
    congr 2
    erw [← map_mul]
    congr 1
    change c b * (c a)⁻¹ * (c b)⁻¹ = (c a)⁻¹
    field_simp
  have e := congrArg (resG _ (fun _ hx => ⟨hx.1, hx.2.1, hx.2⟩ :
    L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
      L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a ⊓ h ⁻¹ᵁ (chart k n a ⊓ chart k n b))))
    (huniq _ _ sa s₂ _ ⟨ha1, ha2⟩ g₂ i)
  exact (cross_resG_resG _ _ _).symm.trans (e.trans ((cross_resG_resG _ _ _).trans (cross_resG_self _ _)))

end GlobalTheory.UMin.ThBdl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

open Matrix

def formPolUnit (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, Matrix.single_apply]⟩

theorem idem_mul_formPolUnit (d : ℕ) : idem d * formPolUnit d = polUnit d := by
  ext1
  show single (Sum.inl 0) (Sum.inl 0) 1 * (form d * single (Sum.inl 0) (Sum.inr 0) 1) = single (Sum.inl 0) (Sum.inr 0) 1
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem bar_formPolUnit_mul_idem {d : ℕ} (hd : 0 < d) : bar d (formPolUnit d) * idem d = bar d (formPolUnit d) := by
  ext1
  have e : ((bar d (formPolUnit d) : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * single (Sum.inr 0) (Sum.inl 0) 1 := by
    rw [bar_coe]
    show form d * (form d * single (Sum.inl 0) (Sum.inr 0) 1)ᵀ * formInv d = _
    rw [Matrix.transpose_mul, form_transpose, Matrix.transpose_single, Matrix.mul_assoc, Matrix.mul_assoc,
      form_mul_formInv hd, Matrix.mul_one]
  rw [Subring.coe_mul, e]
  show form d * single (Sum.inr 0) (Sum.inl 0) 1 * single (Sum.inl 0) (Sum.inl 0) 1 = _
  rw [Matrix.mul_assoc, Matrix.single_mul_single_same, _root_.mul_one]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam.KerSup

variable {X Y : Scheme.{0}}

theorem exists_gen_of_lbIso' {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullId P) (chartPullPull Q (𝟙 X)) h
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X)) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem gen_pull_comp (L : LB X) (f : Y ⟶ X) {Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull (h ≫ f)), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  exact gen_chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl)) t ht

theorem gen_congr (L : LB X) {f g : Y ⟶ X} (e : f = g)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull g), t.IsGen := by
  subst e; exact H

theorem lbIso_pull_comp (L : LB X) {f g : Y ⟶ X} {Y' : Scheme.{0}} (h : Y' ⟶ Y) (H : LBIso (L.pull f) (L.pull g)) :
    LBIso (L.pull (h ≫ f)) (L.pull (h ≫ g)) :=
  H.chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl))
    (chartPullSame L (fun _ => h ≫ g) (fun _ => g) (fun _ => 1) h (fun _ => rfl))

theorem lbIso_pull_pull {L : LB X} {M : LB Y} {j : X ⟶ Y} {Y' : Scheme.{0}} (h : Y' ⟶ X) (H : LBIso L (M.pull j)) :
    LBIso (L.pull h) (M.pull (h ≫ j)) := by
  have a : ChartPull (L.pull h) L h := chartPullPull L h
  have b : ChartPull (M.pull (h ≫ j)) (M.pull j) h :=
    chartPullSame M (fun _ => h ≫ j) (fun _ => j) (fun _ => 1) h (fun _ => rfl)
  exact LBIso.chartPull a b H

end GlobalTheory.ZarhinFam.KerSup

namespace GlobalTheory.ZarhinFam

theorem ker_pol_le_ker_polUnit : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  intro h M d hd S t c z act inc pr hdu hker hz hact hadj hinc hpr hip hpi hP T x hx
  have hNp : act (polUnit d) = act (idem d) ≫ act (formPolUnit d) := by
    rw [← idem_mul_formPolUnit, hact.2.2.1]
  have hbar : act (bar d (formPolUnit d)) ≫ pr ≫ inc = act (bar d (formPolUnit d)) := by
    rw [hpi, ← hact.2.2.1, bar_formPolUnit_mul_idem hd]
  have hy : x ≫ inc ≫ act (polUnit d) = x ≫ inc ≫ act (formPolUnit d) := by
    rw [hNp, ← hpi]
    simp only [Category.assoc]
    rw [← Category.assoc inc pr, hip, Category.id_comp]
  rw [hy]
  apply hz.2 T
  let q : z.A ⟶ c.A := act (bar d (formPolUnit d)) ≫ pr
  let ψ₁ : z.A ⊗ T ⟶ c.A ⊗ c.A := lift (snd z.A T ≫ x) (fst z.A T ≫ q)
  let φ : z.A ⊗ T ⟶ z.A ⊗ z.A := lift (snd z.A T ≫ x ≫ inc) (fst z.A T)
  have g1 : ∃ u : (c.P.pull ψ₁.left).Gen, u.IsGen := by
    have := KerSup.gen_pull_comp c.P _ (lift (fst z.A T ≫ q) (snd z.A T)).left hx
    refine KerSup.gen_congr c.P ?_ this
    rw [← Over.comp_left]
    congr 1
    simp [ψ₁]
  have g2 : ∃ u : (z.P.pull (ψ₁.left ≫ (inc ⊗ₘ inc).left)).Gen, u.IsGen :=
    KerSup.exists_gen_of_lbIso' (pull_isLB c.isLB _) (pull_isLB z.isLB _) (KerSup.lbIso_pull_pull ψ₁.left hP) g1
  have e3 : ψ₁.left ≫ (inc ⊗ₘ inc).left =
      φ.left ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (formPolUnit d)))).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [ψ₁, φ, q, lift_map, comp_lift, lift_fst, lift_snd_assoc, Category.assoc, hbar]
  have i4 := KerSup.lbIso_pull_comp z.P φ.left (hadj (formPolUnit d))
  have g4 := KerSup.exists_gen_of_lbIso' (pull_isLB z.isLB _) (pull_isLB z.isLB _) i4.symm
    (KerSup.gen_congr z.P e3 g2)
  refine KerSup.gen_congr z.P ?_ g4
  rw [← Over.comp_left]
  congr 1
  simp [φ]

end GlobalTheory.ZarhinFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psiCoordinate_norm_chart_eq_coordinate_norm_padicDVR : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  first | exact @GlobalTheory.PsiNormCoord.main | exact GlobalTheory.PsiNormCoord.main | (intros; apply GlobalTheory.PsiNormCoord.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  first | exact @GlobalTheory.UnifTorsK.psiNormAt_pull | exact GlobalTheory.UnifTorsK.psiNormAt_pull | (intros; apply GlobalTheory.UnifTorsK.psiNormAt_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (exact GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_linLevel <;> assumption)
end
