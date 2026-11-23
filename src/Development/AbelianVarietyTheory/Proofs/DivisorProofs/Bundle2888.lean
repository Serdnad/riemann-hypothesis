module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemSpanCstOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Fiber
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem trF_sum_elim {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    (φ₁ : K → (Y ⟶ X)) (φ₂ : K' → (Y ⟶ X)) (ε₁ : K → ℤ) (ε₂ : K' → ℤ) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (q q' : K' → L.ι) :
    trF (Sum.elim φ₁ φ₂) (Sum.elim ε₁ ε₂) r z (Sum.elim p q) (Sum.elim p' q') =
      trF φ₁ ε₁ r z p p' * trF φ₂ ε₂ r z q q' := by
  rw [trF, trF, trF, Fintype.prod_sum_type]; rfl

theorem trF_self' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (hp : r z ∈ LB.wchart L φ p) :
    trF φ ε r z p p = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hp k), _root_.one_zpow]

theorem iso_linComb_pull_glue : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  intro X X' Y M hM L' hL' K K' _ _ φ ε ψ e F w₁ hw₁ u hu

  have memE : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (p : K → M.ι) (q : K' → M.ι),
      F (f z) ∈ LB.wchart M φ p → f z ∈ LB.wchart M ψ q →
      f z ∈ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := by
    intro Z f z p q hp hq
    refine Set.mem_iInter.2 fun k => ?_
    cases k with
    | inl k => exact Set.mem_iInter.1 hp k
    | inr i => exact Set.mem_iInter.1 hq i

  have key : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j' : L'.ι) (q : K' → M.ι) (p p' : K → M.ι),
      F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q → F (f z) ∈ LB.wchart M φ p → F (f z) ∈ LB.wchart M φ p' →
      gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ =
        gm f z _ (u.s (Sum.elim p' q)) * (gm (f ≫ F) z _ (w₁.s (p', j')))⁻¹ := by
    intro Z f z j' q p p' hj hq hp hp'
    have a := gen_trans hu f z (memE f z p q hp hq) (memE f z p' q hp' hq)
    rw [trF_sum_elim, trF_self' hM ψ _ f z q hq, _root_.mul_one] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p' j' j' hp hp' hj hj
    have c : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p') = trF (fun k => F ≫ φ k) ε f z p p' := by
      refine (gm_linComb M φ ε (f ≫ F) z p p' hp hp').trans ?_
      simp only [trF, Category.assoc]
    rw [c, gm_self hL' (f ≫ F) z hj, inv_one, _root_.mul_one] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q)) (u.s (Sum.elim p q)) * (gv w₁ (f ≫ F) z p j')⁻¹ =
      gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p' q)) (u.s (Sum.elim p' q)) * (gv w₁ (f ≫ F) z p' j')⁻¹
    rw [a, b]
    generalize trF (fun k => F ≫ φ k) ε f z p p' = T
    generalize gm f z _ (u.s (Sum.elim p' q)) = U
    generalize gv w₁ (f ≫ F) z p' j' = V
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (j' : L'.ι) (q : K' → M.ι),
      ∃ s : Γ(X, (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q →
        F (f z) ∈ LB.wchart M φ p →
        gm f z _ s = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ := by
    intro j' q
    obtain ⟨W, hW⟩ : ∃ W : (K → M.ι) → X.Opens, ∀ p x, x ∈ W p ↔
        F x ∈ L'.U j' ∧ x ∈ LB.wchart M ψ q ∧ F x ∈ LB.wchart M φ p :=
      ⟨fun p => F ⁻¹ᵁ L'.U j' ⊓ (LB.wchart M ψ q ⊓ F ⁻¹ᵁ LB.wchart M φ p), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ p, W p ≤ (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q := fun p x hx =>
      ⟨mem_pull.2 ((hW p x).1 hx).1, ((hW p x).1 hx).2.1⟩
    have l₁ : ∀ p, W p ≤ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := fun p x hx =>
      memE (𝟙 X) x p q ((hW p x).1 hx).2.2 ((hW p x).1 hx).2.1
    have l₂ : ∀ p, W p ≤ F ⁻¹ᵁ (LB.wchart M φ p ⊓ L'.U j') := fun p x hx =>
      ⟨((hW p x).1 hx).2.2, ((hW p x).1 hx).1⟩
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X, W p)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), f z ∈ W p →
        gm f z (W p) (v p) = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ :=
      ⟨fun p => res (l₁ p) (u.s (Sum.elim p q)) * (res (l₂ p) (pullU F _ (w₁.s (p, j'))))⁻¹,
        fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₁ p) hz _)
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₂ p) hz _).trans (gm_pull f F z _ (l₂ p hz) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose p hp using fun k => exists_chart hM (φ k (F x))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, (hW p x).2 ⟨mem_pull.1 hx.1, hx.2, Set.mem_iInter.2 hp⟩⟩) v (fun p p' x hx => by
        have h₁ := (hW p x).1 hx.1
        have h₂ := (hW p' x).1 hx.2
        exact (hv _ (𝟙 X) x p hx.1).trans ((key (𝟙 X) x j' q p p' h₁.1 h₁.2.1 h₁.2.2 h₂.2.2).trans
          (hv _ (𝟙 X) x p' hx.2).symm))
    refine ⟨s, fun Z f z p hj hq hp => ?_⟩
    have hz := (hW p (f z)).2 ⟨hj, hq, hp⟩
    exact (gm_res f z (l₀ p) hz s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hv Z f z p hz))
  choose s hs using glue
  refine ⟨⟨fun P => s (P.1 PUnit.unit) P.2⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z f z j j' (k : K' → M.ι) (k' : K' → M.ι) hj hj' hk hk'
    choose p hp using fun a => exists_chart hM (φ a (F (f z)))
    have hpm : F (f z) ∈ LB.wchart M φ p := Set.mem_iInter.2 hp
    show gm f z _ (s j k) = gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      gm f z _ (s j' k')
    rw [hs j k Z f z p hj hk hpm, hs j' k' Z f z p hj' hk' hpm]
    have a := gen_trans hu f z (memE f z p k hpm hk) (memE f z p k' hpm hk')
    rw [trF_sum_elim, trF_self' hM (fun a => F ≫ φ a) ε f z p (Set.mem_iInter.2 fun a => Set.mem_iInter.1 hpm a), _root_.one_mul] at a
    have c : gm f z _ ((LB.LinComb M ψ e).g k k') = trF ψ e f z k k' := gm_linComb M ψ e f z k k' hk hk'
    have d : trF ψ (fun i => - e i) f z k k' = (trF ψ e f z k k')⁻¹ := by
      simp only [trF, zpow_neg, Finset.prod_inv_distrib]
    rw [d] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p j j' hpm hpm hj hj'
    have c' : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p) = 1 :=
      (gm_linComb M φ ε (f ≫ F) z p p hpm hpm).trans (trF_self' hM φ ε (f ≫ F) z p hpm)
    rw [c', _root_.one_mul] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k)) (u.s (Sum.elim p k)) * (gv w₁ (f ≫ F) z p j)⁻¹ =
      gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      (gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k')) (u.s (Sum.elim p k')) * (gv w₁ (f ≫ F) z p j')⁻¹)
    rw [a, b, c]
    generalize trF ψ e f z k k' = T
    generalize gm f z _ (u.s (Sum.elim p k')) = U
    generalize gv w₁ (f ≫ F) z p j' = V
    generalize gm (f ≫ F) z _ (L'.g j j') = G
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro Z f z J hJ j' hj
    have hp : F (f z) ∈ LB.wchart M φ (fun k => J ((f ≫ F) ≫ φ k)) :=
      Set.mem_iInter.2 fun k => hJ ((f ≫ F) ≫ φ k)
    show gm f z _ (s j' (fun i => J (f ≫ ψ i))) = _
    rw [hs j' _ Z f z _ hj (hJ.mem ψ f) hp,
      val_of u f z J (Sum.elim (fun k => J ((f ≫ F) ≫ φ k)) (fun i => J (f ≫ ψ i)))
        (by rintro (k | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.assoc])]
    exact mul_comm _ _

end GlobalTheory.Mum
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → (∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → Function.Injective φ := by
  first | exact @GlobalTheory.ValInj.injective_of_val | exact GlobalTheory.ValInj.injective_of_val | (intros; apply GlobalTheory.ValInj.injective_of_val <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  first | exact @GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | exact GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | (intros; apply GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.transitionUnit_pointValue_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' → valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val = valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  first | exact @GlobalTheory.CocVal.valR_cocycle | exact GlobalTheory.CocVal.valR_cocycle | (intros; apply GlobalTheory.CocVal.valR_cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_of_closedPoints_closedFibre_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R),
    LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) →
    ∀ x : T, q x = closedPoint R → x ∈ U := by
  intro R _ _ T q hq U hU x hx
  by_contra hxU
  set c : Sp R := closedPoint R
  have hc : IsClosed ({c} : Set (Sp R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
  have hft : LocallyOfFiniteType (q.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : JacobsonSpace (q.fiber c) := LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)
  let e := q.fiberι c
  have hemb : Topology.IsClosedEmbedding e := by
    refine ⟨IsPreimmersion.isEmbedding e, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hc.preimage q.continuous
  let Z : Set T := closure {x} ∩ (U : Set T)ᶜ
  have hZ : IsClosed Z := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨x', hx'⟩ : x ∈ Set.range e := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  have hne : (e ⁻¹' Z).Nonempty := ⟨x', by
    show e x' ∈ Z
    rw [hx']; exact ⟨subset_closure rfl, hxU⟩⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed
  have hyc' : IsClosed ({e y} : Set T) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hyc
  have hqy : q (e y) = c := by
    have : e y ∈ Set.range e := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact hyZ.2 (hU _ hyc' hqy)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.affineOpen_ring_normal_charZero_finiteType_over_int : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  first | exact @GlobalTheory.KeyVals.ring_of_isAffineOpen | exact GlobalTheory.KeyVals.ring_of_isAffineOpen | (intros; apply GlobalTheory.KeyVals.ring_of_isAffineOpen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] (g : Sp Ω ⟶ Sp R), (∀ w, g w = closedPoint R) → ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  first | exact @GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | exact GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | (intros; apply GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaDown

theorem isThetaPt_of_map : ∀ (B : Scheme.{0}) [IsLocallyNoetherian B] (P : PolAV B) (K C : Type) [Field K] [Field C] (j : K →+* C) (s : Sp K ⟶ B) (x : Sp C ⟶ B) (hx : spMap j ≫ s = x) (k : ℕ) (J : Type) (p : J → (Over.mk s ⟶ P.A)) (w : J → K), (∀ i, p i ^ k ^ 2 = 1) → IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (j (w i))) → IsThetaPt P k p (fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (w i)) := by
  intro B _ P K C _ _ j s x hx k J p w hp H
  have h₁ : Laws := GlobalTheory.firstFiveLaws.1
  have h₂ : Laws2 := GlobalTheory.firstFiveLaws.2.1
  have hk : Odd k := H.1
  let eC : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  have hkC : (k : C) ≠ 0 := by
    have := H.2.1.map eC.toRingHom
    rw [map_natCast] at this
    exact this.ne_zero
  have hkK : IsUnit (k : K) := IsUnit.mk0 _ fun h0 => hkC (by rw [← map_natCast j, h0, map_zero])
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local h₁ h₂ P s hk hkK p hp
  have hC := GlobalTheory.Ex.Specialise.isThetaPt_map h₂ P j hx hw₀
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := eC.symm.isLocalRing
  obtain ⟨u, hu⟩ := GlobalTheory.ThetaUniq.exists_unit_over h₁.globalFns P hk
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x hC) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x H)
  set c : C := eC (u : Γ((Over.mk x).left, ⊤)) with hcdef
  have hc : ∀ i, j (w i) = c * j (w₀ i) := fun i => by
    have q := (congrArg eC (hu i)).trans (map_mul eC _ _)
    exact (eC.apply_symm_apply (j (w i))).symm.trans (q.trans (congrArg (_ * ·) (eC.apply_symm_apply (j (w₀ i)))))
  have hu0 : c ≠ 0 := fun h0 => (u.isUnit.map eC.toRingHom).ne_zero h0
  by_cases hz : ∀ i, w₀ i = 0
  · have e : w = w₀ := funext fun i => j.injective (by rw [hc, hz, map_zero, MulZeroClass.mul_zero])
    subst e
    exact hw₀
  · push_neg at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hd : j (w i₀ / w₀ i₀) = c := by
      rw [map_div₀, hc, mul_div_assoc, div_self ((map_ne_zero j).2 hi₀), _root_.mul_one]
    have hd0 : w i₀ / w₀ i₀ ≠ 0 := fun h0 => hu0 (by rw [← hd, h0, map_zero])
    have e : ∀ i, w i = (w i₀ / w₀ i₀) * w₀ i := fun i => j.injective (by rw [map_mul, hd, hc])
    have := GlobalTheory.Ex.Specialise.isThetaPt_mul P hw₀ hd0
    convert this using 2 with i
    rw [e i]

end GlobalTheory.Mum.ThetaDown
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def ChartExpOn (U : UnifPre I D A G) (e k : ℕ) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W)) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      i' 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res ((inf_le_left.trans inf_le_left).trans inf_le_left :
          U.expW e p i' S jf jt ⊓ W ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_right :
          U.expW e p i' S jf jt ⊓ W ≤ W)).op).hom g =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt α.2))).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt α.2)) (((U.gt e).t α.1).s (jt α.1))).val

end GlobalTheory.MumMult
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem IntFam.exists_expandsAt_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α : D.toPre.X, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R))) → ∃ σ : H0 U.LG.L k, ∀ e : ℕ, U.ExpandsAt e k σ f := by
  intro R _ _ _ hR D A G _ _ hG U k hk F f hf
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 F
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ f h₁ hE
  exact ⟨σ, GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr σ σ₀ f f₀ hσ h₁ hE⟩

end GlobalTheory.Mum
end
