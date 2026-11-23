module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnivBasisMove

open GlobalTheory.ThetaReal GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ}

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (s : SecM A L₁ a T) (s₀ : SecM G L₀ a T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    ThetaAct.sv s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * ThetaAct.sv s r z J'

theorem exists_rel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s₀ : SecM G L₀ a T₀) :
    ∃ s, Rel hp τ hτ w s s₀ := by
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ (SecM.toSec G s₀)
  exact ⟨SecM.ofSec A s, hs⟩

theorem exists_rel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s : SecM A L₁ a T) :
    ∃ s₀, Rel hp τ hτ w s s₀ := by
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ (SecM.toSec A s)
  exact ⟨SecM.ofSec G s₀, hs⟩

variable {hp τ hτ}

theorem Rel.unique_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s s' : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s' s₀) : s = s' :=
  ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    exact (Units.mul_right_inj _).1 ((h _ _ _ _ _ hJ hJ').symm.trans (h' _ _ _ _ _ hJ hJ'))

theorem Rel.unique_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s : SecM A L₁ a T} {s₀ s₀' : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s s₀') : s₀ = s₀' :=
  ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    have q := (h _ χ y _ _ hJ hJ').trans (h' _ χ y _ _ hJ hJ').symm
    rwa [h₂'] at q

theorem Rel.add {s t : SecM A L₁ a T} {s₀ t₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w t t₀) : Rel hp τ hτ w (s + t) (s₀ + t₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', h' _ _ _ _ _ hJ hJ', mul_add]

theorem Rel.smul {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (c : Γ(T₀.left, ⊤))
    (h : Rel hp τ hτ w s s₀) : Rel hp τ hτ w (τ.appTop.hom c • s) (c • s₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', mul_left_comm,
      Category.assoc, psi_fst', ← Category.assoc]
    exact congrArg (fun x => _ * (x * _)) (gs_pull _ τ z ⊤ trivial c).symm

theorem Rel.pull {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (h : Rel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (σ : T'.left ⟶ T₀'.left) (hσ : σ ≫ T₀'.hom = T'.hom ≫ f)
    (u : T' ⟶ T) (u₀ : T₀' ⟶ T₀) (hu : σ ≫ u₀.left = u.left ≫ τ) :
    Rel hp σ hσ w (VVRank.pullM A L₁ a u s) (VVRank.pullM G L₀ a u₀ s₀) :=
  fun Z r z J J' hJ hJ' => by
    have e : psi hp σ hσ ≫ (u₀ ▷ G).left = (u ▷ A).left ≫ psi hp τ hτ := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
          Category.assoc, Category.assoc, psi_fst', hu, ← Category.assoc (u ▷ A).left, ← Over.comp_left,
          whiskerRight_fst, Over.comp_left, Category.assoc]
      · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
          VVRank.whisker_snd_left]
    have q := h _ (r ≫ (u ▷ A).left) z _ _ hJ hJ'
    rw [Category.assoc, Category.assoc, ← e, VVRank.whisker_snd_left, ← Category.assoc] at q
    exact (VVRank.sv_pullS G a u₀ (SecM.toSec G s₀) _ z hJ).trans
      (q.trans (congrArg _ (VVRank.sv_pullS A a u (SecM.toSec A s) _ z hJ').symm))

theorem exists_linearEquiv (hp : IsGrpPullback A G f φ) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (a : ℤ) (T : Over S') :
    ∃ E : SecM G L₀ a (Over.mk (T.hom ≫ f)) ≃ₗ[Γ(T.left, ⊤)] SecM A L₁ a T,
      ∀ x, Rel hp (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) w (E x) x := by
  have : IsIso (C := Scheme.{0}) (X := T.left) (Y := (Over.mk (T.hom ≫ f)).left) (𝟙 T.left) := IsIso.id _
  choose D hD using exists_rel hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) (a := a)
    hw hL₀ hL₁
  let l : SecM G L₀ a (Over.mk (T.hom ≫ f)) →ₗ[Γ(T.left, ⊤)] SecM A L₁ a T :=
    { toFun := D
      map_add' := fun x y => (hD _).unique_down hL₀ hL₁ ((hD x).add (hD y))
      map_smul' := fun c x => (hD _).unique_down hL₀ hL₁ (Rel.smul (T₀ := Over.mk (T.hom ≫ f)) (τ := 𝟙 T.left) c (hD x)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun x y e => ?_, fun s => ?_⟩, hD⟩
  · have e' : D x = D y := e
    exact (hD x).unique_up hL₀ hL₁ (e' ▸ hD y)
  · obtain ⟨s₀, hs⟩ := exists_rel_up hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _)
      hw hL₀ hL₁ s
    exact ⟨s₀, (hD s₀).unique_down hL₀ hL₁ hs⟩

theorem univBasis_move : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  intro S S' f P P' φ hp hw n κ _ T₀ τ hτ b₀ hb₀
  obtain ⟨w, hw⟩ := hw
  have hτ' : τ ≫ T₀.hom = (baseOver S').hom ≫ f := hτ.trans (Category.id_comp _).symm
  choose b hb using fun i => exists_rel hp (T := baseOver S') τ hτ' hw P.isLB P'.isLB (b₀ i)
  refine ⟨b, fun T hT h => ?_⟩
  have hh : h.left = T.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk (T.hom ≫ τ) (by
    change (T.hom ≫ τ) ≫ T₀.hom = T.hom ≫ f
    rw [Category.assoc, hτ])
  have : IsAffine (Over.mk (T.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T
  refine ⟨Module.Basis.map (R := Γ(T.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ ((Category.id_comp _).trans (congrArg (· ≫ τ) hh.symm))

end GlobalTheory.UnivBasisMove
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.BasisBaseChange

open GlobalTheory.FieldBaseChange

section Algebra

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem basis_map_of_basis {φ : R →+* R'} (f : M →ₛₗ[φ] M') {I J : Type} [Fintype I] [Fintype J]
    (b : J → M) (β : I → M) (hb : ∀ s, ∃! a : J → R, s = ∑ j, a j • b j)
    (hβ : ∀ s, ∃! a : I → R, s = ∑ i, a i • β i)
    (hf : ∀ s, ∃! a : J → R', s = ∑ j, a j • f (b j)) (s : M') : ∃! a : I → R', s = ∑ i, a i • f (β i) := by
  classical
  choose u hu _ using fun i => hb (β i)
  choose w hw _ using fun j => hβ (b j)
  have huw : ∀ i i', ∑ j, u i j * w j i' = if i = i' then 1 else 0 := fun i => by
    have h1 : β i = ∑ i', (∑ j, u i j * w j i') • β i' := by
      conv_lhs => rw [hu i]
      simp only [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.smul_sum, ← hw j]
    have h2 : β i = ∑ i', (if i = i' then (1 : R) else 0) • β i' := by simp
    exact congrFun ((hβ (β i)).unique h1 h2)
  have fβ : ∀ a : I → R', ∑ i, a i • f (β i) = ∑ j, (∑ i, a i * φ (u i j)) • f (b j) := fun a => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [← Finset.smul_sum, hu i, map_sum]
    simp only [map_smulₛₗ, ← hu i]
  have fb : ∀ c : J → R', ∑ j, c j • f (b j) = ∑ i, (∑ j, c j * φ (w j i)) • f (β i) := fun c => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_

    rw [← Finset.smul_sum, hw j, map_sum]
    simp only [map_smulₛₗ, ← hw j]
  have back : ∀ (a : I → R') i', ∑ j, (∑ i, a i * φ (u i j)) * φ (w j i') = a i' := fun a i' => by
    simp only [Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]

    simp only [← Finset.mul_sum, ← map_sum, huw]
    simp [apply_ite φ]
  obtain ⟨c, hc, hcu⟩ := hf s
  refine ⟨_, hc.trans (fb c), fun a ha => funext fun i => ?_⟩
  rw [← hcu _ (ha.trans (fβ a)), back]

end Algebra

theorem isLin_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) {H : LB Y} {I : Type} [Fintype I]
    (s : I → SecOver p H) (a : I → R) (t : SecOver p H) : IsLin p s a t ↔ t = ∑ i, a i • s i := by
  have e : ∀ l, chartFun p H l (∑ i, a i • s i) = ∑ i, a i • chartFun p H l (s i) := fun l =>
    (map_sum (chartLin p H l) _ _).trans rfl
  exact ⟨fun h => SecOver.ext _ _ fun l => (h l).trans (e l).symm, fun h l => (congrArg (chartFun p H l) h).trans (e l)⟩

theorem basis_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {A : Over (Sp R)}
    {L : LB A.left} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (A.left ⟶ A.left)) (ε : K → ℤ) {m : ℕ}
    (b : Fin m → SecOver A.hom (LB.LinComb L ψ ε))
    (hb : IsSecBasis (T := Over.mk (spMap φ)) (A := A) _
      (fun i => DVR.pullSec L ψ ε (b i) (snd (Over.mk (spMap φ)) A).left))
    {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ A.left} (H : IsPullback π pB A.hom (spMap φ))
    {ψ' : K → (B ⟶ A.left)} (hψ : ∀ k, ψ' k = π ≫ ψ k) (s : SecOver pB (LB.LinComb L ψ' ε)) :
    ∃! a : Fin m → R', s = ∑ i, a i • pullOver L ε H.w hψ (b i) := by
  let T : Over (Sp R) := Over.mk (spMap φ)
  let p : (T ⊗ A).left ⟶ Sp R' := (fst T A).left
  let q : (T ⊗ A).left ⟶ A.left := (snd T A).left
  have H' : IsPullback q p A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) A.hom).flip
  let e := H.isoIsPullback _ _ H'
  have e1 : e.hom ≫ q = π := H.isoIsPullback_hom_fst _ _ H'
  have e2 : e.hom ≫ p = pB ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_hom_snd _ _ H'
  have e3 : e.inv ≫ π = q := H.isoIsPullback_inv_fst _ _ H'
  have e4 : e.inv ≫ pB = p ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_inv_snd _ _ H'
  have f1 : ∀ k, ψ' k = e.hom ≫ (q ≫ ψ k) := fun k => by rw [hψ, ← e1, Category.assoc]
  have f2 : ∀ k, q ≫ ψ k = e.inv ≫ ψ' k := fun k => by rw [hψ, ← e3, Category.assoc]
  let F := pullOver L ε e2 (φ := fun k => q ≫ ψ k) f1
  let G := pullOver L ε e4 (φ' := fun k => q ≫ ψ k) f2
  let b' : Fin m → SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε) := fun i => DVR.pullSec L ψ ε (b i) q
  have FG : ∀ t, F (G t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver e4 f2 _ _ hJ, Category.assoc, e.hom_inv_id, Category.comp_id]
  have GF : ∀ t, G (F t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e4 f2 _ _ hJ, sval_pullOver e2 f1 _ _ hJ, Category.assoc, e.inv_hom_id, Category.comp_id]
  have Fb : ∀ i, F (b' i) = pullOver L ε H.w hψ (b i) := fun i => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver H.w hψ _ _ hJ]
    exact (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.assoc, e1])
  have hb' : ∀ t : SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε), ∃! a : Fin m → R', t = ∑ i, a i • b' i := by
    intro t
    obtain ⟨r, hr, hu⟩ := hb t
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i), (isLin_iff p _ _ _).1 fun j => ?_,
      fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [constFn, e]
      rfl
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a i)) ((isLin_iff p _ _ _).2 ha)
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R')) (a i)).symm
  have Fs : ∀ a : Fin m → R', F (∑ i, a i • b' i) = ∑ i, a i • pullOver L ε H.w hψ (b i) := fun a => by

    simp only [map_sum, map_smulₛₗ, Fb, RingHom.id_apply]
  obtain ⟨a, ha, hu⟩ := hb' (G s)
  refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
  · show s = _
    rw [← Fs, ← ha, FG]
  · show G s = _
    rw [ha', ← Fs, GF]

theorem basis_pullback : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  intro hT R _ _ _ _ D N hN α R' _ φ B pB π H I _ β hβ s
  have hL := D.P.isLB
  obtain ⟨m, b, -, hb⟩ := hT R D N hN α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id R)) := by
    have : spMap (RingHom.id R) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := basis_of_isPullback (RingHom.id R) hL (D.famφB α) (DegPre.famε N) b
    (hb R (RingHom.id R) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε N) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have hψ : ∀ k, (fun i => π ≫ D.famφB α i) k = π ≫ D.famφB α k := fun _ => rfl
  have h1 := basis_of_isPullback φ hL (D.famφB α) (DegPre.famε N) b (hb R' φ _ fun _ _ => rfl) H hψ
  have h2 := basis_map_of_basis (pullOver D.P.L (DegPre.famε N) H.w hψ) b β h0
    (fun t => (existsUnique_congr fun a => isLin_iff D.P.A.hom β a t).1 (hβ t)) h1 s
  have e1 : ∀ i, pullOver D.P.L (DegPre.famε N) H.w hψ (β i) =
      DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H.w hψ _ _ hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm
  simp only [e1] at h2
  exact (existsUnique_congr fun a => isLin_iff pB _ a s).2 h2

end GlobalTheory.ZH.BasisBaseChange
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.PullDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem corr_of_val_genMap (hφ : Function.Injective φ) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {ψ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ (z : (TK R').left) (J : ((TK R').left ⟶ X) → L.ι), Good L z J →
      val t (genMap hφ) z J = val t' (genMap hφ) z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' :=
  corr_of_val_field_extension _ _ (fracMap hφ) X L hL K K' ψ ε ψ' ε' t t' h

theorem psiEven_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.PsiEven) :
    D.PsiEven := by
  intro χ
  obtain ⟨x, rfl⟩ := hD.xe.surjective χ
  refine corr_of_val_genMap hφ D.P.isLB fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) z
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have cW : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hφ ≫ D.xK (hD.xe x) := by
    rw [Category.id_comp]; exact cPoint_proj hD _ hh x
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  have e := val_corr hJ' (h x) (𝟙 (TK R').left)
  rw [val_mul hJ', val_pull hJ'] at e
  have a₁ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' (-x)
  have a₂ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' x
  have a₃ : val D.sym (genMap hφ ≫ D.xK (hD.xe x)) z J =
      om hD.w z J J' ((𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left) * (om hD.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ *
        val D'.sym (𝟙 _ ≫ D'.xK x) z J' :=
    (congrArg (fun q => val D.sym q z J) cW.symm).trans (PsiEvenPull.sym_pull hG hD _ z hJ hJ')
  rw [c', map_neg] at a₁
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) a₁ ((val_pull hJ _ _ _).trans a₃))
    (Eq.trans ?_ a₂.symm))
  rw [← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


theorem tauBimult_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.TauBimult) :
    D.TauBimult := by
  intro χ χ' ν
  obtain ⟨a, rfl⟩ := hD.xe.surjective χ
  obtain ⟨a', rfl⟩ := hD.xe.surjective χ'
  obtain ⟨b, rfl⟩ := hD.xe.surjective ν
  refine corr_of_val_genMap hφ D.P.isLB fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) y
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have gp := pull_grp hD
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk (genMap hφ) hh.symm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ proj hD = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => om hD.w (Z := (TK R').left) y J J' x.left
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' (T := TK R') y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => om hD.w (Z := (TK R').left) y J J' q)) rfl)
  let τ : D.X → D.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D.tau a b) (genMap hφ) y J
  let τ' : D'.X → D'.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D'.tau a b) (𝟙 (TK R').left) y J'
  have vτ : ∀ a b, τ (hD.xe a) (hD.xe b) =
      (Ω (cP D' _ a * cP D' _ b))⁻¹ * Ω (cP D' _ a) * Ω (cP D' _ b) * (Ω 1)⁻¹ * τ' a b := fun a b => by
    have e := tau_val hD (Z := (TK R').left) _ _ sq hJ hJ' a b
    simp only [Category.id_comp] at e
    rw [← cPoint_add]
    exact e
  have e : τ' (a + a') b * th D' (T := TK R') y J' (cP D' _ a) (cP D' _ a') (cP D' _ b) = τ' a b * τ' a' b := by
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_)
      ((val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (h a a' b) (𝟙 (TK R').left)).trans (val_mul hJ' _ _ _)))
    refine Eq.trans ?_ (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have key : τ (hD.xe a + hD.xe a') (hD.xe b) * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      τ (hD.xe a) (hD.xe b) * τ (hD.xe a') (hD.xe b) := by
    rw [← βc, ← βc, ← βc, cub, ← map_add (f := _), vτ, vτ, vτ, cPoint_add]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) key
  refine (val_cub D.cub κ hJ (cP D _ (hD.xe a)) (cP D _ (hD.xe a')) (cP D _ (hD.xe b))).trans ?_
  rw [comp_cP, comp_cP, comp_cP]

end GlobalTheory.PullDescent

namespace GlobalTheory

theorem psiEven_tauBimult_of_isPullDeg_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) :=
  fun hG _ _ _ _ _ _ _ hφ _ _ hD => ⟨PullDescent.psiEven_desc hG hφ hD, PullDescent.tauBimult_desc hG hφ hD⟩

end GlobalTheory
end
end
