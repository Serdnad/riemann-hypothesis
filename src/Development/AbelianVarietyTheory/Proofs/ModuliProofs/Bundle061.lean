module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle059
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LieCharpolyRootPairs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    liftConstHom p U a = constFn p U a := rfl

theorem liftConstHom_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHom p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_comm {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  apply _root_.GlobalTheory.KS.app_constFn_of_commK <;> assumption

theorem exists_locDer_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  intro R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHom p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHom_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHom q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_comm x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHom q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add (f := _)])
    (fun a b => by rw [hD.2, hc, hc, map_add (f := _), map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.exists_local_derivation_extension_of_affine R Y X q p m D W₀ hW d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

section

noncomputable section

namespace GlobalTheory.DetCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit

section Linear

variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

theorem exists_bijOn_iff (W : Submodule k N) (n : ℕ) :
    (∃ v : Fin n → N, (∀ i, v i ∈ W) ∧ Set.BijOn (fun c : Fin n → k => ∑ i, c i • v i) Set.univ W) ↔
      Module.Finite k W ∧ Module.finrank k W = n := by
  constructor
  · rintro ⟨v, -, hm, hi, hs⟩
    let f : (Fin n → k) →ₗ[k] W := (Fintype.linearCombination k v).codRestrict W fun c => hm trivial
    have hf : Function.Bijective f := by
      refine ⟨fun c c' h => hi trivial trivial (congrArg Subtype.val h), fun w => ?_⟩
      obtain ⟨c, -, hc⟩ := hs w.2
      exact ⟨c, Subtype.ext hc⟩
    have e := LinearEquiv.ofBijective f hf
    exact ⟨Module.Finite.equiv e, by simpa using e.finrank_eq.symm⟩
  · rintro ⟨_, h⟩
    let b := Module.finBasisOfFinrankEq k W h
    have hb : ∀ c : Fin n → k, ∑ i, c i • (b i : N) = (b.equivFun.symm c : W) := fun c => by
      simp [Module.Basis.equivFun_symm_apply]
    refine ⟨fun i => b i, fun i => (b i).2, fun c _ => ?_, fun c _ c' _ h => ?_, fun w hw => ?_⟩
    · simp only [hb]; exact Subtype.property _
    · simp only [hb] at h; exact b.equivFun.symm.injective (Subtype.ext h)
    · exact ⟨b.equivFun ⟨w, hw⟩, trivial, by simp only [hb, LinearEquiv.symm_apply_apply]⟩

end Linear

variable {S : Scheme.{0}} {k : Type} [Field k]

variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem mem_lie_iff (t : Sp k ⟶ S) (v : epsPt t ⟶ G) :
    v ∈ Lie G t ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left :=
  ⟨fun h => congrArg (fun φ => φ.left) (show origin t ≫ v = 1 from h), fun h => Over.OverMorphism.ext h⟩

theorem isLieEigen_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔ ∃ h : v ∈ Lie G t, (⟨v, h⟩ : Lie G t) ∈ eigenspace act t τ :=
  ⟨fun h => ⟨(mem_lie_iff t v).2 h.1, fun a => Subtype.ext (Over.OverMorphism.ext (h.2 a))⟩,
    fun ⟨h, h'⟩ => ⟨(mem_lie_iff t v).1 h, fun a => congrArg (fun φ : Lie G t => φ.1.left) (h' a)⟩⟩

variable [IsCommMonObj G]

theorem comb_iff {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) (w : epsPt t ⟶ G) :
    (∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).1.left) ∧ w = (List.ofFn u).prod) ↔
      w = (comb v c).1 := by
  have key : (comb v c).1 = (List.ofFn fun i => (smulLie (c i) (v i)).1).prod := by
    rw [List.prod_ofFn]
    exact SubmonoidClass.coe_finsetProd (fun i => smulLie (c i) (v i)) Finset.univ
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain rfl : u = fun i => (smulLie (c i) (v i)).1 := funext fun i => Over.OverMorphism.ext (hu i)
    exact key.symm
  · rintro rfl
    exact ⟨fun i => (smulLie (c i) (v i)).1, fun _ => rfl, key⟩

def lieEquiv (t : Sp k ⟶ S) : Lie G t ≃ TanSp t G where
  toFun v := TanSp.mk v.1 (smT_zero_of t _ ((mem_lie_iff t _).1 v.2))
  invFun m := ⟨m.pt, (mem_lie_iff t _).2 (unit_of_smT_zero t _ m.tan)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lieEquiv_smul {t : Sp k ⟶ S} (c : k) (v : Lie G t) : lieEquiv t (smulLie c v) = c • lieEquiv t v := rfl

theorem lieEquiv_act (act : OAct O G) (t : Sp k ⟶ S) (a : O) (v : Lie G t) :
    lieEquiv t (actLie act t a v) = TanSp.act t act a (lieEquiv t v) := rfl

theorem lieEquiv_comb {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) :
    lieEquiv t (comb v c) = ∑ i, c i • lieEquiv t (v i) := by
  apply TanSp.ext
  rw [TanSp.pt_sum]
  exact SubmonoidClass.coe_finsetProd (fun i => smulLie (c i) (v i)) Finset.univ

theorem mem_eigenspace_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : Lie G t) :
    v ∈ eigenspace act t τ ↔ lieEquiv t v ∈ eigenSub (TanSp.act t act) τ := by
  rw [mem_eigenSub]
  refine forall_congr' fun a => ?_
  rw [← lieEquiv_act, ← lieEquiv_smul, (lieEquiv t).injective.eq_iff]

theorem comb_mem {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by
  rw [mem_eigenspace_iff, lieEquiv_comb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((mem_eigenspace_iff act t τ _).1 (hv i))

theorem lieMult_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    LieMult act t τ n ↔ HasEigenDim act t τ n := by
  constructor
  · rintro ⟨v, hv, h⟩
    choose h1 h2 using fun i => (isLieEigen_iff act t τ _).1 (hv i)
    let v' : Fin n → Lie G t := fun i => ⟨v i, h1 i⟩
    have h' : ∀ w ∈ eigenspace act t τ, ∃! c, w = comb v' c := fun w hw => by
      have := h w.1 ((isLieEigen_iff act t τ _).2 ⟨w.2, hw⟩)
      exact (existsUnique_congr fun c => (comb_iff v' c w.1).trans Subtype.ext_iff.symm).1 this
    refine ⟨v', h2, fun c _ => comb_mem h2 c, fun c _ c' _ e => (h' _ (comb_mem h2 c)).unique rfl e,
      fun w hw => ?_⟩
    obtain ⟨c, hc, -⟩ := h' w hw
    exact ⟨c, trivial, hc.symm⟩
  · rintro ⟨v, hv, -, hi, hs⟩
    refine ⟨fun i => (v i).1, fun i => (isLieEigen_iff act t τ _).2 ⟨(v i).2, hv i⟩, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := (isLieEigen_iff act t τ _).1 hw
    obtain ⟨c, -, hc⟩ := hs h2
    refine (existsUnique_congr fun c => comb_iff v c w).2 ⟨c, (congrArg Subtype.val hc).symm, fun c' hc' => ?_⟩
    exact hi trivial trivial ((Subtype.ext hc' : (⟨w, h1⟩ : Lie G t) = comb v c').symm.trans hc.symm)

theorem hasEigenDim_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    HasEigenDim act t τ n ↔ Module.Finite k (eigenSub (TanSp.act t act) τ) ∧
      Module.finrank k (eigenSub (TanSp.act t act) τ) = n := by
  rw [← exists_bijOn_iff]
  refine (Equiv.piCongrRight fun _ => lieEquiv t).exists_congr fun v => and_congr
    (forall_congr' fun i => mem_eigenspace_iff act t τ _) ?_
  have h1 : (fun c : Fin n → k => ∑ i, c i • (Equiv.piCongrRight fun _ => lieEquiv t) v i) =
      lieEquiv t ∘ comb v := funext fun c => (lieEquiv_comb v c).symm
  have h2 : Set.BijOn (lieEquiv t) (eigenspace act t τ) (eigenSub (TanSp.act t act) τ) :=
    (lieEquiv t).bijOn (mem_eigenspace_iff act t τ · |>.symm)
  rw [h1]
  refine ⟨h2.comp, fun h => ?_⟩
  have := ((lieEquiv t).bijOn_symm.2 h2).comp h
  rwa [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp] at this

variable {E : Type} [Field E] [NumberField E]

theorem bijective_restrict [CharZero k] :
    Function.Bijective fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
  refine ⟨fun φ ψ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => RingHom.congr_fun h a, fun τ => ?_⟩
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_splitting [CharZero k] [IsAlgClosed k] :
    ∃ _ : Fintype (𝓞 E →+* k), IsSplitting fun τ : 𝓞 E →+* k => τ := by
  classical
  let e := Equiv.ofBijective _ (bijective_restrict (E := E) (k := k))
  let F : Fintype (𝓞 E →+* k) := Fintype.ofEquiv _ e
  refine ⟨F, isSplitting_of_isDomain (σ := fun τ : 𝓞 E →+* k => τ) Function.injective_id ?_ (RingHom.id k) ?_⟩
  · rw [← NumberField.Embeddings.card E k]
    exact Fintype.card_congr e.symm
  · simpa using NumberField.discr_ne_zero E

variable [IsCMField E]

end GlobalTheory.DetCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaCocycle

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def PullsBack (t' : TObj g k J β s') (t : TObj g k J β s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧ ∀ l, (t'.pt l).left ≫ φ = f ≫ (t.pt l).left

private theorem lbIso_pull_comp_of_lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {f : Y ⟶ X}
    (H : LBIso L' (L.pull f)) (c : Z ⟶ Y) : LBIso (L'.pull c) (L.pull (c ≫ f)) := by
  have a : ChartPull (L'.pull c) L' c :=
    ⟨fun J => J PUnit.unit, fun J y hy => Set.mem_iInter.1 hy PUnit.unit, fun y J J' hJ hJ' => by
      refine (gm_linComb L' (fun _ => c) (fun _ => 1) (𝟙 _) y J J' hJ hJ').trans ?_
      simp⟩
  exact LBIso.chartPull a (chartPullSame L (fun _ => c ≫ f) (fun _ => f) (fun _ => 1) c (fun _ => rfl)) H

theorem PullsBack.comp {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} {f' : S'' ⟶ S'} {f : S' ⟶ S}
    {h : S'' ⟶ S} {φ' : t''.A.left ⟶ t'.A.left} {φ : t'.A.left ⟶ t.A.left} (H' : PullsBack t'' t' f' φ')
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : PullsBack t'' t h (φ' ≫ φ) := by
  obtain ⟨g', l', p'⟩ := H'
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  refine ⟨g'.comp g₀, ?_, fun i => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB φ') (pull_isLB t.isLB (φ' ≫ φ)) l'
      (lbIso_pull_comp_of_lbIso_pull l₀ φ')
  · rw [reassoc_of% (p' i), p₀ i, Category.assoc]

theorem PullsBack.cancel {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} (f' : S'' ⟶ S') {f : S' ⟶ S}
    {h : S'' ⟶ S} {ψ : t''.A.left ⟶ t.A.left} {φ : t'.A.left ⟶ t.A.left} (H'' : PullsBack t'' t h ψ)
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : ∃ c, PullsBack t'' t' f' c ∧ c ≫ φ = ψ := by
  obtain ⟨g'', l'', p''⟩ := H''
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  have sq : ψ ≫ t.A.hom = (t''.A.hom ≫ f') ≫ f := by rw [g''.1.w, Category.assoc]
  set c := g₀.1.lift ψ (t''.A.hom ≫ f') sq with hcdef
  have hc₁ : c ≫ φ = ψ := g₀.1.lift_fst _ _ _
  have hc₂ : c ≫ t'.A.hom = t''.A.hom ≫ f' := g₀.1.lift_snd _ _ _
  refine ⟨c, ⟨g₀.cancel (by rw [hc₁]; exact g'') hc₂, ?_, fun i => ?_⟩, hc₁⟩
  · have l₁ := lbIso_pull_comp_of_lbIso_pull l₀ c
    rw [hc₁] at l₁
    exact LBIso.trans t''.isLB (pull_isLB t.isLB ψ) (pull_isLB t'.isLB c) l'' (LBIso.symm l₁)
  · apply g₀.1.hom_ext
    · rw [Category.assoc, hc₁, p'' i, Category.assoc, Category.assoc, p₀ i]
    · rw [Category.assoc, hc₂, ← Category.assoc, Over.w (t''.pt i), Category.assoc, Over.w (t'.pt i)]
      simp [Out.baseOver]

theorem cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  intro hex o _ g n J β S s I U t u a b ha hb hrig i j m T x y z hxy hxz
  have HA : ∀ i j, PullsBack (u i j) (t i) (S.homOfLE inf_le_left) (a i j) := ha
  have HB : ∀ i j, PullsBack (u i j) (t j) (S.homOfLE inf_le_right) (b i j) := hb
  let V : S.Opens := (U i ⊓ U j) ⊓ (U j ⊓ U m)
  have hVm : V ≤ U m := inf_le_right.trans inf_le_right
  have hVim : V ≤ U i ⊓ U m := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨t', φk, gk, lk, pk, -⟩ := hex o g n J β (U m).toScheme V.toScheme ((U m).ι ≫ s)
    (S.homOfLE hVm ≫ (U m).ι ≫ s) (S.homOfLE hVm) (t m) rfl
  have hk : PullsBack t' (t m) (S.homOfLE hVm) φk := ⟨gk, lk, pk⟩
  obtain ⟨c₁, h₁, e₁⟩ := PullsBack.cancel (S.homOfLE (inf_le_right : V ≤ U j ⊓ U m)) hk (HB j m) (by simp)
  have h₁' : PullsBack t' (t j) (S.homOfLE (inf_le_right.trans inf_le_left : V ≤ U j)) (c₁ ≫ a j m) :=
    h₁.comp (HA j m) (by simp)
  obtain ⟨c₂, h₂, e₂⟩ := PullsBack.cancel (S.homOfLE (inf_le_left : V ≤ U i ⊓ U j)) h₁' (HB i j) (by simp)
  have h₂' : PullsBack t' (t i) (S.homOfLE (inf_le_left.trans inf_le_left : V ≤ U i)) (c₂ ≫ a i j) :=
    h₂.comp (HA i j) (by simp)
  obtain ⟨c₃, h₃, e₃⟩ := PullsBack.cancel (S.homOfLE hVim) h₂' (HA i m) (by simp)
  have h₃' : PullsBack t' (t m) (S.homOfLE hVm) (c₃ ≫ b i m) := h₃.comp (HB i m) (by simp)
  have hφ : φk = c₃ ≫ b i m := hrig V.toScheme m (S.homOfLE hVm) t' φk (c₃ ≫ b i m) inferInstance hk.1 h₃'.1
    hk.2.1 h₃'.2.1 (fun l => by rw [hk.2.2 l, h₃'.2.2 l])
  have hq : (x ≫ (u i j).A.hom) ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) =
      (y ≫ (u j m).A.hom) ≫ S.homOfLE (inf_le_left : U j ⊓ U m ≤ U j) := by
    rw [Category.assoc, Category.assoc, ← (HB i j).1.1.w, ← (HA j m).1.1.w, ← Category.assoc, hxy, Category.assoc]
  have sq := isPullback_opens_inf_le (X := S) (inf_le_right : U i ⊓ U j ≤ U j) (inf_le_left : U j ⊓ U m ≤ U j)
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : T ⟶ V.toScheme, q ≫ S.homOfLE (inf_le_left : V ≤ U i ⊓ U j) = x ≫ (u i j).A.hom ∧
      q ≫ S.homOfLE (inf_le_right : V ≤ U j ⊓ U m) = y ≫ (u j m).A.hom :=
    ⟨sq.lift _ _ hq, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : T ⟶ t'.A.left, w ≫ c₁ = y ∧ w ≫ t'.A.hom = q :=
    ⟨h₁.1.1.lift y q hq₂.symm, h₁.1.1.lift_fst _ _ _, h₁.1.1.lift_snd _ _ _⟩
  have hwx : w ≫ c₂ = x := by
    apply (HB i j).1.1.hom_ext
    · rw [Category.assoc, e₂, ← Category.assoc, hw₁, hxy]
    · rw [Category.assoc, h₂.1.1.w, ← Category.assoc, hw₂, hq₁]
  have hbase : q ≫ S.homOfLE hVim = z ≫ (u i m).A.hom := by
    have e₅ : ∀ {W : Scheme.{0}} (h : W ⟶ (U i ⊓ U m).toScheme),
        h ≫ (U i ⊓ U m).ι = (h ≫ S.homOfLE (inf_le_left : U i ⊓ U m ≤ U i)) ≫ (U i).ι := fun h => by simp
    rw [← cancel_mono (U i ⊓ U m).ι, Category.assoc, Scheme.homOfLE_ι, e₅ (z ≫ (u i m).A.hom)]
    simp only [Category.assoc]
    rw [← reassoc_of% (HA i m).1.1.w, ← reassoc_of% hxz, reassoc_of% (HA i j).1.1.w, ← reassoc_of% hq₁]
    simp
  have hwz : w ≫ c₃ = z := by
    apply (HA i m).1.1.hom_ext
    · rw [Category.assoc, e₃, ← Category.assoc, hwx, hxz]
    · rw [Category.assoc, h₃.1.1.w, ← Category.assoc, hw₂, hbase]
  calc y ≫ b j m = w ≫ c₁ ≫ b j m := by rw [← Category.assoc, hw₁]
    _ = w ≫ c₃ ≫ b i m := by rw [e₁, hφ]
    _ = z ≫ b i m := by rw [← Category.assoc, hwz]

end GlobalTheory.ThetaCocycle
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecOn GlobalTheory.AbLaw.CechOne

private lemma resG_resG_divisors {Y : Scheme.{0}} {A B C : Y.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (s : Γ(Y, C)) : resG Y h₁ (resG Y h₂ s) = resG Y (h₁.trans h₂) s := by
  change _ = (Y.presheaf.map ((homOfLE h₂).op ≫ (homOfLE h₁).op)).hom s
  rw [Functor.map_comp]
  rfl

private lemma resG_self_moduli {Y : Scheme.{0}} {A : Y.Opens} (h : A ≤ A) (s : Γ(Y, A)) :
    resG Y h s = s := by
  change (Y.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma rsT_eq_resG {Y : Scheme.{0}} {A B : Y.Opens} (s : Γ(Y, A)) (h : B ≤ A) :
    rsT s B = resG Y h s := by
  unfold rsT
  rw [dite_eq_left h]

private lemma triv_secOn_ext {X : Scheme.{0}} {W : X.Opens} (σ τ : SecOn (LB.triv X) W)
    (h : (show LB.secGroup (LB.triv X) W from σ).1 PUnit.unit =
      (show LB.secGroup (LB.triv X) W from τ).1 PUnit.unit) : σ = τ :=
  Subtype.ext (funext fun _ => h)

theorem isCob_of_isAffineOpen : ∀ (X : Scheme.{0}) (J : Type) (U : J → X.Opens) (c : C1 U),
    IsAffineOpen (⨆ α, U α) → IsCoc U c → IsCob U c := by
  intro X J U c hA hc

  let φ : ∀ a b, SecOn (LB.triv X) (U a ⊓ U b) := fun a b =>
    show LB.secGroup (LB.triv X) (U a ⊓ U b) from
      ⟨fun _ => resG X inf_le_left (c a b), by
        simp only [LB.secGroup, LB.triv]
        show _ ∈ secOn _ _
        simp only [secOn, Set.mem_ofPred_eq]
        intro i j
        rw [Units.val_one, map_one, _root_.one_mul, resG_resG_divisors]⟩
  have hφ : IsCocycle (LB.triv X) U φ := by
    intro a b d W ha hb hd
    apply triv_secOn_ext
    have h0 := hc a b d
    rw [rsT_eq_resG (c a b) (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)),
      rsT_eq_resG (c b d) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_eq_resG (c a d) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)] at h0
    have e := congrArg (resG X (inf_le_left.trans (le_inf (le_inf ha hb) hd) :
      W ⊓ (LB.triv X).U PUnit.unit ≤ U a ⊓ U b ⊓ U d)) h0
    rw [map_add (f := _), resG_resG_divisors, resG_resG_divisors, resG_resG_divisors] at e
    change resG X _ (resG X _ (c a b)) + resG X _ (resG X _ (c b d)) = resG X _ (resG X _ (c a d))
    rw [resG_resG_divisors, resG_resG_divisors, resG_resG_divisors]
    exact e

  obtain ⟨ψ, hψ⟩ := cechHOneVanishesOnOpen_of_isAffineOpen (LB.isLB_triv X) hA J U (fun a => le_iSup U a) le_rfl φ hφ
  refine ⟨fun i => -resG X (le_inf le_rfl le_top : U i ≤ U i ⊓ (LB.triv X).U PUnit.unit)
    ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit), ?_⟩
  intro i j
  have e := congrArg (fun σ : SecOn (LB.triv X) (U i ⊓ U j) =>
    (show LB.secGroup (LB.triv X) (U i ⊓ U j) from σ).1 PUnit.unit) (hψ i j)
  change resG X inf_le_left (c i j) =
    resG X (inf_le_inf_right _ inf_le_left) ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit) -
      resG X (inf_le_inf_right _ inf_le_right)
        ((show LB.secGroup (LB.triv X) (U j) from ψ j).1 PUnit.unit) at e
  have e' := congrArg (resG X (le_inf le_rfl le_top :
    U i ⊓ U j ≤ U i ⊓ U j ⊓ (LB.triv X).U PUnit.unit)) e
  rw [map_sub, resG_resG_divisors, resG_resG_divisors, resG_resG_divisors, resG_self_moduli] at e'
  rw [rsT_eq_resG _ inf_le_right, rsT_eq_resG _ inf_le_left, map_neg, map_neg, resG_resG_divisors,
    resG_resG_divisors, e']
  abel

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.primitive_regular_on_section_nonzeroLocus : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by
  first | exact @GlobalTheory.primitive_regular_on_nonzeroLocus | exact GlobalTheory.primitive_regular_on_nonzeroLocus | (intros; apply GlobalTheory.primitive_regular_on_nonzeroLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_iso_of_projectiveCoordinateRepresentation : ∀ (R σ : Type) [CommRing R] (I I' : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R) (M : LB Z) (M' : LB Z') (th : σ → M.Sec) (th' : σ → M'.Sec), ProjRep I s M th → ProjRep I' s' M' th' → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → ((∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ↔ ∀ F ∈ I', MvPolynomial.eval₂ β v F = 0)) → ∃ e : Z ≅ Z', e.hom ≫ s' = s ∧ LBIso M (M'.pull e.hom) ∧ ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Z) (v : σ → R'), SecCoord M th x v ↔ SecCoord M' th' (x ≫ e.hom) v := by
  first | exact @GlobalTheory.RepUniq.exists_iso_of_projRep | exact GlobalTheory.RepUniq.exists_iso_of_projRep | (intros; apply GlobalTheory.RepUniq.exists_iso_of_projRep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), Algebra.FiniteType ℤ o → Flat s → LocallyOfFiniteType s → (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X), x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) → (∀ lam : (Fin r → K) →ₗ[K] K, spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le | exact GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le | (intros; apply GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le <;> assumption)
end
