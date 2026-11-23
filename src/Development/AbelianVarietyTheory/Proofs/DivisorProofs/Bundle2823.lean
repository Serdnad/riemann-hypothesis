module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle113
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.EndCompat

def preH {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (w : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (w ≫ ·) fun a b => MonObj.comp_mul w a b

def postH {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) (hf : IsMonHom f) :
    (T ⟶ G) →* (T ⟶ H) :=
  haveI := hf
  MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f

def pullH {S S' : Scheme.{0}} (f : S' ⟶ S) (T G : Over S) [GrpObj G] :
    (T ⟶ G) →* ((Over.pullback f).obj T ⟶ (Over.pullback f).obj G) where
  toFun := (Over.pullback f).map
  map_one' := by simp
  map_mul' a b := Functor.map_mul _ a b

theorem map_ofFn_prod {M N : Type} [Group M] [Group N] (f : M →* N) (x : Fin 8 → M) (k : Fin 8 → ℤ) :
    f (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => f (x v) ^ k v).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow]

theorem aG_comp_eq_prod : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hG₀ hα P c φc hφc pr hpr G _ _ hG D U q hq hqc a E hE u
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  haveI := E.homG
  haveI := hq u
  haveI := U₀.gen_hom
  have hR : IsMonHom (List.ofFn fun v => q v ^ a u v).prod := by
    refine isMonHom_of_mul _ fun T x z => ?_
    have key : ∀ w : T ⟶ G, w ≫ (List.ofFn fun v => q v ^ a u v).prod = ∏ v, (w ≫ q v) ^ a u v := fun w => by
      rw [← List.prod_ofFn]
      exact map_ofFn_prod (preH w) q (a u)
    rw [key, key, key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    haveI := hq v
    rw [MonObj.mul_comp, mul_zpow]
  obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField V₁ (FractionRing V₁) G G₀ hG hG₀
    ((Over.pullback (jK V₁)).map (E.aG ≫ q u))
  refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
  rw [← cancel_mono U₀.gen.hom]
  apply Over.OverMorphism.ext
  refine hα.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have hv : ∀ v, pushHom hα ((Over.pullback (jK V₁)).obj G) ((Over.pullback (jK V₁)).map (q v) ≫ U₀.gen.hom) =
      pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) :=
    fun v => Over.OverMorphism.ext (hqc v)
  have e₁ : ((Over.pullback (jK V₁)).map (List.ofFn fun v => q v ^ a u v).prod ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have := map_ofFn_prod ((pushHom hα ((Over.pullback (jK V₁)).obj G)).comp
      ((postH U₀.gen.hom U₀.gen_hom).comp (pullH (jK V₁) G G₀))) q (a u)
    refine (congrArg (fun z => z.left) this).trans ?_
    refine congrArg (fun z => Over.Hom.left (List.ofFn z).prod) (funext fun v => ?_)
    rw [← hv v]
    rfl
  have e₂ : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have h1 : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
        (U.gen.hom ≫ (List.ofFn fun v => pr v ^ a u v).prod).left ≫ φc := by
      rw [Functor.map_comp, Category.assoc, Over.comp_left, Category.assoc, hqc u, ← Category.assoc,
        ← Over.comp_left, ← Category.assoc, E.ext, Category.assoc, hE u]
    have h2 := map_ofFn_prod ((pushHom hφc ((Over.pullback (jK V₁)).obj G)).comp (preH U.gen.hom)) pr (a u)
    exact h1.trans (congrArg (fun z => z.left) h2)
  exact e₁.trans e₂.symm

end GlobalTheory.Poinc.Sep.EndCompat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowModel

variable {C : Type*} [Category C] {J : Type*}

theorem isIso_of_prod {X Y Z : C} {p : J → (X ⟶ Z)} {r : J → (Y ⟶ Z)}
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a)
    (hY : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ Y, ∀ a, x ≫ r a = y a)
    (f : X ⟶ Y) (hf : ∀ a, f ≫ r a = p a) : IsIso f := by
  obtain ⟨g, hg, -⟩ := hX Y r
  refine ⟨g, ?_, ?_⟩
  · exact (hX X p).unique (fun a => by rw [Category.assoc, hg, hf]) (fun a => Category.id_comp _)
  · exact (hY Y r).unique (fun a => by rw [Category.assoc, hf, hg]) (fun a => Category.id_comp _)

theorem prod_precomp {X X' Z : C} {p : J → (X ⟶ Z)} (e : X' ≅ X)
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X', ∀ a, x ≫ (e.hom ≫ p a) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T y
  refine ⟨x ≫ e.inv, fun a => by rw [Category.assoc, Iso.inv_hom_id_assoc, hx], fun x' hx' => ?_⟩
  rw [← hu (x' ≫ e.hom) (fun a => by rw [Category.assoc, hx']), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem prod_postcomp {X Z Z' : C} {p : J → (X ⟶ Z)} (e : Z ≅ Z')
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z')), ∃! x : T ⟶ X, ∀ a, x ≫ (p a ≫ e.hom) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T (fun a => y a ≫ e.inv)
  refine ⟨x, fun a => by rw [← Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id],
    fun x' hx' => hu x' (fun a => by rw [← hx' a, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])⟩

theorem prod_of_isLimit {X Z : C} {p : J → (X ⟶ Z)} (h : IsLimit (Fan.mk X p)) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a := fun T y =>
  ⟨Fan.IsLimit.lift h y, fun a => Fan.IsLimit.fac h y a, fun x hx =>
    Fan.IsLimit.hom_ext h _ _ fun a => by
      change x ≫ p a = Fan.IsLimit.lift h y ≫ p a
      rw [hx a]; exact (Fan.IsLimit.fac h y a).symm⟩

theorem prod_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) {X Z : Over S} {p : J → (X ⟶ Z)}
    (hX : ∀ (T : Over S) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : Over S') (y : J → (T ⟶ (Over.pullback j).obj Z)),
      ∃! x : T ⟶ (Over.pullback j).obj X, ∀ a, x ≫ (Over.pullback j).map (p a) = y a := by
  intro T y
  let adj := Over.mapPullbackAdj j
  obtain ⟨x, hx, hu⟩ := hX _ (fun a => (adj.homEquiv _ _).symm (y a))
  refine ⟨adj.homEquiv _ _ x, fun a => ?_, fun x' hx' => ?_⟩
  · rw [← adj.homEquiv_naturality_right, hx, Equiv.apply_symm_apply]
  · rw [← hu ((adj.homEquiv _ _).symm x') (fun a => by rw [← adj.homEquiv_naturality_right_symm, hx']),
      Equiv.apply_symm_apply]

end GlobalTheory.Poinc.Sep.PowModel


open GlobalTheory.Poinc.Sep.PowModel in
theorem GlobalTheory.Poinc.Sep.unif_pow_isPow_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hsa hα P c φc hφc pr hpr hP G _ _ hG D U
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  obtain ⟨κ, hκ, hκα⟩ := grpPullback_iso hφc hα
  haveI := U.gen_hom
  haveI := U₀.gen_hom
  have hf : ∀ u, IsMonHom (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv) := fun u => by
    haveI := hpr u
    infer_instance
  have hext : ∀ u, ∃ F : G ⟶ G₀, IsMonHom F ∧
      (Over.pullback (jK V₁)).map F = U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv := fun u => by
    haveI := hf u
    exact (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) G G₀ hG hsa (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv)).exists
  choose q hq hq' using hext
  have hcomp : ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α =
      (U.gen.hom ≫ pr u).left ≫ φc := by
    intro u
    rw [hq' u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left]
    rw [hκα]
  have hsa8 : IsSemiAbelian (powObj G₀ 8) :=
    GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8) hsa
  have hPi := prod_of_isLimit (powIsLimit G₀ 8)
  obtain ⟨Q, hQ, -⟩ := hPi G q
  have hmul : ∀ (T : Over (Sp V₁)) (x y : T ⟶ G), (x * y) ≫ Q = (x ≫ Q) * (y ≫ Q) := fun T x y =>
    (hPi T fun u => (x * y) ≫ q u).unique (fun u => by rw [Category.assoc, hQ u]) (fun u => by
      haveI := hq u
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hQ u, MonObj.mul_comp])
  haveI hQm : IsMonHom Q := by
    constructor
    · have h := hmul _ (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) 1
      rw [_root_.mul_one] at h
      have h' : (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) ≫ Q = 1 := mul_eq_left.1 h.symm
      simpa [Hom.one_def] using h'
    · have h := hmul (G ⊗ G) (fst _ _) (snd _ _)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
      rw [h]; congr 1
  have hGK := prod_postcomp (κ ≪≫ U₀.gen.symm) (prod_precomp U.gen hP)
  have hPiK := prod_pullback (jK V₁) hPi
  haveI : IsIso ((Over.pullback (jK V₁)).map Q) :=
    isIso_of_prod hGK hPiK _ (fun u => by
      rw [← Functor.map_comp, hQ u, hq' u]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc])
  let e := asIso ((Over.pullback (jK V₁)).map Q)
  obtain ⟨Q', hQ'm, hQ'⟩ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) (powObj G₀ 8) G hsa8 hG e.inv).exists
  have e1 : Q ≫ Q' = 𝟙 G := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) G G hG hG (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.hom_inv_id⟩
    ⟨inferInstance, (Over.pullback _).map_id G⟩
  have e2 : Q' ≫ Q = 𝟙 _ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) (powObj G₀ 8) (powObj G₀ 8) hsa8 hsa8 (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.inv_hom_id⟩
    ⟨inferInstance, (Over.pullback _).map_id _⟩
  let E : G ≅ powObj G₀ 8 := ⟨Q, Q', e1, e2⟩
  refine ⟨q, hq, fun T' y' => ?_, hcomp⟩
  obtain ⟨x, hx, hu⟩ := prod_precomp E hPi T' y'
  exact ⟨x, fun u => by rw [← hQ u]; exact hx u, fun x' hx' => hu x' fun u => by
    change x' ≫ Q ≫ powPr G₀ u = y' u
    rw [hQ u]; exact hx' u⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DataDetNormal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem isMonHom_generic (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) : IsMonHom Φ.hom := by
  let ψ : A'.A ≅ A.A := U'.gen.symm ≪≫ Φ ≪≫ U.gen
  have hψ : Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom := by simp [ψ]
  have := U.gen_hom
  have := U'.gen_hom
  have hm : IsMonHom ψ.hom := hL.rigidity _ _ _ A'.isAb A.isAb _ (by
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, ← hψ, ← Category.assoc, hw.one hL hR hI hG hG' hj hE,
      IsMonHom.one_hom])
  have e : Φ.hom = U'.gen.hom ≫ ψ.hom ≫ U.gen.inv := by simp [ψ]
  rw [e]
  infer_instance

end GlobalTheory.DataDetNormal

namespace GlobalTheory.DataDetNormal

theorem exists_iso_extending {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) [IsMonHom Φ.hom] :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = Φ.hom := by
  have h := GlobalTheory.semiAbelianHomExtension_holds
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h.fractionField R (FractionRing R) G' G hG' hG Φ.hom
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ := h.fractionField R (FractionRing R) G G' hG hG' Φ.inv
  obtain ⟨E₁, -, u₁⟩ := h.fractionField R (FractionRing R) G' G' hG' hG' (𝟙 _)
  obtain ⟨E₂, -, u₂⟩ := h.fractionField R (FractionRing R) G G hG hG (𝟙 _)
  have c₁ : F ≫ F₁ = 𝟙 G' := (u₁ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.hom_inv_id]⟩).trans
    (u₁ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  have c₂ : F₁ ≫ F = 𝟙 G := (u₂ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.inv_hom_id]⟩).trans
    (u₂ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  exact ⟨⟨F, F₁, c₁, c₂⟩, hF, hF'⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem thick_compat (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) (ψ : G' ⟶ G)
    (hψ : (Over.pullback (jK R)).map ψ = Φ.hom) (e : ℕ) :
    (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hR.1
  have := hG.smooth
  have := hG.separated
  have := hG'.smooth
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have eψ : Φ.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (GlobalTheory.FormalExt.range_thick I 0 _).2 hx
  refine GlobalTheory.FormalExt.hom_ext_of_flat_family _ _ fun y => ?_
  obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((GlobalTheory.FormalExt.range_thick I e _).1 (by
    have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
    rw [Scheme.Pullback.range_fst] at this
    exact this))
  obtain ⟨jL, hjL⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', hjL'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, hB, -, hg'f, hxr, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x _ _ hjL hjL'
  have hpt : ∀ {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
      r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g :=
    fun ρ r hr => hw.point hL hR hG hG' hE hB h₁ h₂ h₃ h₄ h₅ ρ r hr
  have hg : g' ≫ ψ.left = g := by
    let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
    let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g (h₂.trans h₁.symm)
    have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
    have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
    have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
      (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
        have := hpt _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
        rw [eψ] at this
        exact (pullback.condition_assoc _).trans this)
    exact congr(($this).left)
  refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd]
    show (fstG I e G').left y ∈ Set.range g'
    rw [← hx]; exact hxr
  · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]

end GlobalTheory.DataDetNormal

theorem GlobalTheory.unif_determined_by_data_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, GlobalTheory.UT.Cl.Determined U := by
  intro R _ _ _ hR D A G _ _ hG U D' A' G' _ _ hG' U' hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hR.1
  have := hR.2.2.1
  obtain ⟨j, hj⟩ := GlobalTheory.GenericIso.exists_levelIso U.toUnifPre U'.toUnifPre hD hL.globalFns
  have hE := hj.enough hL.globalFns U.expand U'.expand
  obtain ⟨Φ, w, hw⟩ := GlobalTheory.GenericIso.exists_genericRel hL R _ hR D D' A A' G G' hG hG' U U' hD j hj hE
  have hΦ : IsMonHom Φ.hom := GlobalTheory.DataDetNormal.isMonHom_generic hL hR hI hG hG' hj hE hw
  obtain ⟨ψ, hψm, hψK⟩ := GlobalTheory.DataDetNormal.exists_iso_extending hG hG' Φ
  have hth := GlobalTheory.DataDetNormal.thick_compat hL hR hG hG' hj hE hw ψ.hom hψK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_completeLocalNormal R hR D D' A A' G G' hG hG' U U' hD j hj Φ w hw ψ hψm hψK hth
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hψm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hr := GlobalTheory.pmaps_rig_of_thick_compat hI U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  have hP : IsPullUnif (RingHom.id R) hD bc U U' := (isPullUnif_iff_stalks R R _ _ _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hth e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩
  · obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.UT.exists_genericFibre_iso_of_model_iso R _ D D' A A' G G' U.toUnifPre
      U'.toUnifPre ψ hψm ⟨wL, hwL⟩
    exact ⟨ψ, bc, φ, hψm, mbc, hbc', hP, h1, h2, h3⟩
  · exact (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _
        ((congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
          hs).mpr hr))
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hth e)).mp h₃
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.CubTrivComp

theorem val_cast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (h ▸ t : LB.Gen (LB.LinComb L φ' ε)) r z J = val t r z J := by
  subst h; rfl

theorem isGen_cast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (h ▸ t : LB.Gen (LB.LinComb L φ' ε)).IsGen := by
  subst h; exact ht

theorem exists_even_comp : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H']
    (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i,
    GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  intro S G H H' _ _ _ _ P i e he σ hσ
  have hφ : (fun k => e.left ≫ (![i.left, (1 : H' ⟶ G).left] : Fin 2 → (H'.left ⟶ G.left)) k) =
      ![(e ≫ i).left, (1 : H ⟶ G).left] := by
    funext k
    fin_cases k
    · exact (Over.comp_left _ _ _ e i).symm
    · show e.left ≫ (1 : H' ⟶ G).left = (1 : H ⟶ G).left
      rw [← Over.comp_left, MonObj.comp_one]
  let s₁ : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![(e ≫ i).left, (1 : H ⟶ G).left] ![1, -1]) :=
    hφ ▸ LB.pullGen P.L.L _ _ σ.s e.left
  have v : ∀ {T : Over S} (x : T ⟶ H) {z : T.left} {J}, Good P.L.L z J →
      val s₁ x.left z J = val σ.s (x ≫ e).left z J := fun x z J hJ =>
    (val_cast hφ _ _ _ _).trans ((val_pull hJ σ.s e.left x.left).trans (by rw [Over.comp_left]))
  refine ⟨⟨s₁, isGen_cast hφ (DVR.pullGen_isGen _ _ _ _ σ.gen _), fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · have c := σ.cub T (x ≫ e) (y ≫ e) (u ≫ e) z J hJ
    simp only [← MonObj.mul_comp, Category.assoc] at c
    simp only [v _ hJ]
    exact c
  · show val s₁ (x⁻¹).left z J = val P.sym (x ≫ e ≫ i).left z J * val s₁ x.left z J
    rw [v _ hJ, v _ hJ, GrpObj.inv_comp, hσ T (x ≫ e) z J hJ, Category.assoc]

end GlobalTheory.CubTrivComp
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  first | exact @GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | exact GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | (intros; apply GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal <;> assumption)
end
