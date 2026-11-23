module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def trivTriple (H : Host E) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (a : OAct (𝓞 E) G) : SAB H S where
  G := G
  semi := hG
  act := a
  PP := UU.trivRig G
  cub := UU.trivCub G
  sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S :=
  trivTriple H (𝟙_ (Over S)) (isSemiAbelian_of_isAbelianScheme _ (UU.isAbelianScheme_unit S))
    ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩

theorem isProper_zeroTriple (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (UU.isAbelianScheme_unit S).proper

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) (h : IsProper G.hom) : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

theorem abOpen_and_splitFib {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : AbOpen t.G ∧ SplitFib t.G := by
  refine ⟨⟨⊤, (abLocus_eq_univ _ h).symm, inferInstance⟩, fun x => ?_⟩
  letI selfAlgebra : Algebra (S.residueField x) (S.residueField x) := Algebra.id _
  let f : Sp (S.residueField x) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) (S.residueField x))) ≫
      S.fromSpecResidueField x
  letI : GrpObj t.G := t.grp
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  letI : GrpObj ((Over.pullback f).obj t.G) :=
    Functor.grpObjObj (F := Over.pullback f) (G := t.G)
  have hab : IsAbelianScheme ((Over.pullback f).obj t.G) :=
    isAbelianScheme_pullback_obj f t.G ⟨t.semi.comm, t.semi.smooth, h, t.semi.geomConnected⟩
  exact ⟨S.residueField x, inferInstance, selfAlgebra, inferInstance, inferInstance, _,
    ZJ.isGt_splitExtOfAbelian ((Over.pullback f).obj t.G) hab⟩

theorem good_zeroTriple (S : Scheme.{0}) : Good (zeroTriple H S) := by
  obtain ⟨h₁, h₂⟩ := abOpen_and_splitFib (zeroTriple H S) (isProper_zeroTriple S)
  refine ⟨h₁, h₂, fun x => ⟨⊤, trivial, fun _ => 1, fun i j => ?_, fun y _ => ⟨y, PUnit.unit, rfl, ?_⟩⟩⟩
  · exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · rw [Scheme.basicOpen_one]
    exact ⟨trivial, trivial⟩

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section General

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

end General

section Above

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

end Above

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := ProjSpace.Model.isIso_str_zero (R := R)
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Inhab

end
end

section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

section Away
variable {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0)

end Away

section Basis
variable (h : ℕ)

end Basis

section Use
open AlgebraicGeometry CategoryTheory MonObj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

end Use

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))

def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩

end Zero

end GlobalTheory.ZM.Model
end
end
