module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle149
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLift

open Limits GlobalTheory.MixHt

theorem exists_cover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X']
    [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D →
    IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X →
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧
      IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧
      g.residueDegree (genericPoint Y') ≠ 0 := by
  intro k _ X X' Y _ _ _ p D E ρ π hX hX' hY hρ

  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hX'.isProjOver
  have : IsProper (ρ ≫ p) := hj' ▸ inferInstance
  have : IsProper ρ := IsProper.of_comp ρ p
  have hs : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← ρ.isClosedMap.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hρ⟩)
  have : Surjective ρ := ⟨hs⟩

  obtain ⟨z, hz, hdeg⟩ := exists_residueDegree_pos_of_mem_range _ _ (pullback.fst π ρ) (genericPoint Y)
    ((inferInstance : Surjective (pullback.fst π ρ)).surj _)
  set g := cloι z ≫ pullback.fst π ρ with hgdef
  have hg : g (genericPoint (clo z)) = genericPoint Y := by
    rw [hgdef, Scheme.Hom.comp_apply, cloι_genericPoint, hz]
  have hdeg' : g.residueDegree (genericPoint (clo z)) ≠ 0 := by
    rw [hgdef, CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion (cloι z), mul_one,
      cloι_genericPoint]
    exact hdeg.ne'

  have hP : IsProjOver (pullback.fst π ρ ≫ π ≫ p) :=
    FlagFamily.isProjOver_pullback_over hX.isProjOver hY.isProjOver hX'.isProjOver
  have hA : IsAmb (g ≫ π ≫ p) := by
    have := (IsAmb.mk hX.1 hX.2 hP).sub (cloι z)
    rwa [← Category.assoc] at this
  have hAY : IsAmb (π ≫ p) := isAmb_of_isArithVar hY

  obtain ⟨⟨m, hm⟩, -, -, -, -, hgen⟩ := hasDim_basic k (clo z) (g ≫ π ≫ p) hA
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo z))
  have hdY : HasDim (g (genericPoint (clo z))) (E + 1) := by
    rw [hg]
    exact (DimBasic.hasDim_genericPoint_iff Y (E + 1)).2 hY.dim_eq
  have hcmp := DimDeg.dim_le_and_residueDegree_ne_zero_iff k Y (clo z) (π ≫ p) (g ≫ π ≫ p) hAY hA g rfl
    (genericPoint (clo z)) d (E + 1) hd hdY
  have hdim : topologicalKrullDim (clo z) = (E + 1 : ℕ) := (hgen (clo z) (E + 1)).1 (hcmp.2.1 hdeg' ▸ hd)

  have hcY : CharZero Γ(Y, ⊤) := hY.charZero
  have h₁ : CharZero Y.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Y.Opens) (Opens.mem_top _))
  have h₂ : CharZero (Y.residueField (genericPoint Y)) := by
    let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue _).hom
    exact charZero_of_injective_ringHom f.injective
  have h₃ : CharZero (Y.residueField (g (genericPoint (clo z)))) := hg ▸ h₂
  have h₄ : CharZero ((clo z).residueField (genericPoint (clo z))) :=
    charZero_of_injective_ringHom (g.residueFieldMap _).hom.injective
  have h₅ : CharZero (clo z).functionField := by
    let f : (clo z).functionField →+* (clo z).residueField (genericPoint (clo z)) := ((clo z).residue _).hom
    exact (RingHom.charZero_iff f.injective).2 h₄
  have h₆ : CharZero Γ(clo z, ⊤) :=
    (RingHom.charZero_iff (fnOf_injective (⊤ : (clo z).Opens) (Opens.mem_top _))).2 h₅
  refine ⟨clo z, inferInstance, g, cloι z ≫ pullback.snd π ρ, ?_,
    ⟨hX.1, hX.2, inferInstance, hA.isProjOver, (flat_int_iff_charZero _).2 h₆, hdim⟩, hg, hdeg'⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

end GlobalTheory.CoverLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

open GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem lift_comp_left {S : Scheme.{0}} {B₀ B : Over S} (a b : B₀ ⟶ B) {T : Over S} (p q : T ⟶ B₀) :
    (lift p q).left ≫ (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : B₀ ⊗ B₀ ⟶ B ⊗ B).left =
      (lift (p ≫ a) (q ≫ b)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

theorem lamVal_one_left : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → IsAbelianScheme B₀ → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b] (w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left)), w.IsGen → (∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1) → ∀ (T : Over S) (y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) y).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM hB₀ a b _ _ w hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  let β₂ := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let φ1 : Fin 1 → (B₀.left ⟶ (G2 B₀).left) := fun _ => (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B₀) φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ lamφ B₀ i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B₀)]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [lift_comp_left, prod_lam, one_comp_hom a, Category.id_comp, _root_.one_mul b]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM₀ fe' (LB.oneGen M₀) (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M₀ z₀ J₀ →
      val (L := abelian₂ B₀ M₀) (nest M₀ (lamφ B₀) lamε φ1 ε1 g') r z₀ (ind B₀ J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM₀ hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S} (c : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B₀ J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B₀) c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S) ⟶ B₀).left ≫ B₀.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S) ⟶ B₀)
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B₀.hom _ he (hG _ _ hB₀).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM₀ y₀
      refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S) ⟶ B₀), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

def e8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := W + W.transpose

def actMat (W : Matrix (Fin 8) (Fin 8) ℤ) : Fin 2 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![(e8 W).adjugate * W, (e8 W).adjugate * W.transpose]

variable {S : Scheme.{0}}

def IsProd {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)) : Prop :=
  (∀ a, IsMonHom (pr a)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ B)), ∃! x : T ⟶ A, ∀ a, x ≫ pr a = y a

def IsE8WeightedBundle (W : Matrix (Fin 8) (Fin 8) ℤ) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (M : LB B.left) : Prop :=
  LBIso L (LB.LinComb M (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)))

def IsPPFib (B : Over S) [GrpObj B] (g : ℕ) (M : RigLB B) : Prop :=
  IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ Nonempty (CubicalStr B M) ∧ RelAmple B M.L ∧ KTriv B M.L

def ActsBy {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (f : A ⟶ A)
    (m : Matrix (Fin 8) (Fin 8) ℤ) : Prop :=
  ∀ a, f ≫ pr a = ∏ b, pr b ^ m a b

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TraitTau

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem exists_tauCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X) :
    ∃ k, Q.TauCoord a b k := by
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen :=
    DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _
  have hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) =
      fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k := by
    funext k
    fin_cases k
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm
    · rfl
    · rfl
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b)
    (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)
  let k : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ
  have hk : unitOn k = ρ := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)
  refine ⟨k, u, hu, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]

theorem isMonomialTau_ofDeg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D t β) (hs : ∀ i y z, β i y z = β i z y)
    (ht : ∀ i, t i ≠ 0) : (Wit.ofDeg D hB).IsMonomialTau t β := by
  intro (a : D.X) (b : D.X)
  obtain ⟨k, hk⟩ := exists_tauCoord (Wit.ofDeg D hB) a b
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id
    (Wit.refines_ofDeg D hB) a b k hk x hx
  have hl : ∀ σ : FractionRing R →+* FractionRing R,
      (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y :=
    fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))
  rw [hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)] at hu₁
  obtain ⟨_, _, -, ha⟩ := h a
  obtain ⟨_, _, -, hb⟩ := h b
  obtain ⟨_, _, -, hab⟩ := h (a + b)
  obtain ⟨u₃, hu₃⟩ := h.tau hs ht ha hb hab
  obtain ⟨xa, ha₁, ha₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha
  obtain ⟨xb, hb₁, hb₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb
  obtain ⟨xab, hab₁, hab₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁
  rw [← ha₂, ← hb₂, ← hab₂] at hu₃
  have hc := Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)
  refine ⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩
  refine Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl
  clear hc hk hl
  have hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ *
      (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) := by
    rw [← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]
    ring
  have h₂ := hu u₂
  have h₃ := hu u₃
  generalize ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp
  linear_combination e

theorem finrank_le {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (hn : 2 ≤ n) (hζ : IsUnit ζ) :
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  let K := AlgebraicClosure (FractionRing T.V)
  haveI : CharZero (FractionRing T.V) :=
    (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let κ : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap _ K)
  have hp := IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)
  have hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ)
      (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1
  have hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim
  have e : T.A.g = g := GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  intro g n o _ ζ F T
  refine ⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩
  · fin_cases i
    exact T.symm
  · fin_cases i
    exact T.irr.ne_zero
  · obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha
    fin_cases i
    exact hi

end GlobalTheory.Poinc.TraitTau
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem exists_lamVal_origin_two : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM a b _ _ H
  obtain ⟨w₀, hw₀⟩ := H
  let F : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let e : (𝟙_ (Over S)).left ⟶ (G2 B₀).left := (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
  let q : (𝟙_ (Over S)).left ⟶ B.left := (1 : 𝟙_ (Over S) ⟶ B).left
  let q' : (𝟙_ (Over S)).left ⟶ B₀.left := (1 : 𝟙_ (Over S) ⟶ B₀).left
  have eF : e ≫ F = (lift (1 : 𝟙_ (Over S) ⟶ B) 1).left := by
    show (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b)).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, MonObj.one_comp]
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ F) ≫ (psum B (x2 B) I.down).left = q := fun I => by
    rw [eF]
    exact congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B (T := 𝟙_ (Over S)) I.down)
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B₀ (x2 B₀) I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B₀ (T := 𝟙_ (Over S)) I.down)
  obtain ⟨w, hw, hv⟩ := GlobalTheory.PolDeg.NormIso.exists_normalised M M₀ hM hM₀ (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B₀ (x2 B₀) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) F e (toUnit (G2 B₀)).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ toUnit (G2 B₀)) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 B₀).left) (j : (abelian₂ B M).ι) (k : (abelian₂ B₀ M₀).ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ F ≫ (psum B (x2 B) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B₀ (x2 B₀) I.down).left)) = k →
      GlobalTheory.PolDeg.lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B₀ M₀) w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

end GlobalTheory.Mum.Two
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fraction_constant_period_ratio_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  first | exact @GlobalTheory.HalfRatio.ratio_exists | exact GlobalTheory.HalfRatio.ratio_exists | (intros; apply GlobalTheory.HalfRatio.ratio_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.kodaira_spencer_matrix_exists : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  first | exact @GlobalTheory.KSExist.ksExist | exact GlobalTheory.KSExist.ksExist | (intros; apply GlobalTheory.KSExist.ksExist <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_group_lift_kodaira_spencer_zero : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  first | exact @GlobalTheory.KSFull.ksFull | exact GlobalTheory.KSFull.ksFull | (intros; apply GlobalTheory.KSFull.ksFull <;> assumption)
end
