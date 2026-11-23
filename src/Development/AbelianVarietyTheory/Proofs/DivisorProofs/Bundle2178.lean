module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle933
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle031
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_isAmpleCls : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  intro K _ A
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)
  exact ⟨cls L hL, L, hL, hamp, rfl⟩

end GlobalTheory.AV
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbDual.poincare_evc_mul_right : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X),
    AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  intro K _ A A' P hP Y a b b'
  have hs : (AbDual.swap P).IsLB := pull_isLB hP.isLB _
  have h := (AbDual.isAdditive_iff hs).1 (AbDual.isDual_isAdditive_swap _ A.X A'.X P A'.ab hP) Y b b' a
  rwa [AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs] at h
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem topologicalKrullDim_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  intro K _ A
  haveI : Nonempty A.X.left := ⟨A.origin⟩
  exact GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.X.hom A.dim A.smooth

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_mul_left_of_cube : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K))
    (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  intro K _ A c Y x x' y
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem (Sp K) A.X A.ab L hL Y x x' y
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![x * x' * y, x * x', x * y, x' * y, x, x', y, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (GlobalTheory.CechPic.cls_eq_zero_iff hl).2 h
  rw [GlobalTheory.CechPic.cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [AbVar.lam_eq, AbVar.lam_eq, AbVar.lam_eq]
  simp only [GlobalTheory.CechPic.lam, _root_.mul_one]
  rw [← sub_eq_zero, ← e]
  abel

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.TateHondaBridge

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AV GlobalTheory.AV.AbVar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Published.AbVarRed

def toAbVar {k : Type} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A] (hA : IsAbelianScheme A) :
    AbVar k where
  X := A
  ab := hA
  dim := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose
  smooth := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose_spec

end GlobalTheory.TateHondaBridge

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.TorsKer

theorem pow_eq_one_of_points : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n m : ℕ), (n : K) ≠ 0 →
    (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1) →
    ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1 := by
  intro K _ A C f n m hn hpt T x hx hf
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    have : IsUnit (n : K) := isUnit_iff_ne_zero.2 hn
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hZf, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let Z := torsion A.X n
  let iZ : Z ⟶ A.X := torsion.ι A.X n
  have hiZ : iZ ^ n = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact (pullback.condition (f := mulN A.X n) (g := (η : 𝟙_ (Over (Sp K)) ⟶ A.X))).trans
      (by rw [CategoryTheory.Hom.one_def]; congr 1; exact toUnit_unique _ _)
  let a : Z.left ⟶ C.X.left := (iZ ≫ f.hom).left
  have : IsClosedImmersion (η[C.X]).left :=
    isClosedImmersion_of_comp_eq_id (Y := Sp K) C.X.hom _ (Over.w _)
  let H : Over (Sp K) := Over.mk (pullback.fst a (η[C.X]).left ≫ Z.hom)
  let j : H ⟶ Z := Over.homMk (pullback.fst a (η[C.X]).left) rfl
  have hHf : IsFinite H.hom := by
    haveI := hZf; show IsFinite (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
  have hHe : Etale H.hom := by
    haveI := hZe
    haveI : FormallyUnramified Z.hom := by infer_instance
    haveI : LocallyOfFinitePresentation Z.hom := by infer_instance
    haveI : IsClosedImmersion (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified H.hom := by
      show FormallyUnramified (pullback.fst a (η[C.X]).left ≫ Z.hom)
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ ‹_› ‹FormallyUnramified Z.hom›
    haveI : LocallyOfFinitePresentation H.hom := by
      show LocallyOfFinitePresentation (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
    exact Etale.of_formallyUnramified_of_flat _
  have hjf : j ≫ iZ ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    have h1 : (toUnit H).left = H.hom := by simpa using Over.w (toUnit H)
    have h2 : (η[C.X]).left ≫ C.X.hom = 𝟙 _ := by simpa using Over.w (η[C.X])
    have h3 : a ≫ C.X.hom = Z.hom := Over.w (iZ ≫ f.hom)
    have hs : pullback.snd a (η[C.X]).left = (toUnit H).left := by
      rw [h1]
      show pullback.snd a _ = pullback.fst a _ ≫ Z.hom
      rw [← h3, ← Category.assoc, pullback.condition, Category.assoc, h2]
      exact (Category.comp_id _).symm
    rw [CategoryTheory.Hom.one_def]
    show pullback.fst a _ ≫ a = (toUnit H).left ≫ (η[C.X]).left
    rw [← hs]
    exact pullback.condition
  have hsep : IsSeparated A.X.hom := by
    have := A.ab.proper; infer_instance
  have key : (j ≫ iZ) ^ m = 1 := by
    refine GlobalTheory.GenTorsMap.hom_ext_points hHf hHe hsep _ _ fun y => ?_
    rw [MonObj.comp_one, MonObj.comp_pow]
    refine hpt (y ≫ j ≫ iZ) ?_ ?_
    · rw [← MonObj.comp_pow, ← MonObj.comp_pow, hiZ, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hjf, MonObj.comp_one]
  have hx1 : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by
    rw [GlobalTheory.GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
  let x₁ : T ⟶ Z := pullback.lift x (toUnit T) hx1
  have hx₁ : x₁ ≫ iZ = x := pullback.lift_fst _ _ _
  have hw : x₁.left ≫ a = T.hom ≫ (η[C.X]).left := by
    have e := congrArg (fun g => g.left) hf
    simp only [CategoryTheory.Hom.one_def, Over.comp_left] at e
    have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
    rw [← hT, ← e, ← hx₁]
    simp [a]
  let x₂ : T ⟶ H := Over.homMk (pullback.lift x₁.left T.hom hw)
    (by show _ ≫ pullback.fst a _ ≫ Z.hom = _; rw [← Category.assoc, pullback.lift_fst]; exact Over.w x₁)
  have hx₂ : x₂ ≫ j ≫ iZ = x := by
    rw [← hx₁, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp [x₂, j]
  rw [← hx₂, ← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.AV.TorsKer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem ext_of_pt_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f g : A ⟶ B),
    (∀ x : A.Pt, x ≫ f.hom = x ≫ g.hom) → f = g := by
  intro K _ A B f g h
  have := A.ab.smooth
  have := B.ab.proper
  have : IsReduced A.X.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback A.X.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)
  have hd : Dense (closedPoints ↥(pullback A.X.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst A.X.hom q).surjective.denseRange.dense_image
    (pullback.fst A.X.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι f.hom.left g.hom.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback A.X.hom q)) := hw₀
    let y : Sp Ω ⟶ A.X.left :=
      pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q
    have hy : y ≫ A.X.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : A.Pt := Over.homMk y hy
    have hx : y ≫ f.hom.left = y ≫ g.hom.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)
  have : IsDominant (equalizer.ι f.hom.left g.hom.left) := hdom
  have heq : f.hom = g.hom := Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _))
  exact Subtype.ext heq

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_lift_of_surjective_of_isReduced {K : Type} [Field K] {T T' Z Y : Over (Sp K)}
    (i : Z ⟶ Y) [IsClosedImmersion i.left] [IsReduced T.left] (q : T' ⟶ T) (g : T ⟶ Y) (r : T' ⟶ Z)
    (hq : Surjective q.left) (h : q ≫ g = r ≫ i) : ∃ e : T ⟶ Z, e ≫ i = g := by
  obtain ⟨e, he⟩ := GlobalTheory.lift_of_reduced_of_support i.left g.left (fun t => by
    obtain ⟨t', rfl⟩ := hq.surj t
    apply i.left.range_subset_ker_support
    refine ⟨r.left t', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply])
  exact ⟨Over.homMk e (by rw [← Over.w i, ← Category.assoc, he, Over.w g]), Over.OverMorphism.ext he⟩

theorem exists_grpObj_of_image :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom → Surjective p.left → IsClosedImmersion i.left → GeometricallyIntegral Z.hom → ∃ _ : GrpObj Z, IsMonHom p ∧ IsMonHom i := by
  intro K _ A B f Z p i hf hp hi hZ
  have hmono : Mono i := Over.mono_of_mono_left i
  haveI : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom
  haveI := B.smooth
  haveI : Smooth B.X.hom := SmoothOfRelativeDimension.smooth B.dim _
  haveI : LocallyOfFiniteType Z.hom := by rw [← Over.w i]; infer_instance
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI : IsReduced (Z ⊗ Z).left := (inferInstance : IsReduced (pullback Z.hom Z.hom))
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    ⟨fun f g hf hg => by haveI := hf; haveI := hg; infer_instance⟩
  have hpp : Surjective (p ⊗ₘ p).left :=
    MorphismProperty.pullbackMap (P := @Surjective) hp hp (Over.w p).symm (Over.w p).symm
  have hinv : ι[A.X] ≫ f.hom = f.hom ≫ ι[B.X] := by
    calc ι[A.X] ≫ f.hom = (𝟙 A.X)⁻¹ ≫ f.hom := by rw [Hom.inv_def, Category.id_comp]
      _ = (𝟙 A.X ≫ f.hom)⁻¹ := GrpObj.inv_comp _ _
      _ = f.hom ≫ ι[B.X] := by rw [Category.id_comp, Hom.inv_def]
  obtain ⟨m, hm⟩ := exists_lift_of_surjective_of_isReduced i (p ⊗ₘ p) ((i ⊗ₘ i) ≫ μ[B.X]) (μ[A.X] ≫ p) hpp (by
    rw [← Category.assoc, tensorHom_comp_tensorHom, hf, ← IsMonHom.mul_hom, Category.assoc, hf])
  obtain ⟨v, hv⟩ := exists_lift_of_surjective_of_isReduced i p (i ≫ ι[B.X]) (ι[A.X] ≫ p) hp (by
    rw [← Category.assoc, hf, Category.assoc, hf, hinv])
  have h1 : (η[A.X] ≫ p) ≫ i = η[B.X] := by rw [Category.assoc, hf, IsMonHom.one_hom]
  have h1a : η[A.X] ≫ p ≫ i = η[B.X] := by rw [← Category.assoc, h1]
  letI M : MonObj Z :=
    { one := η[A.X] ≫ p
      mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        calc (m ▷ Z ≫ m) ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[B.X] ▷ B.X ≫ μ[B.X] := by
              simp only [Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id]
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ _ _ _).hom ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by rw [MonObj.mul_assoc]
          _ = (α_ Z Z Z).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by
              rw [associator_naturality_assoc]
          _ = ((α_ Z Z Z).hom ≫ Z ◁ m ≫ m) ≫ i := by
              simp only [Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id] }
  letI G : GrpObj Z :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift v (𝟙 Z) ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift (i ≫ ι[B.X]) i = i ≫ lift ι[B.X] (𝟙 B.X) by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.left_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a]
      right_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift (𝟙 Z) v ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift i (i ≫ ι[B.X]) = i ≫ lift (𝟙 B.X) ι[B.X] by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.right_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a] }
  refine ⟨G, ⟨rfl, ?_⟩, ⟨h1, hm⟩⟩
  change μ[A.X] ≫ p = (p ⊗ₘ p) ≫ m
  rw [← cancel_mono i, Category.assoc, Category.assoc, hm, hf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hf]

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem geometricallyReduced_of_schDominant_comp {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Y)
    (f : Y ⟶ Spec (.of K)) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField K) _)
  have : Flat a := MorphismProperty.of_isPullback hW.flip hy
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd p a)

theorem geometricallyIrreducible_of_surjective_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Surjective p]
    [h : GeometricallyIrreducible (p ≫ f)] : GeometricallyIrreducible f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback p a) :=
    h.geometrically_irreducibleSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact Function.Surjective.irreducibleSpace (pullback.snd p a).continuous (pullback.snd p a).surjective

theorem exists_image_geometricallyIntegral :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X),
      p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  intro K _ A B f
  have hA := A.ab
  have hB := B.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  have : IsProper B.X.hom := hB.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  have : IsSchemeTheoreticallyDominant f.hom.left.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage _
  have hsurj : Surjective f.hom.left.toImage := ⟨by
    have h2 : IsClosed (Set.range f.hom.left.toImage) := f.hom.left.toImage.isClosedMap.isClosed_range
    rw [← Set.range_eq_univ, ← h2.closure_eq]
    exact f.hom.left.toImage.denseRange.closure_range⟩
  have hwi : f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom) = A.X.hom := by
    rw [Scheme.Hom.toImage_imageι_assoc, hw]
  have : GeometricallyIntegral A.X.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : GeometricallyIntegral (f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom)) := by
    rw [hwi]; infer_instance
  have := geometricallyReduced_of_schDominant_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  have := geometricallyIrreducible_of_surjective_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  refine ⟨Over.mk (f.hom.left.imageι ≫ B.X.hom), Over.homMk f.hom.left.toImage hwi,
    Over.homMk f.hom.left.imageι rfl, ?_, hsurj, ?_, ?_⟩
  · ext1
    simp
  · exact inferInstanceAs (IsClosedImmersion f.hom.left.imageι)
  · show GeometricallyIntegral (f.hom.left.imageι ≫ B.X.hom)
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_universal_first_order_deformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  first | exact @GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | exact GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | (intros; apply GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSExist.ksRow_exists_lieComb | exact GlobalTheory.KSExist.ksRow_exists_lieComb | (intros; apply GlobalTheory.KSExist.ksRow_exists_lieComb <;> assumption)
end
