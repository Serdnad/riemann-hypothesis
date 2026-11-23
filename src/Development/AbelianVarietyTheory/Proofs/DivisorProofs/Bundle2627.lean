module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem push_pow {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (h : x₀.left = x.left ≫ π) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ π := by
  have h1 : (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ π := by
    let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
      show ((1 : T ⟶ G').left ≫ π) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
    have he : e * e = e := Over.OverMorphism.ext ((hg.2 T 1 1 e e rfl rfl).trans (by rw [_root_.mul_one]; rfl))
    have he1 : e = 1 := mul_eq_left.1 he
    exact (congrArg (fun z => z.left) he1).symm
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ, pow_succ]; exact hg.2 T _ _ _ _ ih h

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := congrArg (fun z => (Spec.preimage z).hom) h
  simpa using this

theorem lift_of_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg h S _ hS y hy
  obtain ⟨s0, hs0⟩ := hy
  let o : O →+* S := (Spec.preimage (y ≫ (torsion G' q).hom)).hom
  have ho : spMap o = y ≫ (torsion G' q).hom := Spec.map_preimage _
  let φ : R →+* S := o.comp x0
  have hu' : IsUnit (φ P'.f) := hu.map o
  have hw : (y ≫ (torsion.ι G' q).left ≫ π) ≫ t.G.hom = spMap φ ≫ ξ := by
    rw [Category.assoc, Category.assoc, hg.1.w, ← Category.assoc (torsion.ι G' q).left, Over.w (torsion.ι G' q),
      ← Category.assoc, ← ho, GlobalTheory.HTMap.spc_assoc]
  let w : Over.mk (spMap φ ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ hw
  let T : Over (Sp O) := Over.mk (y ≫ (torsion G' q).hom)
  let yt : T ⟶ torsion G' q := Over.homMk y rfl
  let x : T ⟶ G' := yt ≫ torsion.ι G' q
  have hx : x ^ q = 1 := by
    show (yt ≫ torsion.ι G' q) ^ q = 1
    rw [← MonObj.comp_pow, GlobalTheory.KernelNoTorsion.torsionι_pow, MonObj.comp_one]
  let x₀ : Over.mk (T.hom ≫ (spMap x0 ≫ ξ)) ⟶ t.G := Over.homMk (x.left ≫ π) (by
    show (x.left ≫ π) ≫ t.G.hom = T.hom ≫ spMap x0 ≫ ξ
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w x])
  have hx₀ : x₀ ^ q = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [push_pow hg x x₀ rfl q, hx]
    have := push_pow hg x x₀ rfl 0
    simp only [pow_zero] at this
    exact this.symm
  have hwq : w ^ q = 1 := GlobalTheory.HTMap.tors_of (g := 𝟙 _) (w := x₀) (by
    rw [Category.id_comp]
    show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
    rw [Category.assoc]) hx₀
  obtain ⟨β0, hβ0⟩ : ∃ β, P'.At φ w.left β := by
    refine GlobalTheory.HTMap.FP.at_open hu' rfl w hwq fun 𝔪 h𝔪 => ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
    let gm : Bt P' x0 hu →+* IsLocalRing.ResidueField S := (Spec.preimage s0).hom
    have hgm : spMap gm = s0 := Spec.map_preimage _
    have e1 : spMap (gm.comp (algebraMap O (Bt P' x0 hu))) = spMap ((IsLocalRing.residue S).comp o) := by
      rw [← GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) gm, hgm, ← GlobalTheory.HTMap.spc o (IsLocalRing.residue S), ho]
      show s0 ≫ (Hs P' x0 hu).hom = _
      rw [← Over.w (jH P' x0 hu hg.1 h), ← Category.assoc, hs0, Category.assoc]
    have e2 := spMap_inj e1
    refine ⟨gm.comp (inB P' x0 hu), ?_, ?_⟩
    · show (gm.comp (inB P' x0 hu)).comp P'.str = (IsLocalRing.residue S).comp φ
      rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc, e2]
      rfl
    · show spMap (gm.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (IsLocalRing.residue S) ≫ y ≫ (torsion.ι G' q).left ≫ π
      rw [← GlobalTheory.HTMap.spc_assoc, hgm, ← aH_left_π P' x0 hu hg.1, ← jH_ι P' x0 hu hg.1 h, Over.comp_left,
        ← Category.assoc, ← Category.assoc, hs0, Category.assoc, Category.assoc]
  letI : Algebra O S := o.toAlgebra
  have hβ : β0.comp P'.str = (algebraMap O S).comp x0 := hβ0.1
  refine ⟨(ptOf P' x0 hu β0 hβ).left, ?_⟩
  let b : T ⟶ torsion G' q := Over.homMk ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) (by
    show ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) ≫ (torsion G' q).hom = y ≫ (torsion G' q).hom
    rw [Category.assoc, Over.w (jH P' x0 hu hg.1 h), Over.w (ptOf P' x0 hu β0 hβ)]
    exact ho)
  have hb : b = yt := by
    refine GlobalTheory.KernelNoTorsion.torsion_hom_ext (Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_))
    · have e1 : (b ≫ torsion.ι G' q).left = (ptOf P' x0 hu β0 hβ ≫ aH P' x0 hu hg.1).left := by
        show (ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left ≫ (torsion.ι G' q).left = _
        rw [← Over.comp_left, jH_ι]
        rfl
      rw [e1, ptOf_aH_π, hβ0.2]
      show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
      rw [Category.assoc]
    · rw [Over.w (b ≫ torsion.ι G' q), Over.w (yt ≫ torsion.ι G' q)]
  exact congrArg (fun z => z.left) hb
end GlobalTheory.FinPartAt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem aH_left_π_ptMap {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {D : Type} [CommRing D] [Algebra O D]
    (a : Bt P' x0 hu →ₐ[O] D) :
    (ptMap a ≫ aH P' x0 hu hπ).left ≫ π = spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π]
  change spMap a.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]

theorem str_of_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    (a.toRingHom.comp (inB P' x0 hu)).comp P'.str = (algebraMap O D).comp x0 := by
  rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc]
  congr 1
  exact a.comp_algebraMap

theorem at_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    P'.At ((algebraMap O D).comp x0) (spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left)
      (a.toRingHom.comp (inB P' x0 hu)) :=
  ⟨str_of_alg P' x0 hu a, rfl⟩

theorem exists_mul_affine {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {D : Type} [CommRing D] [Algebra O D]
    (a b : Bt P' x0 hu →ₐ[O] D) :
    ∃ z : specO O D ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 =
      (ptMap a ≫ aH P' x0 hu hg.1) * (ptMap b ≫ aH P' x0 hu hg.1) := by
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  obtain ⟨β'', h''⟩ := GlobalTheory.HTMap.FP.At.mul (w := w₁) (w' := w₂) ha hb
  refine ⟨ptOf P' x0 hu β'' h''.1, ?_⟩
  refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
  · rw [ptOf_aH_π, h''.2]
    exact hg.2 (specO O D) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  · rw [Over.w, Over.w]

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

theorem exists_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg S x y
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg
    (Algebra.TensorProduct.includeLeft : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu)
    Algebra.TensorProduct.includeRight
  refine ⟨c ≫ z₀, ?_⟩
  rw [Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end GlobalTheory.FinPartAt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem aH_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg
  have hinj : Function.Injective (pushHom hg (Hs P' x0 hu)) := by
    intro x y hxy
    apply Over.OverMorphism.ext
    apply hg.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · rw [Over.w x, Over.w y]
  have hw : (pushHom hg (Hs P' x0 hu) (aH P' x0 hu hg.1)) ^ q = 1 :=
    GlobalTheory.HTMap.tors_of (g := spMap (inB P' x0 hu)) (w := P'.u) (aH_left_π P' x0 hu hg.1) P'.fin.tors
  apply hinj
  rw [map_pow, hw, map_one]

end GlobalTheory.FinPartAt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem hs_isFinite (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O)
    (hu : IsUnit (x0 P'.f)) : IsFinite (Hs P' x0 hu).hom := by
  haveI : Module.Finite (Localization.Away P'.f) P'.B := P'.fin.finite
  haveI : Module.Finite (OL P' x0 hu) (Bt P' x0 hu) := Module.Finite.base_change _ _ _
  haveI : Module.Finite O (OL P' x0 hu) := inferInstanceAs (Module.Finite O O)
  haveI : Module.Finite O (Bt P' x0 hu) := Module.Finite.trans (OL P' x0 hu) (Bt P' x0 hu)
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [IsFinite.SpecMap_iff]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.FinPartAt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem spMap_injective_divisor {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_ext_Bt {S : Type} [CommRing S] {α β : Bt P' x0 hu →+* S}
    (h1 : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)))
    (h2 : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu)) : α = β := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    have e : (o ⊗ₜ[Localization.Away P'.f] b : Bt P' x0 hu) =
        algebraMap O (Bt P' x0 hu) (show O from o) * inB P' x0 hu b := by
      change _ = (o ⊗ₜ[Localization.Away P'.f] (1 : P'.B)) * ((1 : OL P' x0 hu) ⊗ₜ b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rw [e, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun h1 (show O from o)) (RingHom.congr_fun h2 b)
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

theorem aH_cancel_aff (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {S : Type} [CommRing S]
    (α β : Bt P' x0 hu →+* S)
    (h : spMap α ≫ (aH P' x0 hu hπ).left = spMap β ≫ (aH P' x0 hu hπ).left) : α = β := by
  have hO : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)) := by
    have e := congrArg (· ≫ G'.hom) h
    simp only [Category.assoc, Over.w (aH P' x0 hu hπ)] at e
    apply spMap_injective_divisor
    exact (GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) α).symm.trans (e.trans (GlobalTheory.HTMap.spc _ β))
  have hB : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu) := by
    have e := congrArg (· ≫ π) h
    simp only [Category.assoc, aH_left_π] at e
    have e2 : spMap (α.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (β.comp (inB P' x0 hu)) ≫ P'.u.left :=
      (GlobalTheory.HTMap.spc_assoc _ _ _).symm.trans (e.trans (GlobalTheory.HTMap.spc_assoc _ _ _))
    refine P'.fin.mono S _ _ (GlobalTheory.HTMap.FP.alg_ext ?_) e2
    change α.comp ((inB P' x0 hu).comp P'.str) = β.comp ((inB P' x0 hu).comp P'.str)
    rw [inB_str, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hO]
  exact ringHom_ext_Bt P' x0 hu hO hB

theorem aH_left_mono (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Mono (aH P' x0 hu hπ).left := by
  constructor
  intro T g h e
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => ?_
  have ea := Spec.map_preimage (T.affineCover.f i ≫ g)
  have eb := Spec.map_preimage (T.affineCover.f i ≫ h)
  have key := aH_cancel_aff P' x0 hu hπ (Spec.preimage (T.affineCover.f i ≫ g)).hom
    (Spec.preimage (T.affineCover.f i ≫ h)).hom (by
      change Spec.map (Spec.preimage (T.affineCover.f i ≫ g)) ≫ _ = Spec.map (Spec.preimage (T.affineCover.f i ≫ h)) ≫ _
      rw [ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (T.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))
  exact ea.symm.trans ((congrArg Spec.map (CommRingCat.hom_ext key)).trans eb)

end GlobalTheory.FinPartAt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

theorem exists_const_add_eps_const {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    (z : TensorProduct K (DualNumber K) (primDR A)) :
    ∃ a b : primDR A, liftSemi (constMor A).pull z =
      (constMor A).pull a + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  induction z with
  | add x y hx hy =>
    obtain ⟨a, b, e⟩ := hx
    obtain ⟨a', b', e'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add (f := _), e, e', map_add (f := _), map_add (f := _), smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul]
    have e1 : (TrivSqZeroExt.inl r.fst : DualNumber K) = algebraMap K (DualNumber K) r.fst := rfl
    have e2 : (TrivSqZeroExt.inr r.snd : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, mul_comm]
    have er : r = algebraMap K (DualNumber K) r.fst + DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [← e1, ← e2, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
    conv_lhs => rw [er]
    exact add_smul _ _ _

theorem liftMor_pull_eq_const_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A,
      (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) +
        (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  intro P K _ A _ A' _ i h g hA hg x
  have a₀ : IsAbelianScheme A := by
    haveI := hA.comm
    haveI : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP K) h).pull x)
  obtain ⟨a, b, e⟩ := exists_const_add_eps_const z
  rw [hz] at e
  have red : (redMor A).pull ((liftMor (epsDP K) h).pull x) = (fibMor h).pull x :=
    GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (fibMor h) (fun _ => rfl) (by simp) x
  have ra : (fibMor h).pull x = a := by
    rw [← red, e, map_add (f := _), LinearMap.map_smulₛₗ, redMor_constMor, redMor_constMor]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom (DualNumber.eps : DualNumber K) = 0 := rfl
    rw [this, zero_smul, add_zero]
  exact ⟨b, by rw [ra]; exact e⟩

end GlobalTheory.CechKS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  first | exact @GlobalTheory.ProjSpace.exists_ratCoords_extend | exact GlobalTheory.ProjSpace.exists_ratCoords_extend | (intros; apply GlobalTheory.ProjSpace.exists_ratCoords_extend <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology : AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham <;> assumption)
end
