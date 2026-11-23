module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle465
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle466
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

theorem _root_.GlobalTheory.T.psiE_xi0_mul_cA_eq_one_of_mem_complId : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  first | exact @GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | exact GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | (intros; apply GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedDict

open scoped Matrix

theorem sum_form_orthoFrame {K : Type} [Field K] [StarRing K] {n : ℕ} (G B : Matrix (Fin n) (Fin n) K)
    (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

theorem isSelfDualC_inV : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  intro D S fr hfr Ls hLs
  classical
  have hB : fr.1ᴴ * S.gram * fr.1 = 1 := hfr
  obtain ⟨hfg, hspan, hdual⟩ := hLs
  let f : (Fin S.rank → D.host.E) →ₗ[D.host.E] (Fin S.rank → D.host.E) := Matrix.toLin' fr.1
  have hinv : ∀ y, fr.1 *ᵥ ((fr⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv' : ∀ y, (fr⁻¹).1 *ᵥ (fr.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) ↔ (fr⁻¹).1 *ᵥ y ∈ Ls := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [f, Matrix.toLin'_apply, hinv'] using hx
    · intro h
      exact ⟨_, h, by simp [f, Matrix.toLin'_apply, hinv]⟩
  have hform : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j =
      ∑ i, star (((fr⁻¹).1 *ᵥ x) i) * ((fr⁻¹).1 *ᵥ y) i := by
    intro x y
    have := sum_form_orthoFrame S.gram fr.1 hB ((fr⁻¹).1 *ᵥ x) ((fr⁻¹).1 *ᵥ y)
    rwa [hinv, hinv] at this
  refine ⟨Ls.map (f.restrictScalars (𝓞 D.host.E)), ?_, Submodule.IsLattice.of_fg D.host.E (hfg.map _), fun y => ?_⟩
  · ext x
    simp [inV, f, Matrix.toLin'_apply]
  · rw [hmem, hdual]
    constructor
    · intro h x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := h _ hx
      exact ⟨b, by rw [hform]; exact hb⟩
    · intro h x' hx'
      have hx : fr.1 *ᵥ x' ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) := by
        rw [hmem, hinv']; exact hx'
      obtain ⟨b, hb⟩ := h _ hx
      rw [hform, hinv'] at hb
      exact ⟨b, hb⟩

end GlobalTheory.MovedDict

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_gen_isoLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  have hL₁ : Z.o₁.t.PP.L.IsLB := Z.o₁.t.PP.isLB
  have hL₂ : Z.o₂.t.PP.L.IsLB := Z.o₂.t.PP.isLB
  obtain ⟨w₁, hw₁, -⟩ := Z.m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := Z.m₂.lin
  have i₁ : LBIso Z.o₁.t.PP.L (Xo.univ.t.PP.L.pull Z.m₁.cm.F) := ⟨w₁, hw₁⟩
  have i₂ : LBIso Z.o₂.t.PP.L (Xo.univ.t.PP.L.pull Z.m₂.cm.F) := ⟨w₂, hw₂⟩
  have i₃ : LBIso (lbPow Z.o₁.t.PP.L (p ^ 2)) (Xo.univ.t.PP.L.pull (Z.ψ.left ≫ Z.m₂.cm.F)) :=
    GlobalTheory.ThetaAffineGlue.lbIso_comp (isLB_lbPow hL₁ _) hL₂ hL Z.isog.1.2.2.2.2.2 i₂
  have i₄ := GlobalTheory.ThetaAffineGlue.lbIso_pull i₃ (hkLift Z h hx)
  have i₅ := GlobalTheory.Spread.lbIso_pow_pull_comp hL hL₁ i₁ (hkLift Z h hx) (hkLift_φ Z hx).symm (p ^ 2)
  have i₆ := lbIso_lbPow_pull hL₁ (hkLift Z h hx) (p ^ 2)
  have i₇ := GlobalTheory.EmbVA.lbIso_pow hL (snd (Over.mk x) Xo.univ.t.G).left (p ^ 2) ((p : ℤ) ^ 2) (by push_cast; rfl)
  have i₈ := ((i₇.trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL _) _)
    (isLB_lbPow (pull_isLB hL₁ _) _) i₅.symm).trans (LB.isLB_linComb hL _ _) (isLB_lbPow (pull_isLB hL₁ _) _)
    (pull_isLB (isLB_lbPow hL₁ _) _) i₆).trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL₁ _) _)
    (pull_isLB hL _) i₄
  have e := (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).1 i₈
  rw [Fin.prod_univ_one, Fintype.prod_unique, zpow_one] at e
  refine (GlobalTheory.PrimNorm.hasGen_iff hL (isoφ Xo.univ.t.G (hkMap Z hx hx')) ![(p : ℤ) ^ 2, -1]).2 ?_
  rw [prod_iso', hkMap_snd, e, mul_inv_cancel]

end GlobalTheory.HeckeEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open GlobalTheory.HeckeFrCompare (gx_ext toFib_fst toFib_fst_assoc toFib_snd)
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (push toFib)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

def overCast {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (Over.mk u : Over X) ⟶ Over.mk v :=
  Over.homMk (𝟙 _) (by simp [e])

@[simp] theorem overCast_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (overCast e).left = 𝟙 _ := rfl

theorem overCast_comp_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) {G : Over X} (a : Over.mk v ⟶ G) :
    (overCast e ≫ a).left = a.left := by
  rw [Over.comp_left, overCast_left, Category.id_comp]

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem hkLift_act (hx : x = h ≫ Z.π₁) (r : 𝓞 E) :
    (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ hkLift Z h hx = hkLift Z h hx ≫ (Z.o₁.t.act.act r).left := by
  refine Z.m₁.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, hkLift_φ, Category.assoc, Z.m₁.act, hkLift_φ_assoc, ← Over.comp_left, whiskerLeft_snd,
      Over.comp_left]
  · rw [Category.assoc, hkLift_hom, Category.assoc, Over.w, hkLift_hom, ← Category.assoc, ← Over.comp_left,
      whiskerLeft_fst]

def hkLiftPt (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (Over.mk (t ≫ h) : Over Z.Hk) ⟶ Z.o₁.t.G :=
  Over.homMk (toFib x t a ≫ hkLift Z h hx) (by
    rw [Category.assoc, hkLift_hom, toFib_fst_assoc]; rfl)

theorem hkLiftPt_left (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left = toFib x t a ≫ hkLift Z h hx := rfl

theorem hkLiftPt_φ (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left ≫ Z.m₁.cm.F = a.left := by
  rw [hkLiftPt_left, Category.assoc, hkLift_φ, toFib_snd]

theorem hkLiftPt_mul (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    hkLiftPt Z hx t (a₁ * a₂) = hkLiftPt Z hx t a₁ * hkLiftPt Z hx t a₂ := by
  have e : (t ≫ h) ≫ Z.π₁ = t ≫ x := by rw [hx, Category.assoc]
  have key := Z.m₁.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁) (hkLiftPt Z hx t a₂) (overCast e ≫ a₁)
    (overCast e ≫ a₂) (by rw [overCast_comp_left, hkLiftPt_φ]) (by rw [overCast_comp_left, hkLiftPt_φ])
  refine Over.OverMorphism.ext (Z.m₁.cart.1.hom_ext ?_ ?_)
  · rw [hkLiftPt_φ, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · rw [Over.w, Over.w]

theorem push_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) {T' : Scheme.{0}} (t : T' ⟶ Sp T)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push (hkMap Z hx hx') t a = (hkLiftPt Z hx t a ≫ Z.ψ).left ≫ Z.m₂.cm.F := by
  rw [push, hkMap_snd, Over.comp_left, hkLiftPt_left]
  simp only [Category.assoc]

theorem isLinHom_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : IsLinHom (hkMap Z hx hx') := by
  haveI : IsMonHom Z.ψ := Z.isog.1.1
  refine ⟨hkMap_fst Z hx hx', fun T' t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · have e : (t ≫ h) ≫ Z.π₂ = t ≫ x' := by rw [hx', Category.assoc]
    have key := Z.m₂.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁ ≫ Z.ψ) (hkLiftPt Z hx t a₂ ≫ Z.ψ) (overCast e ≫ b₁)
      (overCast e ≫ b₂) (by rw [overCast_comp_left, h₁, push_hkMap]) (by rw [overCast_comp_left, h₂, push_hkMap])
    rw [push_hkMap, hkLiftPt_mul, MonObj.mul_comp, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · have w : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (snd (Over.mk z) Xo.univ.t.G).left =
        (snd (Over.mk z) Xo.univ.t.G).left ≫ (Xo.univ.t.act.act r).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have w₀ : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_fst]
    have hψ : (Z.o₁.t.act.act r).left ≫ Z.ψ.left = Z.ψ.left ≫ (Z.o₂.t.act.act r).left := by
      rw [← Over.comp_left, Z.isog.1.2.2.2.2.1 r, Over.comp_left]
    refine gx_ext ?_ ?_
    · rw [Category.assoc, hkMap_fst, w₀, Category.assoc, w₀, hkMap_fst]
    · rw [Category.assoc, hkMap_snd, hkLift_act_assoc, reassoc_of% hψ, Z.m₂.act, Category.assoc, w,
        hkMap_snd_assoc]

end GlobalTheory.HeckeEx

end

theorem GlobalTheory.HeckeEx.isLinHom_hkMap_target : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') :=
  fun _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ _ _ hx hx' => GlobalTheory.HeckeEx.isLinHom_hkMap Z hx hx'
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipPaths

variable {T : Type}

theorem arrows_comp {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp p q]

theorem rowPath_arrows (j : ℕ) : ∀ n, (rowPath T j n).arrows = (List.range n).map fun i => Arrow.right i j
  | 0 => by simp [rowPath, Path.arrows]
  | n + 1 => by simp [rowPath, Path.arrows, rowPath_arrows j n, List.range_succ]

theorem downPath_arrows (t : T) (i : ℕ) : ∀ n, (downPath t i n).arrows = (List.range n).reverse.map fun j => Arrow.down t i j
  | 0 => by simp [downPath, Path.arrows]
  | n + 1 => by simp [downPath, arrows_comp, Path.arrows, downPath_arrows t i n, List.range_succ]

theorem edgeOf_inj {m : ℕ} {t : T} {a b : Arrow T} (ha : GlobalTheory.FlipRun.IsGridArrow m t a) (hb : GlobalTheory.FlipRun.IsGridArrow m t b)
    (h : GlobalTheory.FlipRun.edgeOf a = GlobalTheory.FlipRun.edgeOf b) : a = b := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> rcases hb with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩ <;>
    simp_all [GlobalTheory.FlipRun.edgeOf]

theorem map_edgeOf_inj {m : ℕ} {t : T} : ∀ (l₁ l₂ : List (Arrow T)), (∀ a ∈ l₁, GlobalTheory.FlipRun.IsGridArrow m t a) →
    (∀ a ∈ l₂, GlobalTheory.FlipRun.IsGridArrow m t a) → l₁.map GlobalTheory.FlipRun.edgeOf = l₂.map GlobalTheory.FlipRun.edgeOf → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [edgeOf_inj (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_edgeOf_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

theorem gridArrowPath_heq_of_arrows_eq {X : Node} : ∀ {Y : Node} (p : Path T X Y) {Y' : Node} (q : Path T X Y'),
    p.arrows = q.arrows → HEq p q := by
  intro Y p
  induction p with
  | nil =>
    intro Y' q h
    cases q with
    | nil => rfl
    | snoc b q => simp [Path.arrows] at h
  | snoc a p ih =>
    intro Y' q h
    cases q with
    | nil => simp [Path.arrows] at h
    | snoc b q =>
      simp only [Path.arrows] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      have := eq_of_heq (ih q h1)
      subst this
      rfl

theorem eq_of_arrows {X Y : Node} (p q : Path T X Y) (h : p.arrows = q.arrows) : p = q :=
  eq_of_heq (gridArrowPath_heq_of_arrows_eq p q h)

theorem givenPath_arrows (t : T) (m : ℕ) : (givenPath t m).arrows =
    (List.range m).reverse.map (fun j => Arrow.down t 0 j) ++ (List.range m).map fun i => Arrow.right i 0 := by
  simp [givenPath, arrows_comp, rowPath_arrows, downPath_arrows]

theorem oppPath_arrows (t : T) (m : ℕ) : (oppPath t m).arrows =
    (List.range m).map (fun i => Arrow.right i m) ++ (List.range m).reverse.map fun j => Arrow.down t m j := by
  simp [oppPath, arrows_comp, rowPath_arrows, downPath_arrows]

theorem given_opp_paths : ∀ {T : Type} (m : ℕ) (t : T), (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.givenPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.givenPath t m) = GlobalTheory.SplitFlip.givenPath m) ∧ (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.oppPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.oppPath t m) = GlobalTheory.SplitFlip.oppositePath m) ∧ ∀ {X Y : Node} (p q : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.FlipRun.OnGrid m t q → GlobalTheory.FlipRun.edges p = GlobalTheory.FlipRun.edges q → p = q := by
  intro T m t
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [givenPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inr ⟨0, j, Nat.zero_le _, hj, rfl⟩
    · exact Or.inl ⟨i, 0, hi, Nat.zero_le _, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, givenPath_arrows, GlobalTheory.SplitFlip.givenPath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro a ha
    rw [oppPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact Or.inl ⟨i, m, hi, le_rfl, rfl⟩
    · exact Or.inr ⟨m, j, le_rfl, hj, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, oppPath_arrows, GlobalTheory.SplitFlip.oppositePath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro X Y p q hp hq h
    exact eq_of_arrows p q (map_edgeOf_inj _ _ hp hq h)

end GlobalTheory.FlipPaths
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem pathConv_zip_fock (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ d : PureT G p), VecAll ρ e p φ d →
      ∀ (P' : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      PathConv W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F ∧
      IsCuspListed W.θ Y (liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F) := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ _ _ _ _ hF
    exact ⟨trivial, hF⟩
  | snoc a p ih =>
    intro hg φ d hv P' F hF
    have hg' : OnGrid D.R.m t p := fun b hb => hg b (List.mem_append_left [a] hb)
    have ha : IsGridArrow D.R.m t a := hg a (List.mem_append_right p.arrows (List.mem_singleton_self a))
    obtain ⟨h1, h2⟩ := ih hg' φ.1 d.1 hv.1 P'.1 F hF
    obtain ⟨h3, h4⟩ := hC a ha e he φ.2 d.2 hv.2 P'.2 _ h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem mem_support_tensT {X Y : Node} {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) (x : PureT G p)
    (hx : x ∈ (tensT W τi τf).support) :
    ∃ d ∈ τf.support, ∃ P' : PolT G p, x = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P' := by
  classical
  unfold tensT at hx
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  obtain ⟨d, hd, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d, hd, P, Finset.mem_singleton.1 (Finsupp.support_single_subset hx')⟩

theorem totConv_tensE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ : TotT G p) (φ : PureT G p → PureT G p), (∀ d ∈ τ.support, GlobalTheory.FlipRun.VecAll ρ e p (φ d) d) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, TotConv W M p (GlobalTheory.FlipRun.tensE W p Q τ) F := by
  intro D T L sc G W M ρ t e he hC X Y p hg τ φ hv F hF Q x hx
  obtain ⟨d, hd, P', rfl⟩ := mem_support_tensT _ τ x hx
  exact (pathConv_zip_fock M ρ t he hC p hg (φ d) d (hv d hd) P' F hF).1

end GlobalTheory.FlipRun
end
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)), (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  first | exact @GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | (intros; apply GlobalTheory.ExtTensorIrr.piTensor_isIrreducible <;> assumption)
end
