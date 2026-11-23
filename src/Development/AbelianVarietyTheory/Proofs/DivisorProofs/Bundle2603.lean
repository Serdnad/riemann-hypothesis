module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle531
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle634
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

section Generic

variable {S X : Scheme.{0}} {F : Type} [Field F]

def FrameCover (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) (p q : ℕ) : Prop :=
  ∀ z ∈ V, ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : F →+* Γ(X, W))
    (v : Fin p → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G)),
    z ∈ W ∧ IsFrame t π s V χ j (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v w

def IsChg (t : SAB H S) (π : X ⟶ S) {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    (x : Sp R ⟶ X) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G))
    (x' : Sp R' ⟶ X) (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G))
    (M : Matrix (Fin p) (Fin p) R') (N : Matrix (Fin q) (Fin q) R') : Prop :=
  x' = spMap g ≫ x ∧
    (∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (M i) (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i)) ∧
    ∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (N i) (fun k => spMap (Chart.dualMapR g) ≫ (w k).left) (w' i)

def locPt (Y : Scheme.{0}) (y : Y) : Sp (Y.presheaf.stalk y) ⟶ Y := Y.fromSpecStalk y

def genPt (Y : Scheme.{0}) [IsIntegral Y] : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)

def UnitAtPt (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    {Y : Scheme.{0}} [IsIntegral Y] (io : Y ⟶ X) (v₀ : Fin p → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G))
    (w₀ : Fin q → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G)) (δ : Y.functionField) (y : Y) : Prop :=
  ∃ (j : F →+* Y.presheaf.stalk y) (v : Fin p → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G)) (M : Matrix (Fin p) (Fin p) Y.functionField)
    (N : Matrix (Fin q) (Fin q) Y.functionField) (u : (Y.presheaf.stalk y)ˣ),
    IsFrame t π s V χ j (locPt Y y ≫ io) v w ∧
    IsChg t π (algebraMap (Y.presheaf.stalk y) Y.functionField) (locPt Y y ≫ io) v w (genPt Y ≫ io) v₀ w₀ M N ∧
    N.det * algebraMap (Y.presheaf.stalk y) Y.functionField u = M.det * δ

end Generic

variable {D : Datum H} {l : Level H}

theorem comp_chi (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp (HermitianCompactForm.chi c τ) = FramedFlatCoordinates.chr c τ j := rfl

theorem comp_chi_bar (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp ((HermitianCompactForm.chi c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)) = FramedFlatCoordinates.chr c (conjEmb τ) j := by
  refine RingHom.ext fun a => congrArg j (Subtype.ext ?_)
  change τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E))
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj E τ _

section Laws

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R']

theorem exists_pull (g : R →+* R') {j : c.F →+* R} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)}
    {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) {x' : Sp R' ⟶ X}
    (hx : x' = spMap g ≫ x) :
    ∃ (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) (g.comp j) x' v' w' ∧
      (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) ∧
      ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : x' ≫ π = spMap g ≫ x ≫ π := by rw [hx, Category.assoc]
  rw [comp_chi_bar] at h4
  obtain ⟨v', a, a'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := τ) h3
  obtain ⟨w', b, b'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := conjEmb τ) h4
  refine ⟨v', w', ⟨?_, ?_, a, by rw [comp_chi_bar]; exact b⟩, a', b'⟩
  · rw [hx, Category.assoc, h1, DetExtendZero.spMap_comp]
  · rintro _ ⟨z, rfl⟩
    rw [hx, Scheme.Hom.comp_apply]
    exact h2 ⟨_, rfl⟩

theorem exists_chg (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'} {x : Sp R ⟶ X}
    {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} {x' : Sp R' ⟶ X}
    {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') (hx : x' = spMap g ≫ x) :
    j' = g.comp j ∧ ∃ M N, IsChg t π g x v w x' v' w' M N := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hx
  have hj : j' = g.comp j := by
    have := h'.1.symm.trans h₁.1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  subst hj
  choose M hM using fun i => (h₁.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h₁.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  refine ⟨rfl, Matrix.of M, Matrix.of N, hx, fun i => ?_, fun i => ?_⟩
  · simp only [← a]; exact hM i
  · simp only [← b]; exact hN i

theorem sec_chg {σ : Rule t π p q} (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) {g : R →+* R'} {j : c.F →+* R}
    {j' : c.F →+* R'} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)}
    {x' : Sp R' ⟶ X} {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N}
    (hc : IsChg t π g x v w x' v' w' M N) : N.det * g (σ R x v w) = M.det * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain rfl := (exists_chg g h h' hc.1).1
  rw [← hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v₁ w₁ (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h₁ hc.1 a b]
  refine hσ.2 R' _ x' v₁ w₁ v' w' M N h₁ h' (fun i => ?_) fun i => ?_
  · have := hc.2.1 i
    simp only [← a] at this
    exact this
  · have := hc.2.2 i
    simp only [← b] at this
    exact this

theorem isSection_of_chg {σ : Rule t π p q}
    (hσ : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (j' : c.F →+* R') x v w x' v' w' M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w' → IsChg t π g x v w x' v' w' M N →
      N.det * g (σ R x v w) = M.det * σ R' x' v' w') : IsSection t π s V (HermitianCompactForm.chi c τ) σ := by
  refine ⟨fun R R' _ _ g gε j j' x x' v w v' w' h1 h2 h h' hx a b => ?_, fun R _ j x v w v' w' M N h h' a b => ?_⟩
  · obtain rfl : gε = Chart.dualMapR g := by
      refine RingHom.ext fun z => ?_
      have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [e, map_add (f := _), map_mul, h1, h1, h2]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    have := hσ R R' g j j' x v w x' v' w' 1 1 h h' ⟨hx, fun i => ?_, fun i => ?_⟩
    · simpa using this.symm
    · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
    · simp only [← b]; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
  · refine hσ R R (RingHom.id R) j j x v w x v' w' M N h h'
      ⟨by rw [DetExtendZero.spMap_id, Category.id_comp], fun i => ?_, fun i => ?_⟩
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact a i
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact b i

end Laws

section Concrete

variable (Xo : Moduli D l) (c : Coeff l)

abbrev FrU (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c)
    (v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) : Prop :=
  IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) j x v w

abbrev RuleU : Type 1 := Rule Xo.univ.t (toX Xo c) D.p D.q

abbrev SecU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

abbrev NzU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  NowhereZero Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

variable {Xo c} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

abbrev FrY (V : Set (gen Y)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y)
    (v : Fin D.p → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) : Prop :=
  IsFrame Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) j x v w

abbrev RuleY : Type 1 := Rule Y.t (genι Y) D.p D.q

abbrev SecY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  IsSection Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

abbrev NzY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  NowhereZero Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

variable {Y}

def Match (τ : E →+* ℂ) {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Y.X} (f : EigFrame Y φ x)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (v i).left = f.v τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (w i).left = f.v (conjEmb τ) k

def PerData (c : Coeff l) (e : c.F →+* ℂ) (Di : Datum H) {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (P : Di.La →+ (Fin g → ℂ)) (W : Pad.Letter D → Fin g → ℂ) (Q : Di.La →+ (Pad.Letter D → ℂ)) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
    (∀ a b, (herm Hm (P a) (P b)).im = Di.EF a b) ∧ LinearIndependent ℂ W ∧ (∀ v, P v = ∑ z, Q v z • W z) ∧
    ∀ (a : 𝓞 E) v (z : Pad.Letter D), Q (a • v) z = Formalism.L2.PjFree.relab c e z.1 (a : E) * Q v z

def MatchVec (τ : E →+* ℂ) {g : ℕ} (W : Pad.Letter D → Fin g → ℂ) (V : Fin D.p → Fin g → ℂ)
    (W₀ : Fin D.q → Fin g → ℂ) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → V i = W ⟨τ, k⟩) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → W₀ i = W ⟨conjEmb τ, k⟩

end Concrete

end GlobalTheory.DetLine
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpenModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem charZero_of_range [IsOpenImmersion Y.j] {R : Type} [CommRing R] [Nontrivial R] (z : Sp R ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : CharZero R :=
  charZero_of_injective_ringHom (Spec.preimage (IsOpenImmersion.lift Y.j z h ≫ pullback.snd _ _)).hom.injective

theorem exists_keyAt_of_range [IsOpenImmersion Y.j] (hpq : 1 ≤ D.p + D.q) (M : GChart Y) {R : Type} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (h : Set.range z ⊆ Set.range Y.j) :
    ∃ x : KeyIn R, KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := exists_sab z Y.t
  have e : IsOpenImmersion.lift Y.j z h ≫ Y.j = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t Y.j (IsOpenImmersion.lift Y.j z h) Y.m (e.symm ▸ m)
  have hp₀ := Y.oF.proper
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp₀
  have hA : Out.RelAmple t.G t.PP.L := by
    have h₁ := AmpleBaseChange.relAmple_of_isPullback Y.oF.t.PP.isLB Y.oF.ample m'.cart.1
    refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls (pull_isLB Y.oF.t.PP.isLB m'.φ) t.PP.isLB le_rfl ?_).2 h₁
    rw [one_smul]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m')
  have := charZero_of_range z h
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h₂ := IsTotallyComplex.finrank E
    exact Nat.mul_pos (by omega) hpq
  obtain ⟨x₀, -, h₀⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (spMap (algebraMap R (FractionRing R)) ≫ z)
    (le_preimage_comp _ hz) (by
      rintro _ ⟨s, rfl⟩
      exact h ⟨_, rfl⟩) hpos
  obtain ⟨x, -, hx⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hz m hp hA _ h₀
  exact ⟨x, hx⟩

theorem exists_unit_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y hO hj hpq κ hκ M
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : IsReduced Y.X := by
    have (x : Y.X) : _root_.IsReduced (Y.X.presheaf.stalk x) := by
      have := GlobalTheory.IsNormalScheme.isDomain_stalk x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  let W₀ : Y.X.Opens := M.U ⊓ Y.j.opensRange
  have hW₀ : ∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j := fun x => Iff.rfl
  have hr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ Y.X), ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := by
    rintro R _ z hz _ ⟨s, rfl⟩
    exact ((hW₀ _).1 (hz (Set.mem_univ s))).2
  let P : Y.X.Opens → Prop := fun W => IsDomain Γ(Y.X, W)
  have hP : ∀ q ∈ W₀, ∃ W : Y.X.Opens, IsAffineOpen W ∧ W ≤ W₀ ∧ P W ∧ q ∈ W := fun q hq => by
    obtain ⟨D', hqD, hD⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X q
    obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ ((W₀ ⊓ D' : Y.X.Opens) : Set Y.X) from ⟨hq, hqD⟩) (W₀ ⊓ D').isOpen
    exact ⟨W, hW, fun r hr => (hle hr).1, hD W hqW fun r hr => (hle hr).2, hqW⟩
  have loc₁ : ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (hWV : W ≤ W₀), P W →
      ∃ (y : KeyIn Γ(Y.X, W)) (u : Γ(Y.X, W)ˣ),
        KeyAt M (tau hW) (tau_le hW (hWV.trans inf_le_left)) y ∧ GlobalTheory.KeyCl.IsValue κ y (u : Γ(Y.X, W)) := by
    intro W hW hWV hdom
    have : IsDomain Γ(Y.X, W) := hdom
    have : IsNoetherianRing Γ(Y.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : IsIntegrallyClosed Γ(Y.X, W) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
    have : CharZero Γ(Y.X, W) := charZero_of_range (tau hW) (hr _ (tau_le hW hWV))
    obtain ⟨y, hy⟩ := exists_keyAt_of_range hpq M (tau hW) (tau_le hW (hWV.trans inf_le_left)) (hr _ (tau_le hW hWV))
    obtain ⟨u, hu⟩ := GlobalTheory.KeyFamUnit.famUnit κ hκ.2.1 hκ.2.2.1 Γ(Y.X, W) y
    exact ⟨y, u, hy, hu⟩
  obtain ⟨f, hf⟩ := GlobalTheory.KeyOpen.glue_units W₀ P hP
    (fun L _ z v => ∀ (hc : CharZero L) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn L), KeyAt M z hz' x → v = (κ L x : L))
    (fun L _ z hz v w hv hw => by
      have hc : CharZero L := charZero_of_range z (hr z hz)
      have hz' : ⊤ ≤ z ⁻¹ᵁ M.U := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      obtain ⟨x, hx⟩ := exists_keyAt_of_range hpq M z hz' (hr z hz)
      exact (hv hc _ x hx).trans (hw hc _ x hx).symm)
    (fun W hW hWV hPW => by
      obtain ⟨y, u, hy, hu⟩ := loc₁ W hW hWV hPW
      refine ⟨u, fun L _ z hz hc hz' x hx => ?_⟩
      have e : spMap (ev z W hz) ≫ tau hW = z := GlobalTheory.FlagMod.spMap_ev z hW hz
      generalize ev z W hz = φ at e ⊢
      subst e
      exact (hu L φ x (GlobalTheory.KeyAtBC.keyPB_of_keyAt hy hx)).symm)
  exact ⟨W₀, f, hW₀, fun K _ hK z hz hz' x hx => hf K z hz hK hz' x hx⟩

end GlobalTheory.KeyOpenModel
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.exists_integralFramedData_completeDVR_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  first | exact @GlobalTheory.FramedExt.exists_framed_ext | exact GlobalTheory.FramedExt.exists_framed_ext | (intros; apply GlobalTheory.FramedExt.exists_framed_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  first | exact @GlobalTheory.ZConvIdent.translates_kerSmall_le_theta | exact GlobalTheory.ZConvIdent.translates_kerSmall_le_theta | (intros; apply GlobalTheory.ZConvIdent.translates_kerSmall_le_theta <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_flagCover_chart_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  first | exact @GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | exact GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | (intros; apply GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt <;> assumption)
end
