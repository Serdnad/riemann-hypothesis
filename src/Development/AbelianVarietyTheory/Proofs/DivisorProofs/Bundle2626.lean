module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_isVecs_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
    {S : Scheme.{0}} {t : SAB H S} {t' : SAB H (Sp ℂ)} {x : Sp ℂ ⟶ S} (m : SABMap t' t x) {g n : ℕ}
    (u : HolUnif t'.G t'.PP.L g) (hd : ∀ v, IsTangent v → ∃! z, u.IsDiff z v)
    (hd' : ∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) {χ : 𝓞 E →+* ℂ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) : ∃ V : Fin n → Fin g → ℂ, IsVecs u m.φ v V ∧ LinearIndependent ℂ V := by
  choose v' hv' using fun i => FlatRow.exists_lift m.cart (v i)
  have ix := FlatDegreeCompare.Indep.of_eigBasis (((FlatRow.fibre_iff m.cart hv').2 m.act χ).2 hv)
  choose V hV using fun i => (hd _ (ix.1 i)).exists
  exact ⟨V, fun i => ⟨v' i, hv' i, hV i⟩, FlatDegreeCompare.ArchExists.linearIndependent_of_indep u hd' ix hV⟩

theorem exists_unif_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  intro E _ _ _ H D l Xo c U τ e y v w h
  rw [← Category.assoc]
  obtain ⟨t', ⟨n⟩⟩ := exists_sab (y ≫ toX Xo c) Xo.univ.t
  obtain ⟨T, hT, -⟩ := CM.exists_pat_of_obj E H D l _ _ _ _ (ModelCompare.objOfSABMap Xo.univ n)
  obtain rfl : T.t = t' := hT
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, κ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all T.pol rig hrig
  obtain ⟨V, hV, iV⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.1
  obtain ⟨W, hW, iW⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.2
  exact ⟨ModelCompare.objOfSABMap Xo.univ n, ModelCompare.objMapOfSABMap Xo.univ n, _, u, Hm, κ, V, W, hA, hV, hW,
    iV, iW⟩

end GlobalTheory.DetLine
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.EigParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Generic

variable {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) (χ : 𝓞 E → R)

def IsBasG {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ (∀ i (a : 𝓞 E), u i ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ u i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x u a w

end Generic

variable {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem comb_iff {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (a : Fin n → R) (w : epsAt x ⟶ t.G) :
    IsCombAt x a v w ↔ IsCombAtG t x (fun i => (v i).left) a w.left :=
  exists_congr fun _ => and_congr Iff.rfl ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h.symm⟩

theorem basis_iff (χ : 𝓞 E →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) :
    IsEigBasisAt t.act x χ v ↔ IsBasG t x χ (fun i => (v i).left) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨Over.w (v i), (h1 i).1⟩, fun i a => (h1 i).2 a, fun w hw he => ?_⟩
    let w' : epsAt x ⟶ t.G := Over.homMk w hw.1
    exact (existsUnique_congr fun a => comb_iff v a w').1 (h2 w' ⟨hw.2, he⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨(h1 i).2, h2 i⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => comb_iff v a w).2 (h3 w.left ⟨Over.w w, hw.1⟩ hw.2)

theorem exists_over (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : IsBasG t x χ u) :
    ∃ v : Fin n → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => Over.homMk (u i) (hu.1 i).1, (basis_iff χ _).2 hu, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem exists_left (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) :
    ∃ u : Fin m → (Sp (DualNumber R) ⟶ t.G.left), IsBasG t x χ u ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => (v i).left, (basis_iff χ _).1 hv, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem eigFrame_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (V : Set (gen Y)) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y), x ≫ genStr Y = spMap j → Set.range x ⊆ V → ∀ f : EigFrame Y j (x ≫ genι Y), (∃ v w, FrY Y V τ j x v w ∧ Match τ f v w) ∧ ∀ v w, FrY Y V τ j x v w → ∃ f' : EigFrame Y j (x ≫ genι Y), Match τ f' v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ hτ V R _ j x hx hV f
  have hp : D.mult τ = D.p := GlobalTheory.Harm.mult_of_mem D hτ
  have hq : D.mult (conjEmb τ) = D.q := GlobalTheory.Harm.mult_conjEmb_of_mem D hτ
  have hne : conjEmb τ ≠ τ := fun e => (GlobalTheory.Harm.not_mem_hostType_iff H τ).2 (by rw [e]; exact hτ) hτ
  have hf : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (f.v σ) :=
    fun σ => ⟨f.tan σ, f.eig σ, f.basis σ⟩
  refine ⟨?_, fun v w h => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_over _ hp (hf τ)
    obtain ⟨w, hw, hw'⟩ := exists_over _ hq (hf (conjEmb τ))
    refine ⟨v, w, ⟨hx, hV, hv, ?_⟩, hv', hw'⟩
    rw [comp_chi_bar]
    exact hw
  · obtain ⟨-, -, hv, hw⟩ := h
    rw [comp_chi] at hv
    rw [comp_chi_bar] at hw
    obtain ⟨v₁, a, a'⟩ := exists_left _ hp hv
    obtain ⟨w₁, b, b'⟩ := exists_left _ hq hw
    classical
    let g := Function.update (Function.update f.v τ v₁) (conjEmb τ) w₁
    have g1 : g τ = v₁ := by
      simp only [g, Function.update_of_ne hne.symm, Function.update_self]
    have g2 : g (conjEmb τ) = w₁ := Function.update_self _ _ _
    have hg : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (g σ) := fun σ => by
      by_cases e2 : σ = conjEmb τ
      · rw [e2, g2]; exact b
      by_cases e1 : σ = τ
      · rw [e1, g1]; exact a
      have : g σ = f.v σ := by simp only [g, Function.update_of_ne e2, Function.update_of_ne e1]
      rw [this]; exact hf σ
    refine ⟨⟨g, fun σ => (hg σ).1, fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩, fun i k e => ?_, fun i k e => ?_⟩
    · exact (a' i k e).trans (congrFun g1 k).symm
    · exact (b' i k e).trans (congrFun g2 k).symm

end GlobalTheory.DetLine.EigParts
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_vecEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Xo.XF c) :
    ∃ e : (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G) ≃ (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G),
      ∀ (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)),
        SameVecs Y x v (fun i => e (v i)) ∧ ∀ χ : 𝓞 E →+* R,
          IsEigBasisAt Xo.univ.t.act (x ≫ toX Xo c) χ v ↔
            IsEigBasisAt Y.t.act ((x ≫ Y.jQ) ≫ genι Y) χ (fun i => e (v i)) := by
  obtain ⟨e₀, he₀, hb₀⟩ := BdryUnit.exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act x (x ≫ toX Xo c) rfl
  obtain ⟨e, he, hb⟩ := BdryUnit.exists_eigEquiv Y.m.cart Y.m.act x ((x ≫ Y.jQ) ≫ genι Y) (Category.assoc _ _ _)
  refine ⟨e₀.symm.trans e, fun n v => ⟨fun i => ⟨e₀.symm (v i), ?_, (he _).symm⟩, fun χ => ?_⟩⟩
  · exact (he₀ _).symm.trans (congrArg (fun z => z.left) (e₀.apply_symm_apply (v i)))
  · have h := hb₀ χ n fun i => e₀.symm (v i)
    have hv : (fun i => e₀ (e₀.symm (v i))) = v := funext fun i => e₀.apply_symm_apply (v i)
    rw [hv] at h
    exact h.symm.trans (hb χ n fun i => e₀.symm (v i))

theorem frame_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c), (∀ v w, FrU Xo c U τ j x v w → ∃ vb wb, FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) ∧ (∀ (V : Set (gen Y)) vb wb, Set.range x ⊆ U → FrY Y V τ j (x ≫ Y.jQ) vb wb → ∃ v w, FrU Xo c U τ j x v w ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ R _ j x
  obtain ⟨e, he⟩ := exists_vecEquiv Y x
  have hs : (x ≫ Y.jQ) ≫ genStr Y = x ≫ toF Xo c := by
    rw [Category.assoc]
    exact congrArg (x ≫ ·) Y.jQ_over
  refine ⟨fun v w h => ⟨fun i => e (v i), fun i => e (w i),
    ⟨hs.trans h.1, ?_, ((he _ v).2 _).1 h.2.2.1, ((he _ w).2 _).1 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩,
    fun V vb wb hU h => ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact subset_closure ⟨x z, h.2.1 ⟨z, rfl⟩, by simp⟩
  · obtain ⟨v, rfl⟩ : ∃ v : Fin D.p → _, vb = fun i => e (v i) :=
      ⟨fun i => e.symm (vb i), funext fun i => (e.apply_symm_apply _).symm⟩
    obtain ⟨w, rfl⟩ : ∃ w : Fin D.q → _, wb = fun i => e (w i) :=
      ⟨fun i => e.symm (wb i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, w, ⟨hs.symm.trans h.1, hU, ((he _ v).2 _).2 h.2.2.1, ((he _ w).2 _).2 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩

end GlobalTheory.DetLine
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif GlobalTheory.ConjTransport GlobalTheory.DetLine

namespace GlobalTheory.ConjFlat

theorem isTangent_of_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ) {t : epsR ℂ ⟶ A}
    (ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left ≫ ψ = (1 : Over.mk y ⟶ G).left) : IsTangent t := by
  refine h.1.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans ht).trans ?_
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    rw [Hom.one_def]
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem isVecs_conj {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y₁ : Sp ℂ ⟶ S} {A A₁ : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A₁] {L : LB A.left} {L₁ : LB A₁.left} {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ)
    {ρ : A₁.left ⟶ A.left} (hρ : IsGrpPullback A₁ A cj ρ) {ψ₁ : A₁.left ⟶ G.left} (hψ : ψ₁ = ρ ≫ ψ) {g n : ℕ}
    {u : HolUnif A L g} {u₁ : HolUnif A₁ L₁ g} (hx : ∀ z, u₁.ex z = cjPt hρ (u.ex (star z)))
    {v : Fin n → (epsAt y ⟶ G)} {v₁ : Fin n → (epsAt y₁ ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v i).left = (1 : Over.mk y ⟶ G).left)
    (h₁ : ∀ i, (v₁ i).left = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (v i).left) {V : Fin n → Fin g → ℂ}
    (hV : IsVecs u ψ v V) : IsVecs u₁ ψ₁ v₁ fun i => star (V i) := by
  intro i
  obtain ⟨t, ht, hd⟩ := hV i
  have tg : IsTangent t := isTangent_of_fibre h (by rw [ht]; exact hv i)
  have w : (spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left)) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
    rw [Category.assoc, show (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) from Over.w t, ← DetExtendZero.spMap_comp, ← DetExtendZero.spMap_comp]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let t₁ : epsR ℂ ⟶ A₁ := Over.homMk (hρ.1.lift _ _ w) (hρ.1.lift_snd _ _ _)
  have e : t₁.left ≫ ρ = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) :=
    hρ.1.lift_fst _ _ _
  refine ⟨t₁, ?_, ?_⟩
  · rw [hψ, ← Category.assoc, e, h₁, ← ht]
    exact Category.assoc _ _ _
  · have := cj_isDiff hρ (pullId u) tg e hd
    intro U hU f
    simp only [hx]
    exact this U hU f

theorem herm_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    herm (Hm.map star) (star z) (star w) = star (herm Hm z w) := by
  rw [herm, herm, ← star_form, star_star, star_star]

theorem isWedgeCoord_conj {g p q : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ}
    {x : Fin q ⊕ Fin p → Fin g → ℂ} {Δ : ℂ} (h : IsWedgeCoord Hm V W x Δ) :
    IsWedgeCoord (Hm.map star) (fun i => star (V i)) (fun j => star (W j)) (fun k => star (x k)) (star Δ) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun k i => star (a k i), fun k i => ?_, ?_⟩
  · have e : star (x k) - ∑ m, star (a k m) • star (V m) = star (x k - ∑ m, a k m • V m) := by
      simp [star_sum]
    rw [e, herm_conj, ha, star_zero]
  · refine ((starRingEnd ℂ).map_det _).trans (congrArg Matrix.det ?_)
    ext k (j | i)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl, herm_conj]
      simp
    · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem isTransport_to_conj {B : Type} [CommRing B] {b : Base l B} {s s₁ s' s₁' : Sp ℂ ⟶ Sp B} {o : Obj D l b s}
    {o₁ : Obj D l b s₁} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o o' u u' Hm Hm' φ) :
    IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, hΛ', star_star, h1, hΛ]
  · rw [hx, hx, ← cjPt_act] at hw
    rw [e, e, hx', hx', star_star, star_star, ← cjPt_act, h2 a _ _ (cjPt_injective m.cart hw)]
  · rw [e, e, herm_map_star, herm_map_star, star_star, star_star, h3]
  · rw [hx, ← cjPt_eta m] at hz
    rw [e, hx', star_star, h4 a _ (cjPt_injective m.cart hz), cjPt_eta]
  · rw [hx, ← cjPt_etaA m] at hz
    rw [e, hx', star_star, h5 a _ (cjPt_injective m.cart hz), cjPt_etaA]

theorem exists_conj_fibre (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ (o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o₁ o cj)
      (k : ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)), k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
  obtain ⟨o₁, ⟨m⟩, -⟩ := exists_conj_obj Xo c y o n
  refine ⟨o₁, m, ?_⟩
  have a : ∀ f : Sp ℂ ⟶ Xo.X, f = cj ≫ y ≫ toX Xo c →
      ∃ k : ObjMap o₁ Xo.univ f, k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
    rintro _ rfl
    exact ObjComp.objMap_comp n m
  exact a _ (Category.assoc _ _ _)

end GlobalTheory.ConjFlat

namespace GlobalTheory

open ConjFlat

theorem isFlatAt_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c)
    (e : c.F →+* ℂ) (hσ : SecU Xo c U τ σ) (h : IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e)) :
    IsFlatAt Xo c U τ σ e := by
  intro y y' v w v' w' hf hf' o o' n n' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hΔ hΔ'
  obtain ⟨o₁, m, k, hk⟩ := exists_conj_fibre Xo c y o n
  obtain ⟨o₁', m', k', hk'⟩ := exists_conj_fibre Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  obtain ⟨v₁, w₁, hf₁, a, b⟩ := exists_pull (starRingEnd ℂ) hf (x' := cj ≫ y) rfl
  obtain ⟨v₁', w₁', hf₁', a', b'⟩ := exists_pull (starRingEnd ℂ) hf' (x' := cj ≫ y') rfl
  have i1 : ∀ z : ℂ, Chart.dualMapR (starRingEnd ℂ) (algebraMap ℂ _ z) = algebraMap ℂ _ (starRingEnd ℂ z) :=
    fun z => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : Chart.dualMapR (starRingEnd ℂ) DualNumber.eps = DualNumber.eps := by ext <;> simp [Chart.dualMapR]
  have s := hσ.1 ℂ ℂ _ _ _ _ _ _ v w v₁ w₁ i1 i2 hf hf₁ rfl a b
  have s' := hσ.1 ℂ ℂ _ _ _ _ _ _ v' w' v₁' w₁' i1 i2 hf' hf₁' rfl a' b'
  have q := h (cj ≫ y) (cj ≫ y') v₁ w₁ v₁' w₁' hf₁ hf₁' o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁' _ _ _ _ _
    (fun i => star (x i)) (star Δ) (star Δ') hA₁ hA₁' (isTransport_to_conj m m' hΛ hx hΛ' hx' hφ)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.1.1 i).1) a hV)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.2.1 i).1) b hW)
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.1.1 i).1) a' hV')
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.2.1 i).1) b' hW')
    (isWedgeCoord_conj hΔ) (by
      have := isWedgeCoord_conj hΔ'
      simpa only [LinearEquiv.trans_apply, conjEquiv_apply, star_star] using this)
  rw [s, s'] at q
  refine (starRingEnd ℂ).injective ?_
  rw [map_mul, map_mul]
  exact q

end GlobalTheory
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

theorem flat_Bt : Module.Flat O (Bt P' x0 hu) := by
  haveI : Module.Free (Localization.Away P'.f) P'.B := P'.fin.free
  haveI : Module.Flat (OL P' x0 hu) (Bt P' x0 hu) := Module.Flat.baseChange _ _ _
  haveI : Module.Flat O (OL P' x0 hu) := inferInstanceAs (Module.Flat O O)
  exact Module.Flat.trans O (OL P' x0 hu) (Bt P' x0 hu)

theorem flat_Hs : Flat (Hs P' x0 hu).hom := by
  haveI := flat_Bt P' x0 hu
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.flat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu
  exact GlobalTheory.FinPartAt.flat_Hs P' x0 hu
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

theorem one_left_π {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) (T : Over S') :
    (1 : T ⟶ G').left ≫ π = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
    show _ = T.hom ≫ f
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
  have h := hg.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have e : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have e' : x₀ = 1 := by
    have := congrArg (· * x₀⁻¹) e
    simpa using this
  exact congrArg Over.Hom.left e'

theorem exists_unit {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) :
    ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = 1 := by
  obtain ⟨β₀, h1, h2⟩ := P'.fin.one O (lo P' x0 hu)
  have hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0 := by
    rw [GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]
    try rfl
  have hid : (specO O O).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)
  refine ⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩
  have hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1 := by
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, h2, one_left_π hg]
      refine (GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]
    · rw [Over.w, Over.w]
  rw [Category.assoc, hz, MonObj.comp_one]

end GlobalTheory.FinPartAt
end
end
