module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle623
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

instance mono_spMap_ringOfIntegers (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) :=
  have := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K)) (S := K)
  inferInstance

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section Move

variable {A B T : Type} [CommRing A] [Algebra c.F A] [CommRing B] [Algebra c.F B] [CommRing T] [Algebra c.F T]

theorem ptF_fst (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _

theorem ptF_snd (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.snd _ _ = spMap (algebraMap c.F A) :=
  pullback.lift_snd _ _ _

theorem ptF_map {φ : A →ₐ[c.F] B} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : Q.x = spMap φ.toRingHom ≫ P.x) :
    GlobalTheory.AllWt.ptF Q = spMap φ.toRingHom ≫ GlobalTheory.AllWt.ptF P := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptF_fst, ptF_fst, h]
  · rw [Category.assoc, ptF_snd, ptF_snd, sp_comp]
    exact congrArg spMap φ.comp_algebraMap.symm

def umap (φ : A →ₐ[c.F] B) (t : Ix Dw → Aˣ) : Ix Dw → Bˣ := fun i => Units.map (φ : A →* B) (t i)

theorem frBor_one (P : FrPt Xo c A) : FrBor 1 P P :=
  ((frBor_calculus E H Dw l Xo c A P P P).1 1).2 ⟨fun _ => 1, fun _ _ _ h => Matrix.one_apply_ne h.ne,
    fun _ _ => Matrix.one_apply_eq _, (frChg_refl_and_comp E H Dw l Xo c A P P P).1⟩

def BM (φ : A →ₐ[c.F] B) (t : Ix Dw → Bˣ) (P : FrPt Xo c A) (Q : FrPt Xo c B) : Prop :=
  ∃ P', FrMap φ P P' ∧ FrBor t P' Q

theorem BM.of_frBor {t : Ix Dw → Aˣ} {P Q : FrPt Xo c A} (h : FrBor t P Q) : BM (AlgHom.id _ _) t P Q :=
  ⟨P, frMap_id P, h⟩

theorem BM.x_eq {φ : A →ₐ[c.F] B} {t : Ix Dw → Bˣ} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : BM φ t P Q) :
    Q.x = spMap φ.toRingHom ≫ P.x := by
  obtain ⟨P', h1, h2⟩ := h
  exact h2.1.trans h1.1

end Move

section Dict

variable {S T : Type} [CommRing S] [CommRing T]


attribute [local instance] Over.cartesianMonoidalCategory in
open GlobalTheory.Exist.FlagBaseChange MonObj in
theorem sab_dict {X X' : Scheme.{0}} {t' : SAB H X'} {t : SAB H X} {f : X' ⟶ X} (m : SABMap t' t f) {x' : Sp S ⟶ X'}
    {x : Sp S ⟶ X} (hx : x' ≫ f = x) :
    (∀ v : Sp (DualNumber S) ⟶ t.G.left, v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x →
      ∃ w, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ∧ w ≫ m.φ = v) ∧
    (∀ w : Sp (DualNumber S) ⟶ t'.G.left, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsTanAtG t x (w ≫ m.φ) ↔ IsTanAtG t' x' w) ∧ ∀ χ : 𝓞 E → S,
        (∀ a, (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w ≫ m.φ) ↔
          ∀ a, w ≫ (t'.act.act a).left = spMap (epsMul (χ a)) ≫ w) ∧
    ∀ (n : ℕ) (w : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)) (a : Fin n → S) (w' : Sp (DualNumber S) ⟶ t'.G.left),
      (∀ i, w i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') →
      w' ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsCombAtG t x (fun i => w i ≫ m.φ) a (w' ≫ m.φ) ↔ IsCombAtG t' x' w a w') := by
  obtain ⟨B, hB, h1, h2, h3⟩ := exists_tangentEquiv m.cart t'.act.act t.act.act m.act x' x hx
  refine ⟨fun v hv => ?_, fun w hw => ⟨?_, fun χ => ?_⟩, fun n w a w' hw hw' => ?_⟩
  · obtain ⟨w, e⟩ := B.surjective (Over.homMk v hv)
    exact ⟨w.left, Over.w w, (hB w).symm.trans (congrArg (fun u => u.left) e)⟩
  · have := h1 (Over.homMk w hw)
    unfold TanAt at this
    rw [hB] at this
    have e := Over.w (B (Over.homMk w hw))
    rw [hB] at e
    exact (and_iff_right e).trans (this.trans (and_iff_right hw).symm)
  · have := h2 χ (Over.homMk w hw)
    unfold EigAt at this
    simp only [Over.comp_left, hB] at this
    exact this
  · have := h3 n (fun i => Over.homMk (w i) (hw i)) a (Over.homMk w' hw')
    unfold CombAt at this
    simp only [hB, Over.OverMorphism.ext_iff] at this
    unfold IsCombAtG
    simp only [eq_comm (b := w'), eq_comm (b := w' ≫ m.φ)]
    exact this

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)

def TanRel (xF : Sp S ⟶ Xo.XF c) (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Z.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ xF ∧
    w ≫ Z.m0.toSABMap.φ = u ∧ w ≫ Z.m.φ = v

variable {Z} {xF : Sp S ⟶ Xo.XF c} {x₀ : Sp S ⟶ Xo.X} {x : Sp S ⟶ Z.X}

theorem TanRel.map (ψ : S →+* T) {u v} (h : TanRel Z xF u v) :
    TanRel Z (spMap ψ ≫ xF) (spMap (dualMap ψ) ≫ u) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  refine ⟨spMap (dualMap ψ) ≫ w, ?_, Category.assoc _ _ _, Category.assoc _ _ _⟩
  rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
  congr 2
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_tanRel_right (h₀ : xF ≫ pullback.fst _ _ = x₀) {u} (hu : IsTanAt x₀ u) : ∃ v, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m0.toSABMap h₀).1 u hu.1
  exact ⟨_, w, h1, h2, rfl⟩

theorem exists_tanRel_left (hx : xF ≫ Z.j = x) {v} (hv : IsTanAtG Z.t x v) : ∃ u, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m hx).1 v hv.1
  exact ⟨_, w, h1, rfl, h2⟩

theorem TanRel.tan_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {u v} (h : TanRel Z xF u v) :
    IsTanAt x₀ u ↔ IsTanAtG Z.t x v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact ((sab_dict Z.m0.toSABMap h₀).2.1 w h1).1.trans ((sab_dict Z.m hx).2.1 w h1).1.symm

theorem TanRel.eig_iff {u v} (h : TanRel Z xF u v) (χ : 𝓞 E → S) :
    (∀ a, u ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (χ a)) ≫ u) ↔
      ∀ a, v ≫ (Z.t.act.act a).left = spMap (epsMul (χ a)) ≫ v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact (((sab_dict Z.m0.toSABMap rfl).2.1 w h1).2 χ).trans (((sab_dict Z.m rfl).2.1 w h1).2 χ).symm

theorem TanRel.comb_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {n : ℕ} {u v u' v'}
    (h : ∀ i : Fin n, TanRel Z xF (u i) (v i)) (h' : TanRel Z xF u' v') (a : Fin n → S) :
    IsCombAt x₀ u a u' ↔ IsCombAtG Z.t x v a v' := by
  choose w h1 h2 h3 using h
  obtain ⟨w', k1, rfl, rfl⟩ := h'
  obtain rfl : u = _ := (funext h2).symm
  obtain rfl : v = _ := (funext h3).symm
  exact ((sab_dict Z.m0.toSABMap h₀).2.2 n w a w' h1 k1).trans ((sab_dict Z.m hx).2.2 n w a w' h1 k1).symm

variable [Algebra c.F S] [Algebra c.F T]

def Comparison₂ (P : FrPt Xo c S) {φ : c.F →+* S} {x : Sp S ⟶ Z.X} (g : EigFrame Z φ x) : Prop :=
  φ = algebraMap c.F S ∧ GlobalTheory.AllWt.ptF P ≫ Z.j = x ∧ ∀ τ i, TanRel Z (GlobalTheory.AllWt.ptF P) (P.u τ i) (g.v τ i)

theorem exists_tie_frame (P : FrPt Xo c S) (hx : GlobalTheory.AllWt.ptF P ≫ Z.j = x) :
    ∃ g : EigFrame Z (algebraMap c.F S) x, Comparison₂ P g := by
  choose v hv using fun τ i => exists_tanRel_right (Z := Z) (ptF_fst P) (P.tan τ i)
  refine ⟨⟨v, fun τ i => ((hv τ i).tan_iff (ptF_fst P) hx).1 (P.tan τ i), fun τ i => ((hv τ i).eig_iff _).1 (P.eig τ i),
    fun τ w hw he => ?_⟩, rfl, hx, hv⟩
  obtain ⟨u, hu⟩ := exists_tanRel_left hx hw
  exact (existsUnique_congr fun a => TanRel.comb_iff (ptF_fst P) hx (hv τ) hu a).1
    (P.basis τ u ((hu.tan_iff (ptF_fst P) hx).2 hw) ((hu.eig_iff _).2 he))

theorem Comparison₂.tri_of_bm {P : FrPt Xo c S} {Q : FrPt Xo c T} {φ : c.F →+* S} {φ' : c.F →+* T} {x' : Sp T ⟶ Z.X}
    {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} (hf : Comparison₂ P f) (hg : Comparison₂ Q g) {ψ : S →ₐ[c.F] T} {t : Ix Dw → Tˣ}
    (h : BM ψ t P Q) : f.Tri ψ.toRingHom g fun τ i => t (some ⟨τ, i⟩) := by
  have e := ptF_map h.x_eq
  obtain ⟨P', h1, h2⟩ := h
  refine ⟨by rw [← hg.2.1, e, Category.assoc, hf.2.1], by rw [hg.1, hf.1]; exact ψ.comp_algebraMap.symm, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h2.2.1 τ i
  refine ⟨cf, c1, c2, (TanRel.comb_iff ((ptF_fst Q).trans h2.1) hg.2.1 (fun k => ?_) (hg.2.2 τ i) cf).1 c3⟩
  rw [e, h1.2.1]
  exact (hf.2.2 τ k).map _

end Dict

end Descent

end GlobalTheory.ShFam
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def EigFrame.Coord {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (A : Mat Dw.mult R') : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧
    ∀ τ i, IsCombAtG Z.t x' (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (A τ i) (g.v τ i)

def EigFrame.Stable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (ψ : R →+* R'),
    ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i

theorem EigFrame.tri_iff {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) :
    f.Tri ψ g t ↔ ∃ A : Mat Dw.mult R', f.Coord ψ g A ∧ (∀ τ i, A τ i i = t τ i) ∧ ∀ τ i k, i < k → A τ i k = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose A hA hA' hA'' using h3
    exact ⟨A, ⟨h1, h2, hA''⟩, hA, hA'⟩
  · rintro ⟨A, ⟨h1, h2, h3⟩, hA, hA'⟩
    exact ⟨h1, h2, fun τ i => ⟨A τ i, hA τ i, hA' τ i, h3 τ i⟩⟩

variable {F : Type} [Field F]

def Tied (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z)
    (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) {k : (E →+* ℂ) → ℕ} (S : Fr (ratOf Y) Dw.mult k)
    (A₀ : Mat Dw.mult Y.Fn) : Prop :=
  A₀ ∈ S.S (genericPoint Y.X) ∧ ∀ y : Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* Y.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)),
    f.Coord (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ (A₀ * A⁻¹)

end GlobalTheory.ShFam
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Member

theorem selfInter_Lw_interPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) (la : GlobalTheory.AllWt.Weight Dw),
    ((C.Y.inter (fun _ => C.Lw la) : ℤ) : ℝ) =
      C.Y.interPoly (fun x : Root Dw.mult => C.gr x.1 x.2)
        ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ C.Y.dim) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C la
  rw [← Fin.prod_const]
  have h := C.Y.interPoly_prod_sum (fun x : Root Dw.mult => C.gr x.1 x.2)
    (fun _ x => -(GlobalTheory.AllWt.exOf Dw la 0 (some x)))
  push_cast at h
  rw [h]
  congr 2
  funext i
  simp [FlagCpt.Lw, FlagCpt.LEx, Finset.sum_neg_distrib]

end GlobalTheory.Member
end

section

noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

def FlowMajSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom → ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      X.maj (X.flow ξ s x) τ v = X.maj x τ v +
        ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
          (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ))) ∧
    ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (v w : Fin r → ℂ),
      ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w ∧ ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w

def OrbitThickSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∀ x ∈ X.dom, ∃ ε : ℝ, 0 < ε ∧ ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ → ε ≤ X.la1 (X.flow ξ s x)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ThickBdd (φ : Frame X.Ψ r → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ X.dom, ε ≤ X.la1 x → φ x ≤ C

def FreqNonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ

def StepBound (w : ℝ) (φ : Frame X.Ψ r → ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ q : X.Ψ → ℝ, (∀ τ, 0 < q τ ∧ q τ ≤ 1) → ∀ B : ℝ,
    (∀ s : X.Ψ → ℝ, φ (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) ≤ B) →
    φ x ≤ B * ∏ τ, q τ ^ (-w)

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FlowTie {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β)) (k : U.Comp) (ξ' : Fin r → E)
    (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)),
      (∀ τ, 0 < d τ) ∧ (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) ∧
      ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom,
        AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z

def BdExt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {V K : Type} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) : Prop :=
  ∃ (χ : Sp V ⟶ gen Z) (g : EigFrame Z φ (χ ≫ genι Z)), χ ≫ genStr Z = spMap φ ∧
    GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ ∧
    (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ g.v τ i) ∧
    χ (IsLocalRing.closedPoint V) ∈ genBd Z

end Geometric

end GlobalTheory.CuspFrom
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) :=
  GlobalTheory.LocM.isFrame_bc
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩


end Model

end GlobalTheory.HTLine.Dvd
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.divisionCompatible_at_readIdentifications : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  first | exact @GlobalTheory.divTied3_read | exact GlobalTheory.divTied3_read | (intros; apply GlobalTheory.divTied3_read <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.liftScalar_eq_labelScalar : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  first | exact @GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | exact GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | (intros; apply GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label <;> assumption)
end
