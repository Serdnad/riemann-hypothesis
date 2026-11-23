module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeCmEqIdealAndCovolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace PolFibre

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMapR_id : Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem spMap_dual_hom (f : R →+* R') : spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso (L.pull φ) M) (ψ : Z ⟶ Y) :
    LBIso (L.pull (ψ ≫ φ)) (M.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (chartPullPull M ψ ψ rfl) h

theorem refl (P : Out.PolAV (Sp R)) : IsPolFibre (RingHom.id R) P P (𝟙 _) :=
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  ⟨rfl, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id (CommRingCat.of R)).symm rfl,
    LBIso.chartPull (chartPullPull P.L _ (𝟙 _) rfl) (chartPullId P.L) (PolBaseChange.lbIso_refl P.isLB)⟩

theorem vec_refl {A : Over (Sp R)} (v : epsR R ⟶ A) : IsVecOver (RingHom.id R) (𝟙 _) v v := by
  unfold IsVecOver
  rw [dualMapR_id, Category.comp_id]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R))).symm)

variable {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')}
  {φ : P'.A.left ⟶ P.A.left}

theorem comp (h : IsPolFibre f P P' φ) {ψ : P''.A.left ⟶ P'.A.left} (h' : IsPolFibre g P' P'' ψ) :
    IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap f g) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem cancel (h : IsPolFibre f P P' φ) {χ : P''.A.left ⟶ P.A.left} (h' : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ := by
  have n := h'.2.1.congr (spMap_comp_spMap f g).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := h.2.1.1.lift_fst _ _ w
  have e₂ := h.2.1.1.lift_snd _ _ w
  generalize h.2.1.1.lift _ _ w = ψ at e₁ e₂
  subst e₁
  exact ⟨ψ, ⟨h'.1.trans h.1.symm, h.2.1.cancel n e₂,
    LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ).symm h'.2.2⟩, rfl⟩

theorem vec_iff {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    {v'' : epsR R'' ⟶ A''} (w : ψ ≫ A'.hom = A''.hom ≫ spMap g) (h : IsVecOver f φ v v') :
    IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  have e : (spMap (Chart.dualMapR g) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR (g.comp f)) ≫ v.left := by
    rw [Category.assoc, h, ← Category.assoc, ← dualMapR_comp]
    exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)
  refine ⟨fun h' => ?_, fun h' => hφ.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) h').trans e)
  · exact (Category.assoc _ _ _).trans (Eq.trans h' e.symm)
  · rw [Category.assoc, Category.assoc, w, Over.w v', ← Category.assoc, Over.w v'']
    exact (spMap_dual_hom g).symm

end PolFibre

theorem polFibre_id_comp_cancel : (∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), IsPolFibre (RingHom.id R) P P (𝟙 _) ∧ IsVecOver (RingHom.id R) (𝟙 _) v v) ∧ ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') (P : Out.PolAV (Sp R)) (P' : Out.PolAV (Sp R')) (P'' : Out.PolAV (Sp R'')) (φ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' φ → (∀ ψ : P''.A.left ⟶ P'.A.left, IsPolFibre g P' P'' ψ → IsPolFibre (g.comp f) P P'' (ψ ≫ φ)) ∧ (∀ χ : P''.A.left ⟶ P.A.left, IsPolFibre (g.comp f) P P'' χ → ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ) ∧ ∀ (ψ : P''.A.left ⟶ P'.A.left) (v : epsR R ⟶ P.A) (v' : epsR R' ⟶ P'.A) (v'' : epsR R'' ⟶ P''.A), ψ ≫ P'.A.hom = P''.A.hom ≫ spMap g → IsVecOver f φ v v' → (IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'') :=
  ⟨fun _ _ P v => ⟨PolFibre.refl P, PolFibre.vec_refl v⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun _ h' => PolFibre.comp h h', fun _ h' => PolFibre.cancel h h',
      fun _ _ _ _ w hv => PolFibre.vec_iff h.2.1.1 w hv⟩⟩

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomUnique

theorem hom_ext_of_lieBasis : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P Q : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (f f' : P.A ⟶ Q.A), (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom f → IsMonHom f' → v ≫ f = v ≫ f' → f = f' := by
  intro hU hB k _ s P Q v f f' hv hf hf' h
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB s P
  obtain ⟨Q', ψ, hQ⟩ := exists_isPolFibre hB s Q
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hP.2.1.1 v
  obtain ⟨g, hg, eg⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f
  obtain ⟨g', hg', eg'⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f'
  have hb := hv ℂ s P' φ v' hP hv'
  have e₁ : v' ≫ g = v' ≫ g' := by
    refine Over.OverMorphism.ext (hQ.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have hl : v.left ≫ f.left = v.left ≫ f'.left := congrArg (fun z => z.left) h
    unfold IsVecOver at hv'
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, eg, eg', ← Category.assoc, ← Category.assoc,
      hv', Category.assoc, Category.assoc, hl]
  have e₂ : g = g' := by
    refine (HomDescent.pol_countable_and_tangent_ext hU P' Q').2 g g' hg hg' fun x hx => ?_
    obtain ⟨c, hc, -⟩ := hb.2 x hx
    have ec : c = ![c 0] := by
      ext i
      fin_cases i
      rfl
    rw [ec, LieMultiple.isLieComb_one_iff_comp] at hc
    rw [hc, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e₁
  have := P.isAb.smooth
  have := Q.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap s) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom s) s.injective
  exact ExtUnique.over_hom_ext_of_isPullback hP.2.1.1 (by rw [← eg, ← eg', e₂])

end GlobalTheory.HomUnique
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TorsionGenerators

variable {R : Type} [CommRing R]

theorem exists_fibre (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [CommRing k] (t : R →+* k) :
    ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left)
      (β : (𝟙_ (Over (Sp k)) ⟶ P'.A) ≃* (Over.mk (spMap t) ⟶ P.A)), IsPolFibre t P P' φ ∧
      (∀ x, (β x).left = x.left ≫ φ) ∧ ∀ (n : ℤ) x y (c : Γ(Sp k, ⊤)ˣ),
        Out.WeilIs P'.A P'.L n x y c → Out.WeilIs P.A P.L n (β x) (β y) c := by
  obtain ⟨P', φ, h⟩ := exists_isPolFibre hL.polBaseChange t P
  obtain ⟨β, hβ⟩ := UnifPoint.exists_pointEquiv h.2.1
  refine ⟨P', φ, β, h, hβ, fun n x y c H => ?_⟩
  have H' := (weilIs_grpPullback_of_comm _ _ P.A P'.A _ φ P.L P'.L P.isLB P'.isLB h.2.1 (LBIso.symm h.2.2) _ n x y
    (pushPt h.2.1.1.w x) (pushPt h.2.1.1.w y) c rfl rfl).1 H
  exact UnifPoint.weilIs_congr (Category.id_comp _) (hβ x).symm (hβ y).symm H'

theorem exists_weilIs (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [Field k]
    (t : R →+* k) {n : ℕ} {x y : Over.mk (spMap t) ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ u : kˣ, Out.WeilIs P.A P.L n x y (unitOn u) := by
  obtain ⟨P', φ, β, h, -, H⟩ := exists_fibre hL P t
  obtain ⟨x, rfl⟩ := β.surjective x
  obtain ⟨y, rfl⟩ := β.surjective y
  rw [← map_pow, MulEquiv.map_eq_one_iff] at hx hy
  obtain ⟨c, hc, -⟩ := (hL.weil _ P' n _).1 x y hx hy
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c, ?_⟩
  have e : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c) = c :=
    Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c.val)
  rw [e]
  exact H n x y c hc

theorem unitOn_injective {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun a b h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

section Ext

variable {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

def extPt (e : β.comp t = t') : Over.mk (spMap t') ⟶ Over.mk (spMap t) :=
  Over.homMk (spMap β) ((spMap_comp_spMap _ _).trans (congrArg spMap e))

theorem extPt_injective (e : β.comp t = t') {A : Over (Sp R)} {x y : Over.mk (spMap t) ⟶ A}
    (h : extPt e ≫ x = extPt e ≫ y) : x = y := by
  have : Epi (extPt e).left := TorsionSeparable.epi_specMap β
  have : Epi (extPt e) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

theorem weilIs_extPt (hL : Out.Laws) (P : Out.PolAV (Sp R)) (e : β.comp t = t') {n : ℤ}
    {x y : Over.mk (spMap t) ⟶ P.A} {u : Kˣ} (H : Out.WeilIs P.A P.L n x y (unitOn u)) :
    Out.WeilIs P.A P.L n (extPt e ≫ x) (extPt e ≫ y) (unitOn (Units.map β.toMonoidHom u)) := by
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (extPt e) H
  have e' : Units.map (extPt e).left.appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map β.toMonoidHom u) :=
    Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rwa [e'] at H'

end Ext

section System

variable {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (a : OAct O P.A) (tr : O → ℤ)

variable {P a tr} {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

theorem extPt_eq_one_iff (e : β.comp t = t') {x : Over.mk (spMap t) ⟶ P.A} : extPt e ≫ x = 1 ↔ x = 1 :=
  ⟨fun h => extPt_injective e (h.trans (comp_one _).symm), fun h => by rw [h, comp_one]⟩

theorem unitsMap_injective (β : K →+* k) : Function.Injective (Units.map β.toMonoidHom) :=
  Units.map_injective β.injective

end System

theorem exists_finite_coordinates {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : X ⟶ Sp R) [LocallyOfFiniteType p]
    (t : R →+* Ω) (x : Sp Ω ⟶ X) (hx : x ≫ p = spMap t) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (B : Type) [CommRing B] (io : B →+* Ω), Function.Injective io → (∀ c, t c ∈ io.range) →
      (∀ y ∈ s, y ∈ io.range) → ∃ b : Sp B ⟶ X, spMap io ≫ b = x := by
  obtain ⟨A, i, _, q, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i)
      (t : Spec A), i t = x (IsLocalRing.closedPoint Ω) := by
    obtain ⟨n, t, ht⟩ := X.affineCover.exists_eq (x (IsLocalRing.closedPoint Ω))
    exact ⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨q, ht.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i x hr)
  have hφa : Spec.map φ ≫ i = x := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i ≫ p)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom t := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, hx]
  let : Algebra R A := ψ.hom.toAlgebra
  have : Algebra.FiniteType R A := h₂
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  refine ⟨φ.hom '' (s : Set A), s.finite_toSet.image _, fun B _ io hio h1 h2 => ?_⟩
  have hmem : ∀ y, φ.hom y ∈ io.range := by
    intro y
    have hy : y ∈ Algebra.adjoin R (s : Set A) := by simp [hs]
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact h2 _ ⟨y, hy, rfl⟩
    | algebraMap c => exact (congr($hc c) : φ.hom (algebraMap R A c) = t c) ▸ h1 c
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let e : B ≃+* io.range := RingEquiv.ofBijective io.rangeRestrict
    ⟨fun a b h => hio (congrArg Subtype.val h), io.rangeRestrict_surjective⟩
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict io.range hmem))) ≫ i, ?_⟩
  rw [← hφa, ← Spec.map_comp_assoc]
  congr 2
  ext y
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom y, hmem y⟩)

end GlobalTheory.TorsionGenerators

namespace GlobalTheory

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory

namespace CMData

variable {K : Type} [Field K] [NumberField K]

theorem exists_periodPair (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I.1, z = σ x := by
  obtain ⟨b, hspan⟩ : ∃ b : Module.Basis (Fin 2) ℚ K, ∀ x : K, x ∈ I.1 ↔ x ∈ Submodule.span ℤ (Set.range b) := by
    have hcard := (Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)).symm.trans h2
    refine ⟨(basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq hcard), fun x => ?_⟩
    rw [Module.Basis.coe_reindex, EquivLike.range_comp, mem_span_basisOfFractionalIdeal]
    exact Iff.rfl
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hX : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im ≠ 0 := by
    intro h0
    have e := CMLattice.im_mul_conj_eq_det σ b ![1, (a : K)]
    rw [h0, mul_zero] at e
    apply ha
    simpa using e
  have e2 : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im =
      (σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hind : LinearIndependent ℝ ![σ (b 0), σ (b 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have e1 := congrArg (fun w => (starRingEnd ℂ (σ (b 0)) * w).im) hst
      simp only [Complex.real_smul, mul_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero,
        Complex.zero_im] at e1
      have hprod : t * ((σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im) = 0 := by
        linear_combination -e1
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd (e2.trans h) hX
    subst ht
    have h0 : σ (b 0) ≠ 0 := by
      intro h
      apply hX
      rw [h, zero_mul, Complex.zero_im]
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right h0, rfl⟩
  refine ⟨⟨σ (b 0), σ (b 1), hind⟩, fun z => ?_⟩
  show z ∈ Submodule.span ℤ {σ (b 0), σ (b 1)} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • b 0 + n • b 1, ?_, by simp⟩
    rw [hspan]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rintro ⟨x, hx, rfl⟩
    rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two]

theorem exists_mul_of_invariants {L L' : PeriodPair} {c₄ Δ : ℂ}
    (h : c₄ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3 * Δ)
    (h₄ : c₄ = 12 * L'.g₂) (hΔ : Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w := by
  subst h₄ hΔ
  exact (lattice_determined_by_invariants L L').2 (by linear_combination (-1 / 1728 : ℂ) * h)

theorem exists_field (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
        ∀ L' : PeriodPair,
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.c₄ = 12 * L'.g₂ →
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 →
          ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ I.1, z = c * σ x := by
  obtain ⟨M, hfin, hσM, hF⟩ := exists_field_cm_curves_unit_discriminant K h2 σ hσ
  refine ⟨M, hfin, hσM, fun I => ?_⟩
  obtain ⟨L, hL⟩ := exists_periodPair h2 σ hσ I
  have hstab : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice := by
    intro a z hz
    obtain ⟨x, hx, rfl⟩ := (hL z).1 hz
    refine (hL _).2 ⟨(a : K) * x, ?_, by rw [map_mul]⟩
    have hax := Submodule.smul_mem (I.1 : Submodule (𝓞 K) K) a hx
    simpa [Algebra.smul_def] using hax
  obtain ⟨W, hW, hj⟩ := hF L hstab
  refine ⟨W, hW, fun L' h4 hD => ?_⟩
  obtain ⟨c, hc, hc'⟩ := exists_mul_of_invariants hj h4 hD
  refine ⟨c, hc, fun z => ?_⟩
  rw [hc' z]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hL w).1 hw
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ x, (hL _).2 ⟨x, hx, rfl⟩, rfl⟩

theorem mem_inv_iff (𝔟 : (Ideal (𝓞 K))⁰) (x : K) :
    x ∈ ((FractionalIdeal.mk0 K 𝔟)⁻¹).1 ↔ ∀ b ∈ (𝔟 : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K)) := by
  have hne : ((FractionalIdeal.mk0 K 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.mem_inv_iff hne, FractionalIdeal.coe_mk0]
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
    have hint : IsIntegral ℤ (algebraMap (𝓞 K) K a) := RingOfIntegers.isIntegral_coe a
    rw [ha] at hint
    exact hint
  · intro h y hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, h b hb⟩, rfl⟩

end CMData


open CMData in
theorem exists_cm_curves_of_weierstrass_curves :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞 K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
  intro H K _ _ h2 σ₀ hσ₀ 𝔟
  obtain ⟨M, hfin, hσM, hF⟩ := CMData.exists_field h2 σ₀ hσ₀
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨W₀, hW₀, hF₀⟩ := hF 1
  obtain ⟨P, v, L₀, hP, hP₀⟩ := H (𝓞 M) W₀ hW₀
  obtain ⟨c₀, hc₀, hc₀L⟩ := hF₀ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hP₀ _).1 (hP₀ _).2.2
  have hL0 : ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔
      ∃ a : 𝓞 K, z = c₀ * σ₀ (a : K) := by
    intro z
    rw [hc₀L z, Units.val_one]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩, rfl⟩
  choose W hW hWL using fun C : ClassGroup (𝓞 K) => hF (FractionalIdeal.mk0 K (𝔟 C))⁻¹
  choose Q t L hQ hQL using fun C => H (𝓞 M) (W C) (hW C)
  choose c hc hcL using fun C => hWL C (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hQL C _).1 (hQL C _).2.2
  refine ⟨M, hNF, σ₀.codRestrict M hσM, P, v, L₀, Q, t, L, fun C => (hW C).unit, fun a => rfl, hP, hQ,
    fun C s => ?_, ⟨c₀, hc₀, hL0⟩, fun C => c C / c₀, fun C => div_ne_zero (hc C) hc₀, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact ((hQL C s).2.2).symm
  · intro C x hx z hz
    obtain ⟨a, rfl⟩ := (hL0 z).1 hz
    have hxI := (CMData.mem_inv_iff (𝔟 C) x).2 hx
    rw [hcL C]
    refine ⟨x * (a : K), ?_, ?_⟩
    · have hax := Submodule.smul_mem (((FractionalIdeal.mk0 K (𝔟 C))⁻¹).1 : Submodule (𝓞 K) K) a hxI
      simpa [Algebra.smul_def, mul_comm] using hax
    · rw [map_mul]
      field_simp
  · intro C y hy z hz
    obtain ⟨x', hx', rfl⟩ := (hcL C z).1 hz
    have hint := (CMData.mem_inv_iff (𝔟 C) x').1 hx' y hy
    rw [hL0]
    refine ⟨⟨x' * (y : K), hint⟩, ?_⟩
    show _ = c₀ * σ₀ (x' * (y : K))
    have hcC := hc C
    rw [map_mul]
    field_simp

end GlobalTheory
end
