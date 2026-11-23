module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PointAlg

section Points

variable {S S' X : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem prod_left (h : IsGrpPullback G' G f φ) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t) {n : ℕ}
    (x' : Fin n → (Over.mk t' ⟶ G')) (x : Fin n → (Over.mk t ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (x i).left) :
    (List.ofFn x').prod.left ≫ φ = (List.ofFn x).prod.left := by
  subst e
  have h1 := map_list_prod (pushHom h (Over.mk t')) (List.ofFn x')
  rw [List.map_ofFn] at h1
  have h2 : (pushHom h (Over.mk t')) ∘ x' = x := funext fun i => Over.OverMorphism.ext (hx i)
  rw [h2] at h1
  exact congrArg (fun z => z.left) h1


omit [GrpObj G] [GrpObj G'] in
theorem exists_lift_pt (h : IsPullback φ G'.hom G.hom f) {t' : X ⟶ S'} (x : X ⟶ G.left) (e : x ≫ G.hom = t' ≫ f) :
    ∃ x' : Over.mk t' ⟶ G', x'.left ≫ φ = x :=
  ⟨Over.homMk (h.lift x t' e) (h.lift_snd _ _ _), h.lift_fst _ _ _⟩


omit [GrpObj G] [GrpObj G'] in
theorem pt_ext (h : IsPullback φ G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

theorem exists_lift_hom {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G f φ) (hH : IsGrpPullback H' H f ψ) (w : G ⟶ H) [IsMonHom w] :
    ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hG (isGrpPullback_pullback G f)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H f) hH
  refine ⟨a.hom ≫ (Over.pullback f).map w ≫ b.hom, inferInstance, ?_⟩
  have e : ((Over.pullback f).map w).left ≫ pullback.fst H.hom f = pullback.fst G.hom f ≫ w.left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', e, ← Category.assoc, ha']

theorem onto_lift {B : Over S} {B' : Over S'} {β : B'.left ⟶ B.left} (hB : IsPullback β B'.hom B.hom f)
    (hG : IsGrpPullback G' G f φ) {n : ℕ} (w : Fin n → (B ⟶ G)) (w' : Fin n → (B' ⟶ G'))
    (hw : ∀ i, (w' i).left ≫ φ = β ≫ (w i).left) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t)
    (h : ∀ y : Over.mk t ⟶ G, ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (y : Over.mk t' ⟶ G') : ∃ x : Fin n → (Over.mk t' ⟶ B'), y = (List.ofFn fun i => x i ≫ w' i).prod := by
  subst e
  obtain ⟨x, hx⟩ := h (pushPt hG.1.w y)
  choose x' hx' using fun i => exists_lift_pt hB (t' := t') (x i).left (Over.w (x i))
  refine ⟨x', pt_ext hG.1 ?_⟩
  rw [prod_left hG rfl _ (fun i => x i ≫ w i) fun i => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hw, ← Category.assoc, hx'], ← hx]
  rfl

end Points

theorem isAbelianScheme_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (Out.powObj G n)
  | 0 => by
    have := hG.comm
    have : IsIso (Out.powObj G 0).hom := inferInstanceAs (IsIso (𝟙 S))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstanceAs (GeometricallyConnected (𝟙 S))⟩
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj G hG n

theorem onto_of_onto {R : Type} [CommRing R] [IsDomain R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {n : ℕ}
    (w : Fin n → (B ⟶ A))
    (h : ∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Fin n → (Over.mk (spMap σ) ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (t : Sp ℂ ⟶ Sp R) (y : Over.mk t ⟶ A) :
    ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod := by
  have := hA.comm
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ Out.powObj B n),
      x ≫ (List.ofFn fun i => Out.powPr B i ≫ w i).prod = (List.ofFn fun i => (x ≫ Out.powPr B i) ≫ w i).prod := by
    intro T x
    have h1 := map_list_prod (preHom (G := A) x) (List.ofFn fun i => Out.powPr B i ≫ w i)
    rw [List.map_ofFn] at h1
    refine h1.trans ?_
    congr 2
  obtain ⟨x, hx⟩ := (OntoSurj.surjective_of_onto_complex_points R σ hσ A (Out.powObj B n)
    (List.ofFn fun i => Out.powPr B i ≫ w i).prod hA (isAbelianScheme_pow B hB n) fun y => by
      obtain ⟨x, hx⟩ := h y
      refine ⟨(Out.powIsLimit B n).lift (Fan.mk _ x), ?_⟩
      rw [key, hx]
      congr 2
      funext i
      exact congrArg (· ≫ w i) ((Out.powIsLimit B n).fac (Fan.mk _ x) ⟨i⟩).symm).2 ℂ t y
  exact ⟨fun i => x ≫ Out.powPr B i, by rw [hx, key]⟩

theorem map_sum_eq_prod {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    {n : ℕ} (z : Fin n → V) : e (∑ i, z i) = (List.ofFn fun i => e (z i)).prod := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    simpa using this.symm
  | succ n ih => rw [Fin.sum_univ_succ, he, ih, List.ofFn_succ, List.prod_cons]



theorem exists_numberField_point_of_cmLat : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  intro hC hPt hT hL E _ _ _ H D l Xo g ty FU i Pe hP p q ⟨Z⟩
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨ε, a, ha⟩ := exists_pure_vectors_periods_span E H _ g ty Pe hP p q Z
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull (spMap ρ.toRingHom ≫ y) Xo.univ.t
        exact ⟨_, ⟨m'⟩⟩
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end GlobalTheory.PointAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.cmCurveBaseChange_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  first | exact @GlobalTheory.CM.EllComp.ellMap_comp | exact GlobalTheory.CM.EllComp.ellMap_comp | (intros; apply GlobalTheory.CM.EllComp.ellMap_comp <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_kronecker_cmLogPeriod_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  first | exact @GlobalTheory.LamF.exists_kronecker_logOm_eq | exact GlobalTheory.LamF.exists_kronecker_logOm_eq | (intros; apply GlobalTheory.LamF.exists_kronecker_logOm_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_lieBasis_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  first | exact @GlobalTheory.LamT.exists_isLieBasis_locMod | exact GlobalTheory.LamT.exists_isLieBasis_locMod | (intros; apply GlobalTheory.LamT.exists_isLieBasis_locMod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.integral_eigenbasis_baseChange_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  first | exact @GlobalTheory.LamT.lieInt_baseChange | exact GlobalTheory.LamT.lieInt_baseChange | (intros; apply GlobalTheory.LamT.lieInt_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

theorem locMod_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  intro E _ _ _ H Dw l Xo c _ z T iK
  refine ⟨fun h => ?_, fun M T' ψ i hψ => ?_⟩
  · have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
    let ρ : 𝓞 z.K →+* T.V := e.symm.toRingHom.comp
      ((iK.comp (algebraMap (𝓞 z.K) z.K)).codRestrict (algebraMap T.V T.Fr).range fun a => h a)
    have hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K) := by
      ext a
      exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h a⟩)
    obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ρ z.B).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ iK z.Φ.T).1
    obtain ⟨m1, h1⟩ := sab_comp_exists n' z.Φ.m _ rfl
    obtain ⟨k, hk⟩ := sab_comp_exists n' z.m' _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T.V T.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hρ])
    exact ⟨⟨ρ, hρ, G, t', n, n', m1, m2, h1, h2.trans hk⟩⟩
  · obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ψ M.G).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ i M.t').1
    obtain ⟨N, hN⟩ := sab_comp_exists n M.n _ (spectrumMap_comp M.ρ ψ)
    obtain ⟨N', hN'⟩ := sab_comp_exists n' M.n' _ (spectrumMap_comp iK i)
    obtain ⟨m1, h1⟩ := sab_comp_exists n' M.m1 (spMap (i.comp iK) ≫ z.x)
      (by rw [spectrumMap_comp, Category.assoc])
    obtain ⟨k, hk⟩ := sab_comp_exists n' M.m2 _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T'.V T'.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hψ])
    refine ⟨⟨ψ.comp M.ρ, ?_, G, t', N, N', m1, m2, ?_, ?_⟩, n, n', h1, h2.trans hk⟩
    · rw [← RingHom.comp_assoc, hψ, RingHom.comp_assoc, M.hρ, RingHom.comp_assoc]
    · rw [h1, hN', M.h1, Category.assoc]
    · rw [hN, hN', ← Category.assoc, h2, hk, Category.assoc, M.h2, Category.assoc]

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
  obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
  obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
  have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
    Φ'.th hx hn.symm hs hw hθ).1 ht'
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
  have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
    rintro _ rfl
    exact hu
  have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
    fun i => huv _
  have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
  have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
      rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, Formalism.L2.Pj.dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
    fun a => ?_, ?_, hv⟩, fun i => ?_⟩
  · exact (hr _ n.base he).symm ▸ hw.2
  · refine Eq.trans ?_ (hm j i)
    have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
    rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Formalism.L2.Pj.dualMap]
  · rw [← hn, ← Category.assoc, hv, Category.assoc]

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_normalised_polarisation : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A →
    LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
    ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧
      LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  intro laws R _ _ P w w' hw hw' hs ha
  have : IsCommMonObj P.A := P.isAb.comm
  have hM := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := laws.cube _ P ⟨P.L, rig, hM, hrig⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have ha' : LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) := by
    simpa only [LamEq, Category.comp_id] using ha
  obtain ⟨Q, -, e, -, iso⟩ := exists_normalised_bundle laws.globalFns P.isAb hM hT w w' hs ha'
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hQ := Q.isLB
  have lam : LamEq Q.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) := iso _ _ _
  refine ⟨Q.L, hQ, ⟨Q.rig, Q.rigGen⟩, fun s => ⟨⊤, trivial, ?_⟩, ?_, kTriv_of_lamEq _ _ _ _ hM hQ lam P.ktriv, lam, ?_⟩
  · have h : HasGen Q.L (K := Fin 2) ![(GrpObj.inv (X := P.A)).left, 𝟙 _] ![1, -1] := by
      rw [e]
      refine hasGen_nested hM _ _ _ _ ?_
      rw [Fin.prod_univ_two]
      show normCls P.L w (GrpObj.inv (X := P.A)).left ^ (1 : ℤ) *
        normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ (-1 : ℤ) = 1
      have e : GrpObj.inv (X := P.A) = (𝟙 P.A)⁻¹ := by simp [Hom.inv_def]
      have e' : (𝟙 P.A)⁻¹ ≫ w = (𝟙 P.A ≫ w)⁻¹ := map_inv (postHom w P.A) _
      rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc P.A), zpow_neg, zpow_one, mul_inv_cancel]
    have h' := h.pull (P.A.hom ⁻¹ᵁ ⊤).ι
    have e₁ : (fun k => (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (![(GrpObj.inv (X := P.A)).left, 𝟙 _] : Fin 2 → _) k) =
        ![(P.A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      exacts [rfl, Category.comp_id _]
    rw [e₁] at h'
    exact h'
  · have one : ptCls P.L P.A 1 = 1 := by
      have h := (hasGen_iff hM _ _).1 (HasGen.pull (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1)
        ⟨rig, hrig⟩ (toUnit P.A).left)
      rw [Fintype.prod_unique, zpow_one] at h
      exact h
    have two : ptCls P.L P.A (𝟙 P.A * 𝟙 P.A) = ptCls P.L P.A (𝟙 P.A) ^ (4 : ℤ) := by
      have h := (hasGen_iff hM _ _).1 (laws.mulPull _ P 2)
      rw [Fin.prod_univ_two] at h
      have h' : ptCls P.L P.A (𝟙 P.A) ^ (((2 : ℕ) : ℤ) ^ 2) * ptCls P.L P.A (𝟙 P.A ^ 2) ^ (-1 : ℤ) = 1 := h
      rw [zpow_neg, zpow_one, mul_inv_eq_one, pow_two (𝟙 P.A)] at h'
      exact h'.symm
    have sq : LBIso (lbPow Q.L 2) (lbPow P.L 2) := by
      rw [e]
      refine lbIso_nested hM _ _ _ _ _ _ ?_
      refine (Fintype.prod_unique _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      show normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ ((2 : ℕ) : ℤ) = ptCls P.L P.A (𝟙 P.A) ^ ((2 : ℕ) : ℤ)
      rw [normCls_left, zpow_natCast, zpow_natCast, pow_two, Category.id_comp]
      have adj := diff₂_ptCls_adj hM ha' (𝟙 P.A) (𝟙 P.A)
      rw [Category.id_comp, Category.id_comp, diff₂_comm w] at adj
      nth_rewrite 2 [adj]
      rw [← diff₂_mul_right (hc P.A), hs, diff₂, one, two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_zpow, ofMul_pow]
      abel
    have A₁ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb hM
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₂ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) Q.L 2 two_pos P.isAb P.isAb hQ
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₃ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (DVR.linComb_isLB _ hM _ _) (show IsFinite (𝟙 P.A.left) from inferInstance)
    exact A₂.2.1.1 (A₃.2.2.2 _ (DVR.linComb_isLB _ hQ _ _) sq.symm (A₁.2.1.2 P.ample))
  · have := (iso P.A (𝟙 P.A) w).symm
    rwa [← e] at this

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.tensor_pairing_identity_of_pure_tensors : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  first | exact @GlobalTheory.LamCalc.lamEq_of_tmul | exact GlobalTheory.LamCalc.lamEq_of_tmul | (intros; apply GlobalTheory.LamCalc.lamEq_of_tmul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.eq_of_lamEq_polAV : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  first | exact @GlobalTheory.CM.PairingInj.eq_of_lamEq | exact GlobalTheory.CM.PairingInj.eq_of_lamEq | (intros; apply GlobalTheory.CM.PairingInj.eq_of_lamEq <;> assumption)
end
