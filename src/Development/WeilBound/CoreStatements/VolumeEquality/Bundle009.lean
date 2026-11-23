module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle063
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

noncomputable section

namespace SheetDecomposition.Cj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped CategoryTheory.Obj ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  by
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext <;> simp [dualMap]

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  apply TrivSqZeroExt.ext <;> simp [dualMap]

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem cj_cj (z : Sp ℂ ⟶ X) : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
  rw [← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

theorem eps_sq : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
      CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
    CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
  have h3 := congrArg Spec.map h2
  simpa only [Spec.map_comp] using h3

def cjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, eps_sq, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (cjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := (show ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧ w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left from hw)
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (cjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem isTangent_of_fibre {A : Over (Sp ℂ)} [GrpObj A] {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) : IsTangent v' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm
    refine Eq.trans hv ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem fibreLatVec_conj {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) (R R' : RiemLat E g Λ) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) (hP : ∀ x, R'.P x = star (R.P x))
    (hH : R'.Hm = R.Hm.map (starRingEnd ℂ)) (hB : ∀ a x, R'.B a x = star (R.B a (star x)))
    (htan : ∀ a, IsTanAt t.G z (v a)) (hF : FibreLatVec t z R x v) :
    FibreLatVec t (spMap (starRingEnd ℂ) ≫ z) R' (fun a => star (x a)) (fun a => cjVec z (v a)) := by
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
  refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
    GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
    fun p => ?_, fun i => ?_⟩
  · rw [hH]
    exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
  · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
      (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left
    rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
      ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
    simp only [Category.assoc]
  · intro x y e
    rw [hP, hP] at e
    exact hinj (star_injective e)
  · show star p ∈ u.Λ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hP, hx, star_star]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [hP, star_star]⟩
  · obtain ⟨v', e, hd⟩ := hvec i
    have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
      rw [Category.assoc, Over.w]
      exact eps_sq
    let t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A :=
      Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
    have e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := h.1.lift_fst _ _ _
    refine ⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩
    rw [← Category.assoc, e', Category.assoc, e]
    rfl

theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) {gm : Λ ≃ₗ[𝓞 E] Λ} (h : R₁.EqvBy R₂ gm) : R₁'.EqvBy R₂' gm := by
  obtain ⟨k, hk⟩ := h
  refine ⟨{ toFun := fun x => star (k (star x))
            invFun := fun x => star (k.symm (star x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by simp
            left_inv := fun x => by simp
            right_inv := fun x => by simp }, fun x => ?_⟩
  show R₂'.P (gm x) = star (k (star (R₁'.P x)))
  rw [h₁, h₂, hk, star_star]

theorem autGrp_neg (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : autGrp (E := E) (-f) = autGrp f := by
  ext gm
  show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y
  simp

theorem star_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ}
    (ht : t ∈ ballDom q) : star t ∈ ballDom q := by
  intro τ
  have e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    simp [ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]
  rw [e]
  exact (ht τ).transpose

theorem preimage_star_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    star ⁻¹' ballDom q = ballDom q := by
  ext t
  constructor
  · intro h
    have h' := star_mem_ballDom (q := q) (t := star t) h
    rwa [star_star] at h'
  · intro h
    exact star_mem_ballDom (q := q) (t := t) h

theorem analyticAt_star_star {n : ℕ} {f : (Fin n → ℂ) → Fin g → ℂ} {t₀ : Fin n → ℂ} (h : AnalyticAt ℂ f (star t₀)) :
    AnalyticAt ℂ (fun t => star (f (star t))) t₀ := by
  have h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1
  have := (show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

end SheetDecomposition.Cj
end
end

section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas PositivityTheory.EqVol

namespace Moeb

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem sgI_sq : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

def sinv (u : Matrix (Sg j j') (Sg j j') ℂ) : Matrix (Sg j j') (Sg j j') ℂ := sgI j j' * uᴴ * sgI j j'

theorem sinv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : sinv u * u = 1 := by
  unfold IsSgU at h
  rw [sinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, sgI_sq]

theorem mul_sinv {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : u * sinv u = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_su {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : IsSgU (sinv u) := by
  have h1 := mul_sinv h
  unfold IsSgU at h ⊢
  conv_lhs => rw [← h]
  have : (sinv u)ᴴ * (uᴴ * sgI j j' * u) * sinv u = (u * sinv u)ᴴ * sgI j j' * (u * sinv u) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h1]
  simp

theorem moeb_one (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : moebBall q (fun _ => 1) t = t := by
  funext k
  have : ∀ W : Matrix (Fin j') (Fin j) ℂ, moebW (1 : Matrix (Sg j j') (Sg j j') ℂ) W = W := fun W => by
    rw [moebW, ← fromBlocks_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  simp [moebBall, ballPt, this, ballMat, Function.swap]

theorem moeb_maps (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {t : Fin n → ℂ} (ht : t ∈ ballDom q) : moebBall q u t ∈ ballDom q :=
  (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu).2.1 ht

theorem moeb_mul (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v w : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = w τ) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = moebBall q w t := by
  rw [← GlobalTheory.T.ball_mobius_mul Ψ j j' n q u v hu hv t ht, funext hw]

theorem moeb_inv (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = 1) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = t :=
  (moeb_mul q hu hv hw ht).trans (moeb_one q t)

theorem moeb_injOn (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ)) :
    Set.InjOn (moebBall q u) (ballDom q) := fun t ht t' ht' h => by
  rw [← moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht, h,
    moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht']

theorem moeb_meas (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    MeasurableSet (moebBall q u '' S) ∧ ballMeas q (moebBall q u '' S) = ballMeas q S := by
  obtain ⟨h1, h2, G, h3, h4⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu
  exact ⟨hS.image_of_continuousOn_injOn (h1.continuousOn.mono hSD) ((moeb_injOn q hu).mono hSD),
    ballMeas_image q h1 h2 (moeb_injOn q hu) (fun t ht => ballDens_transform q h1 h3 h2 h4 ht) hS hSD⟩

def ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (q'.symm.trans q)

theorem ren_apply (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (x : Ψ × Fin j × Fin j') :
    ren q q' t (q x) = t (q' x) := by
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (q'.symm.trans q) t (q' x)
  simpa [ren] using this

theorem ballMat_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballMat q (ren q q' t) = ballMat q' t := by
  funext τ
  ext a b
  simp [ballMat, ren_apply]

theorem ren_mem (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ren q q' t ∈ ballDom q ↔ t ∈ ballDom q' := by
  simp only [ballDom, Set.mem_setOf_eq, ballMat_ren]

theorem moeb_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) :
    moebBall q u (ren q q' t) = ren q q' (moebBall q' u t) := by
  funext k
  obtain ⟨x, rfl⟩ := q.surjective k
  rw [ren_apply]
  simp [moebBall, ballPt, ballMat_ren]

theorem ren_meas (q q' : Ψ × Fin j × Fin j' ≃ Fin n) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q') :
    ballMeas q (ren q q' '' S) = ballMeas q' S := by
  have hm : MeasurePreserving (ren q q') volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℂ) _
  rw [ballMeas_apply q ((ren q q').measurableSet_image.2 hS) (by rintro _ ⟨t, ht, rfl⟩; exact (ren_mem q q' t).2 (hSD ht)),
    ballMeas_apply q' hS hSD, ← hm.setLIntegral_comp_emb (ren q q').measurableEmbedding]
  simp only [ballDens, ballPot, ballMat_ren]

theorem core (q : Ψ × Fin j × Fin j' ≃ Fin n) {G : Type} [Group G] [Countable G]
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (S S' : Set (Fin n → ℂ)) (h1 : ∀ τ, ρ 1 τ = 1)
    (hm : ∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) (hU : ∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) (hΓ : Γ ≤ U) (hΓ' : Γ' ≤ U)
    (hI : EqIdx Γ Γ') (hS : MFund q ρ Γ S) (hS' : MFund q ρ Γ' S') : ballMeas q S = ballMeas q S' := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : ballDom q → Fin n → ℂ) := MeasurableEmbedding.subtype_coe hD
  letI act : MulAction U (ballDom q) :=
    { smul := fun γ t => ⟨moebBall q (ρ γ) t, moeb_maps q (hU γ γ.2) t.2⟩
      one_smul := fun t => Subtype.ext (by
        show moebBall q (ρ 1) t = t
        rw [funext h1, moeb_one])
      mul_smul := fun a b t => Subtype.ext
        (moeb_mul q (hU a a.2) (hU b b.2) (fun τ => (hm a b τ).symm) t.2).symm }
  have sm : ∀ (γ : U) (t : ballDom q), ((γ • t : ballDom q) : Fin n → ℂ) = moebBall q (ρ γ) t := fun _ _ => rfl
  haveI : MeasurableConstSMul U (ballDom q) := ⟨fun γ =>
    (Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1
      (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q (ρ γ) (hU γ γ.2)).1.continuousOn) _).measurable⟩
  let μ : Measure (ballDom q) := (ballMeas q).comap Subtype.val
  have hμ : ∀ s, μ s = ballMeas q (Subtype.val '' s) := fun s => hemb.comap_apply _ s
  haveI : SMulInvariantMeasure U (ballDom q) μ := ⟨fun γ s hs => by
    rw [hμ, hμ, ← (moeb_meas q (hU _ (γ⁻¹).2) (hemb.measurableSet_image.2 hs) (Subtype.coe_image_subset _ _)).2]
    congr 1
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨γ • x, hx, rfl⟩, by rw [← sm, inv_smul_smul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨γ⁻¹ • x, by simpa using hx, rfl⟩⟩
  have fd : ∀ (Γ : Subgroup G) (S : Set (Fin n → ℂ)), Γ ≤ U → MFund q ρ Γ S →
      IsFundamentalDomain (Γ.subgroupOf U) (Subtype.val ⁻¹' S : Set (ballDom q)) μ ∧
        μ (Subtype.val ⁻¹' S) = ballMeas q S := fun Γ S hΓ ⟨a1, a2, a3, a4⟩ => by
    refine ⟨IsFundamentalDomain.mk' (hemb.measurable a1).nullMeasurableSet fun x => ?_, ?_⟩
    · obtain ⟨γ, hγ, h⟩ := a3 x x.2
      refine ⟨⟨⟨γ, hΓ hγ⟩, hγ⟩, h, fun g hg => ?_⟩
      have e : (g.1 * (⟨γ, hΓ hγ⟩ : U)⁻¹) • ((⟨γ, hΓ hγ⟩ : U) • x) = g.1 • x := by
        rw [← mul_smul, inv_mul_cancel_right]
      have := a4 _ h (g.1.1 * γ⁻¹) (Γ.mul_mem g.2 (Γ.inv_mem hγ)) (by
        have e' := congrArg Subtype.val e
        rw [sm, sm, sm] at e'
        exact e' ▸ hg)
      exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
    · rw [hμ, Subtype.image_preimage_coe, Set.inter_eq_right.2 a2]
  obtain ⟨a₁, b₁⟩ := fd Γ S hΓ hS
  obtain ⟨a₂, b₂⟩ := fd Γ' S' hΓ' hS'
  rw [← b₁, ← b₂]
  exact fdEqual _ _ μ _ _ _ _
    (by rw [Subgroup.relIndex_subgroupOf hΓ, Subgroup.relIndex_subgroupOf hΓ']; exact hI.1)
    (by rw [Subgroup.relIndex_subgroupOf hΓ']; exact hI.2) a₁ a₂

end Moeb

open Moeb

theorem moebVol : MoebVol := by
  intro Ψ _ j j' n q q' G _ _ ρ ρ' w U Γ Γ' a S S' h1 hm hU hU' hw hc hΓ hΓ' hI hS ⟨b1, b2, b3, b4⟩
  have r1 : MeasurableSet (ren q q' '' S') := (ren q q').measurableSet_image.2 b1
  have r2 : ren q q' '' S' ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact (ren_mem q q' t).2 (b2 ht)
  obtain ⟨m1, m2⟩ := moeb_meas q hw r1 r2
  have key : ∀ γ ∈ Γ', ∀ t ∈ ballDom q', moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) =
      moebBall q w (ren q q' (moebBall q' (ρ' γ) t)) := fun γ hγ t ht => by
    have ht' := (ren_mem q q' t).2 ht
    rw [← moeb_ren, moeb_mul q (hU (a * γ * a⁻¹) (hΓ' ⟨γ, hγ, rfl⟩)) hw (fun _ => rfl) ht',
      moeb_mul q hw (hU' γ hγ) (hc γ) ht']
  rw [← ren_meas q q' b1 b2, ← m2]
  refine core q ρ U Γ _ S _ h1 hm hU hΓ hΓ' hI hS ⟨m1, ?_, fun t ht => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact moeb_maps q hw (r2 ht)
  · have hi := fun τ => sinv_su (hw τ)
    obtain ⟨s, hs⟩ := (ren q q').surjective (moebBall q (fun τ => sinv (w τ)) t)
    have hs' : s ∈ ballDom q' := (ren_mem q q' s).1 (hs ▸ moeb_maps q hi ht)
    obtain ⟨γ, hγ, h⟩ := b3 s hs'
    refine ⟨a * γ * a⁻¹, ⟨γ, hγ, rfl⟩, _, ⟨_, h, rfl⟩, ?_⟩
    rw [← key γ hγ s hs', hs, moeb_inv q hw hi (fun τ => mul_sinv (hw τ)) ht]
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨γ, hγ, rfl⟩ ⟨_, ⟨s, hs, rfl⟩, e⟩
    replace e : moebBall q w (ren q q' s) = moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) := e
    rw [key γ hγ t (b2 ht)] at e
    have e2 := (ren q q').injective (moeb_injOn q hw ((ren_mem q q' _).2 (b2 hs))
      ((ren_mem q q' _).2 (moeb_maps q' (hU' γ hγ) (b2 ht))) e)
    obtain rfl := b4 t ht γ hγ (e2 ▸ hs)
    exact map_one _

end SheetDecomposition
end
end
