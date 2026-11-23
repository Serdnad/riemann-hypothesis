module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle190
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesUnramifiedPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle110
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle188
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle108
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle114
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle117
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Calculus.FDeriv.Star
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.Chart

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

theorem ring_eq' {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem exists_chart_values : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hpN hc
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends X G Ω ξ E M p N J c hpN hc
  obtain ⟨_, ⟨A, hA, rfl⟩, hpA, hAx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hpx x.opensRange.isOpen
  replace hA : IsAffineOpen A := hA
  have hrange : Set.range hA.fromSpec ⊆ Set.range x := by
    rw [hA.range_fromSpec]
    exact hAx
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(X, A), spMap a ≫ x = hA.fromSpec :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x hA.fromSpec hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨EB, iEB, mEB, ⟨MB⟩⟩ := lieModel_exists X G Γ(X, A) hA.fromSpec
  have hex : ∀ i, ∃ b, MB.pt b = epsBase a ha ≫ MR.pt (e i) := fun i =>
    MB.onto _ (isTanAt_base a ha (MR.tan _))
  choose eB heB using hex
  refine ⟨A, hA, EB, iEB, mEB, MB, eB, hpA, fun t ht => hxN (hAx ht), ?_⟩
  intro y f hg hy i w hw
  let q : Cpt ξ := ⟨centre y, hg⟩
  have hqr : q.1 ∈ x.opensRange := by
    refine hrange ⟨spMap f (IsLocalRing.closedPoint ℂ), ?_⟩
    change _ = centre y
    simp only [centre, hy, Scheme.Hom.comp_apply]
    rfl
  have hqx : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo y).hom.comp ψ = f.comp a := by
    refine ring_eq' x y ψ hψ _ ?_
    have e2 : spMap (f.comp a) = spMap f ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, hy]
  let vq : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G := epsBase ψ hψ ≫ MR.pt (e i)
  refine ⟨hg, vq, hext q ψ hψ i vq rfl, ?_⟩
  rw [hw, heB]
  change spMap (dualMap f) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
    spMap (dualMap (Scheme.stalkClosedPointTo y).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
  rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]

end GlobalTheory.CompanionTheory.Ar.LocFrames.Chart
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GramConj

open GlobalTheory.ArchMetricCompare (cj cjPt cjUnif cj_isAH cj_val isIso_of_cj carry carry_isAH)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualConj_dualConj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 (Sp (DualNumber ℂ)) := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  exact Spec.map_id _

theorem fderiv_conj {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases h : DifferentiableAt ℂ F 0
  · have d := h.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have h' : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun h' => h (by
      have := h'.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := by
        ext z
        simp
      rw [star_zero, e] at this
      exact this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} {M : LB A.left} {M' : LB A'.left} {g : ℕ}

theorem isDiff_conj (h : IsGrpPullback A' A cj ψ) (u : HolUnif A M g) (u' : HolUnif A' M' g)
    (hex : ∀ z, u'.ex z = cjPt h (u.ex (star z))) {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    u'.IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have e4 : (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := by
    rw [e2, ← Category.assoc, dualConj_dualConj, Category.id_comp]
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun p _ => by
    have q : ((show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ) p ∈ U := by
      rw [e4]
      exact hU (show spMap (dualMap (starRingEnd ℂ)) p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    exact q
  have e1 : (fun z => valAt' (u'.ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => by
      simp only [hex]
      exact cj_val h _ U f
  rw [e1, fderiv_conj]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem exists_conjUnif (h : IsGrpPullback A' A cj ψ) (hM : M.IsLB) (u : HolUnif A M g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    ∃ (u' : HolUnif A' (M.pull ψ) g) (χ' : u'.Λ → ℂ), u'.IsAH (Hm.map star) χ' ∧
      ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
  have hM1 : (M.pull (𝟙 A.left)).IsLB := pull_isLB hM _
  obtain ⟨w, hw⟩ : LBIso M (M.pull (𝟙 A.left)) :=
    LBIso.chartPull (chartPullId M) (chartPullPull M (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hM)
  have key : ∀ f, f = ψ ≫ 𝟙 A.left → ∃ (u' : HolUnif A' (M.pull f) g) (χ' : u'.Λ → ℂ),
      u'.IsAH (Hm.map star) χ' ∧ ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
    rintro _ rfl
    exact ⟨cjUnif h (carry u hM hM1 hw), _, cj_isAH h _ (carry_isAH hM hM1 hw hA), fun _ => rfl⟩
  exact key _ (Category.comp_id _).symm

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  rintro S G _ L x x' n v v' Γ rfl hv' ⟨Q, ψ, vo, u, Hm, χ, W, hP, hLB, hAH, hvo, hΓ⟩
  have hc := isGrpPullback_pullback Q.A cj
  haveI := (Out.TLinPf.isAb_pullback cj Q.A Q.isAb).comm
  obtain ⟨u', χ', hAH', hex⟩ := exists_conjUnif hc Q.isLB u hAH
  have sq : ∀ i, (spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left) ≫ Q.A.hom = (epsR ℂ).hom ≫ cj := fun i => by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t : ∀ i, epsR ℂ ⟶ (Over.pullback cj).obj Q.A := fun i => Over.homMk (hc.1.lift _ _ (sq i)) (hc.1.lift_snd _ _ _)
  have et : ∀ i, (t i).left ≫ pullback.fst Q.A.hom cj = spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left :=
    fun i => hc.1.lift_fst _ _ _
  refine ⟨GlobalTheory.TorsionTauCompare.polOfPullback Q _ hc, pullback.fst Q.A.hom cj ≫ ψ, t, u', Hm.map star, χ',
    fun i => star (W i), hc.comp hP, ?_, hAH', fun i => ⟨?_, isDiff_conj hc u u' hex (et i) (hvo i).2⟩, fun i j => ?_⟩
  · exact LBIso.symm (Cusp.FibreMove.lbIso_pull (LBIso.symm hLB) _)
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ) (et i))).trans
      (((Category.assoc _ _ _).trans (congrArg _ (hvo i).1)).trans (hv' i).symm)
  · rw [Matrix.map_apply, hΓ, map_mul, Complex.conj_ofReal]
    congr 1
    refine Eq.trans ?_ (GlobalTheory.ArchMetricCompare.star_form Hm (star (W i)) (star (W j)))
    rw [star_star (W i), star_star (W j)]
    rfl

end GlobalTheory.CompanionTheory.Ar.GramConj
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.root_lines_unramified_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z) → Nonempty (DRTie M D.p p H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.inf_norm_conjugate_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_metric_hermitian_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X), ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lie_fibre_exists | exact GlobalTheory.CompanionTheory.Ar.lie_fibre_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.lie_fibre_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genV_res {N N' : X.Opens} (l : N' ≤ N) (h' : genPt ξ ∈ N') (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genV ξ N' h' (X.presheaf.map (homOfLE l).op v) = genV ξ N h v := by
  have e : X.presheaf.germ N' (genPt ξ) h' (X.presheaf.map (homOfLE l).op v) = X.presheaf.germ N (genPt ξ) h v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom e

theorem unitAt_genV {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) {v : Γ(X, N)}
    (hv : IsUnit v) : unitAt ξ ⟨q, hq⟩ (genV ξ N h v) := by
  obtain ⟨u, rfl⟩ := hv
  have e : genV ξ N h u * genV ξ N h (u⁻¹ : Γ(X, N)ˣ) = 1 := by rw [← map_mul]; simp
  refine ⟨left_ne_zero_of_mul_eq_one e, ⟨_, genMap_germ N hq hN h _⟩, ?_⟩
  rw [inv_eq_of_mul_eq_one_right e]
  exact ⟨_, genMap_germ N hq hN h _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem gaga_rat_C : GagaSections → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] [Algebra ℂ Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap ℂ Ω) → IsCptGen ξ → ConstClosed ℂ Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap (RingHom.id ℂ) → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s (RingHom.id ℂ) ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap (RingHom.id ℂ) → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  have dens := GlobalTheory.T.smooth_algebra_eq_zero_of_vanish_open
  have chart := GlobalTheory.T.analytic_chart_vanishing_section
  have unit := GlobalTheory.T.is_unit_of_nonvanishing_points
  have trans := GlobalTheory.T.line_bundle_from_unit_ratios
  have hch := GlobalTheory.T.analytic_chart_unit_section
  have cmp := GlobalTheory.T.overlapping_analytic_charts_ratio
  intro hG X s Ω _ _ ξ L W F hp hs hξs hgen hcl hVB hW h1 hext
  haveI : Smooth s := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, hZc, -⟩ := cpt_open_integral X Ω ξ hgen
  have spid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp
  choose Uo hUo b hb hfr using fun p : Cpt ξ => hVB p trivial
  let Uc : Cpt ξ → X.Opens := fun p => Uo p ⊓ Z
  let T : Cpt ξ → Ω := fun p => b p 0
  have inZ : ∀ p q, q ∈ Uc p → genPt ξ ⤳ q := fun p q hq => (hZ q).1 hq.2
  have memU : ∀ p : Cpt ξ, p.1 ∈ Uc p := fun p => ⟨hUo p, (hZ _).2 p.2⟩
  have gen : ∀ (p q : Cpt ξ), q.1 ∈ Uc p → L.IsGenAt q (T p) := fun p q hq => by
    obtain ⟨li, sp⟩ := hfr p q trivial hq.1
    refine ⟨li.ne_zero 0, ?_⟩
    rw [sp]
    congr 1
    ext e
    simp [T, Fin.exists_fin_one, eq_comm]
  have hunitW : ∀ (p : Cpt ξ) (q : X) (hq : genPt ξ ⤳ q), q ∈ Uc p → q ∈ W → unitAt ξ ⟨q, hq⟩ (T p) := fun p q hq a c => by
    have := unitAt_div_of_isGenAt (h1 ⟨q, hq⟩ c) (gen p ⟨q, hq⟩ a)
    simpa using this
  let V : Option (Cpt ξ) → X.Opens := fun o => o.elim ⟨(Z : Set X)ᶜ, hZc.isOpen_compl⟩ Uc
  have hV1 : ∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q := fun i q hq => inZ i q hq
  have hV2 : ∀ q ∈ V none, ¬ genPt ξ ⤳ q := fun q hq h => hq ((hZ q).2 h)
  have hV3 : ∀ (i j : Cpt ξ) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) →
      unitAt ξ ⟨q, hq⟩ (T j / T i) := fun i j q hq a c =>
    unitAt_div_of_isGenAt (gen i ⟨q, hq⟩ a) (gen j ⟨q, hq⟩ c)
  have hV4 : ⨆ i, V i = ⊤ := by
    refine top_le_iff.1 fun q _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : q ∈ Z
    · exact ⟨some ⟨q, (hZ q).1 h⟩, memU ⟨q, (hZ q).1 h⟩⟩
    · exact ⟨none, h⟩
  obtain ⟨g, hLB, hg⟩ := trans X Ω ξ (Cpt ξ) V T hgen hV1 hV2 hV3 hV4
  let Rel : Cpt ξ → (Sp ℂ ⟶ X) → ℂ → Prop := fun p x c => ∃ (d : ℕ) (B : Set (Fin d → ℂ))
    (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (b₁ : Fin d → ℂ),
    HChart s ξ W (Uc p) F (T p) B Y H ∧ b₁ ∈ B ∧ Y b₁ = x ∧ H b₁ = c
  have relEx : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → centre x ∈ Uc p → ∃ c, Rel p x c := by
    intro p x hx hm
    have hc : genPt ξ ⤳ centre x := inZ p _ hm
    obtain ⟨t, ht, he⟩ := hext x hc (by rw [hx, spid])
    have u := unitAt_div_of_isGenAt (gen p ⟨centre x, hc⟩ hm) ht
    obtain ⟨N, hN, v, lN, uv, ev⟩ := exists_unit_section hgen hc u (Uc p) hm
    obtain ⟨d, B, Y, b₁, hC, hb₁, e₁, hin, hd⟩ := chart dens X s Ω ξ W N x hs hgen hW hx hc hN
    have gm : ∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N),
        genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T p := fun q hq h => by
      rw [GagaC.genMap_germ N hq h (genPt_mem hc hN), ← GagaC.genMap_germ N hc hN (genPt_mem hc hN), ev]
    subst e₁
    obtain ⟨B₂, H, m₂, hH⟩ := hch X s Ω ξ W (Uc p) N F (T p) t v d B Y b₁ hgen hC hb₁ hin lN hd uv gm
      (gen p p (memU p)).1 he
    exact ⟨_, d, B₂, Y, H, b₁, hH, m₂, rfl, rfl⟩
  have relCmp : ∀ (p p' : Cpt ξ) (x : Sp ℂ ⟶ X) (c c' r : ℂ), Rel p x c → Rel p' x c' →
      ValAt ξ x (T p' / T p) r → c = r * c' := by
    rintro p p' x c c' r ⟨d, B, Y, H, b₁, hH, m₁, rfl, rfl⟩ ⟨d', B', Y', H', b₂, hH', m₂, e, rfl⟩ hr
    exact cmp X s Ω ξ W (Uc p) (Uc p') F (T p) (T p') d d' B B' Y Y' H H' b₁ b₂ r hgen hH hH'
      (hunitW p) (hunitW p') m₁ m₂ e.symm hr
  have relU : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X) (c c' : ℂ), Rel p x c → Rel p x c' → c = c' := fun p x c c' a a' => by
    have hz : genPt ξ ⤳ centre x := by
      obtain ⟨d, B, Y, H, b₁, hH, m₁, rfl, -⟩ := a
      exact hH.cpt b₁ m₁
    have := relCmp p p x c c' 1 a a' (by
      rw [div_self (gen p p (memU p)).1]; exact ValAt.one hz)
    simpa using this
  classical
  let h0 : Cpt ξ → (Sp ℂ ⟶ X) → ℂ := fun p x => if hh : ∃ c, Rel p x c then hh.choose else 0
  have h0s : ∀ p x c, Rel p x c → h0 p x = c := fun p x c hc => by
    have hh : ∃ c, Rel p x c := ⟨c, hc⟩
    simp only [h0, dif_pos hh]
    exact relU p x _ _ hh.choose_spec hc
  let h : Option (Cpt ξ) → (Sp ℂ ⟶ X) → ℂ := fun o => o.elim (fun _ => 0) h0
  let LL : LB X := LB.mk (Option (Cpt ξ)) V g
  have hhol : ∀ (i : LL.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
      (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ LL.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B := by
    rintro (_ | p) m B y oB hy hb
    · exact differentiableOn_const _
    · intro b₀ h₀
      obtain ⟨c, hc⟩ := relEx p (y b₀) (hb b₀ h₀).1 ((top_le_iff_centre _ _).1 (hb b₀ h₀).2)
      obtain ⟨d, B₁, Y, H, b₁, hH, m₁, e, -⟩ := hc
      obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := hH.chart.factor m B y oB hy (fun b hb' => (hb b hb').1) b₀ h₀ b₁ m₁ e.symm
      have eq : ∀ b ∈ ball b₀ ε, h (some p) (y b) = H (κ b) := fun b hb' => by
        obtain ⟨k1, k2⟩ := hκ b hb'
        exact h0s p _ _ ⟨d, B₁, Y, H, κ b, hH, k1, k2.symm, rfl⟩
      have m₁' : κ b₀ ∈ B₁ := k₀ ▸ m₁
      have dH : DifferentiableAt ℂ H (κ b₀) := (hH.hol _ m₁').differentiableAt (hH.chart.isOpen.mem_nhds m₁')
      have dk : DifferentiableAt ℂ κ b₀ := dκ.differentiableAt (ball_mem_nhds _ ε0)
      refine (DifferentiableAt.congr_of_eventuallyEq (dH.comp b₀ dk) ?_).differentiableWithinAt
      filter_upwards [ball_mem_nhds b₀ ε0] with b hb'
      exact eq b hb'
  have hcomp : ∀ (i j : LL.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (LL.U i ⊓ LL.U j) →
      h i x = valAt' x (LL.U i ⊓ LL.U j) (LL.g i j).val * h j x := by
    rintro (_ | p) (_ | p') x hx hm
    · simp [h]
    · have m := (top_le_iff_centre _ _).1 hm
      exact absurd (inZ p' _ m.2) (hV2 _ m.1)
    · have m := (top_le_iff_centre _ _).1 hm
      exact absurd (inZ p _ m.1) (hV2 _ m.2)
    · have m := (top_le_iff_centre _ _).1 hm
      obtain ⟨c, hc⟩ := relEx p x hx m.1
      obtain ⟨c', hc'⟩ := relEx p' x hx m.2
      have hz := inZ p _ m.1
      have vr := ValAt.of_section m hz (hg p p' _ hz m)
      show h0 p x = _ * h0 p' x
      rw [h0s _ _ _ hc, h0s _ _ _ hc']
      exact relCmp p p' x c c' _ hc hc' vr
  obtain ⟨σ, hσ⟩ := hG X s hp hs LL hLB h hhol hcomp
  have hne : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → centre x ∈ Uc p → h0 p x ≠ 0 := fun p x hx hm => by
    obtain ⟨c, hc⟩ := relEx p x hx hm
    rw [h0s _ _ _ hc]
    obtain ⟨d, B, Y, H, b₁, hH, m₁, -, rfl⟩ := hc
    exact hH.ne b₁ m₁
  have hu : ∀ p, IsUnit (σ.f (some p)) := fun p => unit X s (Uc p) _ inferInstance fun x hx hm => by
    rw [show valAt' x (Uc p) (σ.f (some p)) = h0 p x from hσ (some p) x hx ((top_le_iff_centre _ _).2 hm)]
    exact hne p x hx hm
  have gU : ∀ p : Cpt ξ, genPt ξ ∈ Uc p := fun p => genPt_mem p.2 (memU p)
  let c : Cpt ξ → Ω := fun p => genV ξ (Uc p) (gU p) (σ.f (some p))
  have hcT : ∀ p p', c p * T p = c p' * T p' := fun p p' => by
    have gI : genPt ξ ∈ Uc p ⊓ Uc p' := ⟨gU p, gU p'⟩
    have e := (congrArg (genV ξ (Uc p ⊓ Uc p') gI) (σ.compat (some p) (some p'))).trans
      (map_mul (genV ξ (Uc p ⊓ Uc p') gI) _ _)
    have e₁ := genV_res (ξ := ξ) (inf_le_left : Uc p ⊓ Uc p' ≤ Uc p) gI (gU p) (σ.f (some p))
    have e₂ := genV_res (ξ := ξ) (inf_le_right : Uc p ⊓ Uc p' ≤ Uc p') gI (gU p') (σ.f (some p'))
    have e₃ := (GagaC.genMap_germ (ξ := ξ) (Uc p ⊓ Uc p') specializes_rfl gI gI (g (some p) (some p')).val).symm.trans
      (hg p p' _ specializes_rfl gI)
    have e₄ : c p = T p' / T p * c p' := by
      show genV ξ (Uc p) (gU p) (σ.f (some p)) = _ * genV ξ (Uc p') (gU p') (σ.f (some p'))
      rw [← e₁, ← e₂, ← e₃]
      exact e
    have n₁ := (gen p p (memU p)).1
    rw [e₄]
    field_simp
  let f : Ω := c ⟨genPt ξ, specializes_rfl⟩ * T ⟨genPt ξ, specializes_rfl⟩
  have hf : ∀ p, f = c p * T p := fun p => hcT _ p
  refine ⟨f, 1, one_ne_zero, fun p => ?_, fun y hy hWy hc => ?_⟩
  · rw [hf p]
    exact isGenAt_mul_of_unitAt (gen p p (memU p)) (unitAt_genV p.2 (memU p) (gU p) (hu p))
  · let p : Cpt ξ := ⟨centre y, hc⟩
    have mU : centre y ∈ Uc p := memU p
    have hyW : centre y ∈ W := (top_le_iff_centre _ _).1 hWy
    have hy' : y ≫ s = 𝟙 _ := by rw [hy, spid]
    obtain ⟨r, -, hr⟩ := ValAt.exists_ne_zero hgen hc (hunitW p _ hc mU hyW)
    have v1 : ValAt ξ y (c p) (valAt' y (Uc p) (σ.f (some p))) :=
      ValAt.of_section mU hc (GagaC.genMap_germ _ hc mU (gU p) _)
    have v2 := ValAt.mul v1 hr
    rw [show valAt' y (Uc p) (σ.f (some p)) = h0 p y from hσ (some p) y hy' ((top_le_iff_centre _ _).2 mU)] at v2
    obtain ⟨cc, hcc⟩ := relEx p y hy' mU
    have e : F y = h0 p y * r := by
      rw [h0s _ _ _ hcc]
      obtain ⟨d, B, Y, H, b₁, hH, m₁, rfl, rfl⟩ := hcc
      exact hH.rel b₁ m₁ hyW r hr
    rw [_root_.one_mul, e, hf p]
    exact v2

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end
