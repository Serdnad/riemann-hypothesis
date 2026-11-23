module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle261
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquiv
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeFreeEveryStalk
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle260
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family | exact GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.root_origin_good_primes_finite : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 :=
  @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_cover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_point_mem_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U :=
  @_root_.SheetDecomposition.One.genPt_mem_dense
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeFibre

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexAt NumberField.ComplexEmbedding

section Linear

variable {F W : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup W] [Module ℂ W]

@[reducible] def coreOfForm (e : F ≃ₗ[ℂ] W) (h : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) :
    InnerProductSpace.Core ℂ F where
  inner a b := h (e a) (e b)
  conj_inner_symm a b := by
    simpa using (hh (e b) (e a)).symm
  re_inner_nonneg a := by
    by_cases ha : e a = 0
    · simp [ha]
    · exact (hp _ ha).le
  add_left a b c := by simp
  smul_left a b r := by simp
  definite a h0 := by
    by_contra ha
    have := hp (e a) (fun h1 => ha (by simpa using h1))
    rw [h0] at this
    simp at this

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]

theorem exists_metric [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V]
    (W : (L →+* ℂ) → Type) [∀ σ, AddCommGroup (W σ)] [∀ σ, Module ℂ (W σ)]
    (e : ∀ σ, Fibre σ V ≃ₗ[ℂ] W σ) (h : ∀ σ, W σ →ₗ⋆[ℂ] W σ →ₗ[ℂ] ℂ)
    (hh : ∀ σ v w, h σ w v = starRingEnd ℂ (h σ v w)) (hp : ∀ σ v, v ≠ 0 → 0 < (h σ v v).re)
    (hc : ∀ σ (x y : V), h (conjugate σ) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ x)) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ y)) =
      starRingEnd ℂ (h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)))) :
    ∃ m : HermitianMetric L V, ∀ σ (x y : V), (m.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) =
      h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)) := by
  have tm : ∀ (σ : L →+* ℂ) (z : ComplexAt σ) (x : V), (z ⊗ₜ[𝓞 L] x : Fibre σ V) =
      ((ofComplex σ).symm z : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := fun σ z x => by
    rw [TensorProduct.smul_tmul', _root_.GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def]
    simp
  have cm : ∀ (σ : L →+* ℂ) (x : V), conjMap σ V ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) =
      (1 : ComplexAt (conjugate σ)) ⊗ₜ[𝓞 L] x := fun σ x => by
    rw [conjMap_tmul, map_one]
  refine ⟨⟨fun σ => coreOfForm (e σ) (h σ) (hh σ) (hp σ), fun σ x y => ?_⟩, fun σ x y => rfl⟩
  change h _ (e _ _) (e _ _) = starRingEnd ℂ (h σ (e σ x) (e σ y))
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | tmul z a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc' hd => simp only [map_add (f := _), ← hc', ← hd]
    | tmul w b =>
      rw [tm σ z a, tm σ w b, conjMap_smul, conjMap_smul, cm, cm]
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, hc, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]

end Linear

section Geo

theorem exists_fibre_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {L : Type} [Field L] [NumberField L]
    (x : Sp (𝓞 L) ⟶ S) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G x V) (σ : L →+* ℂ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ x) W)
    (j : V →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] W)
    (hj : ∀ a, ((Mσ.pt (j a)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt a).left)) :
    ∃ e : Fibre σ V ≃ₗ[ℂ] W, ∀ a, e ((1 : ComplexAt σ) ⊗ₜ a) = j a := by
  letI i₀ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  letI i₂ : Module (𝓞 L) W := Module.compHom W (algebraMap (𝓞 L) ℂ)
  haveI i₃ : IsScalarTower (𝓞 L) ℂ W := ⟨fun a z w => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let j' : V →ₗ[𝓞 L] W := { toFun := j, map_add' := map_add j, map_smul' := fun a v => j.map_smulₛₗ a v }
  have hb : IsBaseChange ℂ j' :=
    GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ x V W M Mσ j' hj
  let l : ComplexAt σ ≃ₗ[𝓞 L] ℂ :=
    { toFun := (ofComplex σ).symm, invFun := ofComplex σ, map_add' := map_add _,
      map_smul' := fun a z => rfl, left_inv := (ofComplex σ).left_inv, right_inv := (ofComplex σ).right_inv }
  let e₀ : Fibre σ V ≃ₗ[𝓞 L] ℂ ⊗[𝓞 L] V := TensorProduct.congr l (LinearEquiv.refl _ V)
  let E : Fibre σ V ≃+ W := e₀.toAddEquiv.trans hb.equiv.toAddEquiv
  have he : ∀ z a, E (z ⊗ₜ a) = ((ofComplex σ).symm z) • j a := fun z a => by
    change hb.equiv (e₀ (z ⊗ₜ a)) = _
    change hb.equiv (l z ⊗ₜ a) = _
    rw [hb.equiv_tmul]
    rfl
  refine ⟨{ E with map_smul' := fun c t => ?_ }, fun a => ?_⟩
  · change E (c • t) = c • E t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.smul_tmul', he, he, _root_.GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, map_mul, mul_smul]
      simp
    | add a b ha hb' => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb', smul_add]
  · exact (he 1 a).trans (by simp)

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem lifts_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) {c : R →+* R'} {x' : Sp R' ⟶ S} {a : V}
    {v : epsAt x' ⟶ G} (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left)) : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left :=
  (Category.comp_id _).symm.trans h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polarised_at {L : Type} [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L))
    (m : SABMap tK t (spMap (algebraMap (𝓞 L) L))) (hK : IsPrincipal tK) (σ : L →+* ℂ) :
    ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)),
      IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  obtain ⟨hP, hA, -⟩ := hK
  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab (spMap σ) tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := by
    rw [Category.comp_id, spectrumMap_comp]
  refine ⟨t', e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 hP
  · obtain ⟨w, gw, -⟩ := m₁.lin
    exact relAmple_pull m₁.cart.1 tK.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _)
      (fun _ => trivial) hA

theorem hodgeInnerProduct_conj_of_eq {X : Scheme.{0}} (t : SAB H X) {z z' : Sp ℂ ⟶ X}
    (hz : z' = spMap (starRingEnd ℂ) ≫ z) {v w : epsAt z ⟶ t.G} {v' w' : epsAt z' ⟶ t.G} {c : ℂ}
    (hv : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left)
    (hw : w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (h : HodgeIP t.G t.PP.L z v w c) :
    HodgeIP t.G t.PP.L z' v' w' (starRingEnd ℂ c) := by
  subst hz
  exact GlobalTheory.T.hodge_inner_product_conjugate E H X t z v w v' w' c hv hw h

end Geo

theorem exists_hermitianBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK → ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB := by
  intro E _ _ _ H L _ _ t tK m hK
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨V, i₁, i₂, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G (𝓞 L) (𝟙 _)
  obtain ⟨hf, hpj⟩ := GlobalTheory.T.lie_model_finite_projective _ t.G (𝓞 L) (𝟙 _) V M
  have hW := fun σ : L →+* ℂ => GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)
  choose W iW₁ iW₂ hM using hW
  let Mσ : ∀ σ : L →+* ℂ, LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (W σ) := fun σ => (hM σ).some
  choose j hj using fun σ : L →+* ℂ =>
    (GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts _ t.G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) V (W σ) M (Mσ σ)).exists
  choose e he using fun σ : L →+* ℂ => exists_fibre_equiv t.G (𝟙 _) M σ (Mσ σ) (j σ) (hj σ)
  choose h hI hh hp using fun σ : L →+* ℂ =>
    GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H _ t _ (W σ) (Mσ σ) (polarised_at t tK m hK σ)
  have hcs : ∀ σ : L →+* ℂ, (conjugate σ).comp (algebraMap (𝓞 L) L) =
      (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L)) := fun σ => RingHom.ext fun a => rfl
  have hl : ∀ (σ : L →+* ℂ) (x : V), ((Mσ (conjugate σ)).pt (j _ x)).left =
      spMap (dualMap (starRingEnd ℂ)) ≫ ((Mσ σ).pt (j σ x)).left := fun σ x => by
    have e₁ : spMap (dualMap ((conjugate σ).comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) := by
      rw [hcs, dualMap_comp_alt, spectrumMap_comp]
    exact (lifts_left M (hj _ x)).trans ((congrArg (· ≫ (M.pt x).left) e₁).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (lifts_left M (hj σ x)).symm)))
  have hz : ∀ σ : L →+* ℂ, spMap ((conjugate σ).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      spMap (starRingEnd ℂ) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := fun σ => by
    rw [Category.comp_id, Category.comp_id, hcs, spectrumMap_comp]
  obtain ⟨mt, hmt⟩ := exists_metric W e h hh hp fun σ x y => by
    rw [he, he, he, he]
    exact ((hI _ _ _ _).1 (hodgeInnerProduct_conj_of_eq t (hz σ) (hl σ x) (hl σ y) ((hI σ _ _ _).2 rfl))).symm
  refine ⟨{ carrier := V, metric := mt }, M, fun σ x x' v v' hv hv' => ?_⟩
  have key : ∀ (a : V) (u : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) ⟶ t.G),
      (u.left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt a).left) → u = (Mσ σ).pt (j σ a) := fun a u ha => by
    exact Over.OverMorphism.ext ((lifts_left M ha).trans (lifts_left M (hj σ a)).symm)
  obtain rfl := key x v hv
  obtain rfl := key x' v' hv'
  have := hmt σ x x'
  rw [he, he] at this
  rw [this]
  exact (hI σ _ _ _).2 rfl

end GlobalTheory.CompanionTheory.Ar.HodgeFibre
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.root_lines_weight_bound_of_free : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_unit_analytic_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anUnit | exact GlobalTheory.CompanionTheory.Ar.Flat.anUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.archimedean_frame_of_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.fibre_lattice_linear_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (A₀ : Type) (x : A₀ → Fin g → ℂ) (x' : A₀ → Fin g' → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), FibreLatVec t z R x v → FibreLatVec t z R' x' v → ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), φ '' Set.range R.P = Set.range R'.P ∧ (∀ p q, R'.ip (φ p) (φ q) = R.ip p q) ∧ (∀ a p, φ (R.B a p) = R'.B a (φ p)) ∧ ∀ i, φ (x i) = x' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hfree_at_component_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r :=
  PositivityTheory.Xgn.hodge_free_every_stalk

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem _root_.GlobalTheory.T.period_riemann_lattice_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_type_exterior_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t₀ : ℝ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (hc : genPt 𝔐.ξ ⤳ centre z) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ) (α κ : Ω) (u : ℂ), CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → Represents Y U τ.1 Z.M a b φ → HasInfNorm U τ.1 φ s t₀ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → 𝔐.Interior z → (∀ a : c.F, ValAt 𝔐.ξ z (𝔐.cst a) (s a)) → (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, hc⟩ → (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, hc⟩ → 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ → 𝔐.M.GramAt 𝔐.t.PP.L z bq Δ → Γ.PosDef → Δ.PosDef → a' = α • exteriorPower.ιMulti Ω _ bp → b' = κ • exteriorPower.ιMulti Ω _ bq → ValAt 𝔐.ξ z (α / κ) u → Real.log ‖u‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr.hodge_norm | exact GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr.hodge_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr.hodge_norm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart <;> assumption)
end
