module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle138
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle157
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.PointDet

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem connectedSpace_of_specializes {X : Scheme.{0}} (x : X) (h : ∀ q : X, x ⤳ q) : ConnectedSpace X := by
  have hcl : closure {x} = (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (h q)
  have hp : PreconnectedSpace X := ⟨by rw [← hcl]; exact isPreconnected_singleton.closure⟩
  exact { toPreconnectedSpace := hp, toNonempty := ⟨x⟩ }

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

noncomputable def rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : c.F :=
  ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem rtF_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtF c ^ 2 = -(H.d : c.F) := by
  apply Subtype.ext
  simpa [rtF] using H.sqrt_neg_disc_sq

theorem isIntegral_rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    IsIntegral ℤ (rtF c) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [rtF_sq]
  have := isIntegral_algebraMap (R := ℤ) (A := c.F) (x := -(H.d : ℤ))
  simpa using this

noncomputable def rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : 𝓞 c.F :=
  IsIntegralClosure.mk' (𝓞 c.F) (rtF c) (isIntegral_rtF c)

theorem algebraMap_rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    algebraMap (𝓞 c.F) c.F (rtO c) = rtF c :=
  IsIntegralClosure.algebraMap_mk' _ _ _

theorem rtO_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtO c ^ 2 = -(H.d : 𝓞 c.F) := by
  apply RingOfIntegers.ext
  have := rtF_sq c
  rw [← algebraMap_rtO] at this
  simpa using this

theorem detCond_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  intro E _ _ _ H D l Xo c Y S Ω _ Kf _ J _ y 𝔐 L _ _ z
  haveI : IsReduced 𝔐.X := isReduced_of_isNormalScheme 𝔐.normal
  haveI : ConnectedSpace 𝔐.X := connectedSpace_of_specializes _ 𝔐.all
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.Ggeo.exists_smoothOfRelativeDimension_of_geometricallyConnected 𝔐.X 𝔐.t.G 𝔐.t.semi.smooth 𝔐.t.semi.geomConnected
  let s : 𝔐.X ⟶ Sp (𝓞 c.F) := 𝔐.f ≫ Y.s
  have hd : Dense {p : 𝔐.X | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ 𝔐.X)
      (β : 𝓞 c.F →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D 𝔐.t.act x (β (rtO c))} := by
    intro q
    refine closure_mono (Set.singleton_subset_iff.2 ?_) (specializes_iff_mem_closure.1 (𝔐.all q))
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
    haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
    haveI : CharZero (AlgebraicClosure Ω) := charZero_of_injective_ringHom i.injective
    refine ⟨AlgebraicClosure Ω, inferInstance, inferInstance, inferInstance, spMap i ≫ 𝔐.ξ,
      i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)), ?_, ?_, ?_⟩
    · let y₀ : Sp (AlgebraicClosure Ω) := (default : PrimeSpectrum (AlgebraicClosure Ω))
      refine ⟨y₀, ?_⟩
      rw [Scheme.Hom.comp_apply]
      exact congrArg 𝔐.ξ (Subsingleton.elim _ _)
    · have h := 𝔐.cst_over
      change (spMap i ≫ 𝔐.ξ) ≫ 𝔐.f ≫ Y.s = _
      rw [Category.assoc, h, spMap_comp_spMap]
    · intro τ
      have hβ : (i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) (rtO c) = (i.comp 𝔐.cst) (rtF c) := by
        simp only [RingHom.comp_apply, algebraMap_rtO]
      rw [hβ]
      obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.Ar.LabelCover.exists_label E H l c (rtF c) rfl (AlgebraicClosure Ω) (i.comp 𝔐.cst) τ
      constructor
      · intro h
        obtain ⟨t, rfl⟩ := h₁ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inl t)) D.p).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inl t))
      · intro h
        obtain ⟨t, rfl⟩ := h₂ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inr t)) D.q).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inr t))
  obtain ⟨b, hb⟩ := Spec.map_surjective (z ≫ s)
  refine ⟨b.hom (rtO c), ?_, ?_⟩
  · have := congrArg b.hom (rtO_sq c)
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  · intro k _ _ g
    haveI : CharZero k := charZero_of_injective_ringHom g.injective
    refine GlobalTheory.DetSpread.detCond_of_dense E H D 𝔐.X 𝔐.t.G n 𝔐.t.act (𝓞 c.F) s (rtO c) hn (rtO_sq c) hd k
      (spMap g ≫ z) (g.comp b.hom) ?_
    rw [Category.assoc, ← hb]
    exact spMap_comp_spMap b.hom g

end GlobalTheory.CompanionTheory.Ar.PointDet
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anSolve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU _ _ hτ i e P y v w he hP hy hfr
  obtain ⟨-, -, hv, hw⟩ := hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, hWs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hS : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))).det ≠ 0 := by
    have := hd 0 _ e hcard he
    have h2 : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, h4, h5⟩, hu⟩ := GlobalTheory.T.hermitian_period_linear_algebra D.p D.q g (tyPart ty τ') (tyPart ty (ComplexEmbedding.conjugate τ')) V W (fun m => P (e m)) _ Hm hlin hHh hHp hS hVl hWl (fun n => hVs _) (fun n => hWs _) (fun m n => hs τ' _ _)
  refine ⟨⟨V, W, Fm, B, d⟩, ⟨fun a => (hVd a _).2 rfl, fun j => (hWd j _).2 rfl, h1, h2, h3, h4, h5⟩, ?_⟩
  rintro ⟨V', W', Fm', B', d'⟩ ⟨k1, k2, k3, k4, k5, k6, k7⟩
  have eV : V' = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W' = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  have := hu ⟨Fm', B', d'⟩ ⟨k3, k4, k5, k6, k7⟩
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.hodge_component_label_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt | exact GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.hodge_generated_sum_specialization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.ActFam

theorem comp_mul_hom {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    (u ≫ a) * (u ≫ b) = u ≫ (a * b) := by
  rw [Hom.mul_def, Hom.mul_def, comp_lift_assoc]

theorem exists_action_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  intro E _ _ _ H R _ t g n M ρ ψ e hρ
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ
  have hlift := fun c : 𝓞 E => exists_linear_lift_of_additive_family R t.G g n M (Metric.ball 0 ρ) ψ e g
    (Metric.ball 0 ρ) (fun b z => e.ex b z ≫ t.act.act c) Metric.isOpen_ball subset_rfl
    (fun b hb z w => by
      haveI := t.act.hom c
      simp only [e.add b hb z w]
      exact (IsMonHom.monoidHom (t.act.act c) _).map_mul _ _)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp e.hol (t.act.act c).left)
  choose h hd hs using hlift
  have hex : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ z, e.ex b (h c b z) = e.ex b z ≫ t.act.act c :=
    fun c b hb z => (hs c b hb).1 z
  have huq : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z, e.ex b (l z) = e.ex b z ≫ t.act.act c) → l = h c b :=
    fun c b hb l hl => (hs c b hb).2.1 l hl
  have hring : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ), ∀ c, f c = h c b := by
    intro b hb
    refine ⟨RingHom.mk' ⟨⟨fun c => h c b, ?_⟩, ?_⟩ ?_, fun c => rfl⟩
    · refine (huq 1 b hb LinearMap.id fun z => ?_).symm
      rw [t.act.one]
      exact (Category.comp_id _).symm
    · intro c c'
      refine (huq (c * c') b hb (h c b * h c' b) fun z => ?_).symm
      rw [Module.End.mul_apply, hex c b hb, hex c' b hb, mul_comm c c', t.act.mul, Category.assoc]
    · intro c c'
      refine (huq (c + c') b hb (h c b + h c' b) fun z => ?_).symm
      rw [LinearMap.add_apply, e.add b hb, hex c b hb, hex c' b hb, t.act.add, comp_mul_hom]
  have hall : ∀ b, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ),
      b ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ c, f c = h c b := by
    intro b
    by_cases hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ
    · obtain ⟨f, hf⟩ := hring b hb
      exact ⟨f, fun _ => hf⟩
    · obtain ⟨f, -⟩ := hring 0 h0
      exact ⟨f, fun hb' => absurd hb' hb⟩
  choose B hB using hall
  refine ⟨B, fun c x => ?_, fun b hb c x => ?_⟩
  · refine (hd c x).congr fun b hb => ?_
    simp only [hB b hb c]
  · rw [hB b hb c]
    exact hex c b hb x

end GlobalTheory.CompanionTheory.Ar.Flat.ActFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.flag_label_bases_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ m : ℕ, 0 < m ∧ ∀ (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ), ∃ (b : Fin (labelRk D s) → 𝔐.Li) (π : Fin (labelRk D s) → Module.Dual Ω 𝔐.Li), (∀ i, flagStep Ω b i = flagStep Ω (Fl.b s) i) ∧ (𝔐.V s).IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ 𝔐.M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧ ∀ i, ∀ e ∈ 𝔐.M.lat p, (m : Ω) * π i e ∈ regAt 𝔐.ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | exact GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.frame_point_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | exact GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem flagged_model_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl _ hβ
  obtain ⟨-, ⟨x, hx⟩, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c O β Y 𝔐.Ω₀ 𝔐.ξ₀ Ω x 𝔐.fn hβ 𝔐.gen₀ (hx ▸ 𝔐.fn_over)
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  have hB := GlobalTheory.T.generic_flag_trdeg_formula 𝔐.Ω₀ Ω Fl.Li₀ 𝔐.Li Fl.j (CMType H ⊕ CMType H) (labelRk D) Fl.V₀ Fl.b Fl.deg Fl.generic
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).mpr hchar
  haveI : FaithfulSMul ℤ 𝔐.Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ 𝔐.Ω₀).mpr Int.cast_injective
  haveI : FaithfulSMul 𝔐.Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective 𝔐.Ω₀ Ω).mpr 𝔐.fn.injective
  have htow := trdeg_add_eq ℤ 𝔐.Ω₀ (A := Ω)
  rw [hA, hB] at htow
  have hcard : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have harith : D.dim + ∑ σ : CMType H ⊕ CMType H, labelRk D σ * (labelRk D σ - 1) / 2 =
      Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) := by
    have h1 : (D.p + D.q) * (D.p + D.q - 1) / 2 = D.p * (D.p - 1) / 2 + D.q * (D.q - 1) / 2 + D.p * D.q := by
      rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
      simp [Finset.Nat.antidiagonal_succ, Finset.sum_range_succ]
      ring
    rw [Fintype.sum_sum_type, h1, Datum.dim, ← hcard]
    simp [Finset.sum_const, Finset.card_univ, labelRk]
    ring
  have htr : Algebra.trdeg ℤ Ω = ((Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) : ℕ) : Cardinal) := by
    rw [← htow, ← harith]; push_cast; rfl
  exact GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ 𝔐.tie htr

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.irreducible_component_clopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.cptOver_any | exact GlobalTheory.CompanionTheory.Ar.Br.cptOver_any | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.cptOver_any <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FibrePol

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem exists_fibre_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H L _ _ D σ
  have hC := Out.CubePf.cubePull
  let m₁ := PullbackSections.sabM hC (spMap σ) D.tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ D.m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = emb σ := by
    simp only [emb, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨w, hw, -⟩ := m₁.lin
  refine ⟨PullbackSections.sabT hC (spMap σ) D.tK, e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 D.princ.1
  · exact relAmple_pull m₁.cart.1 D.tK.PP.isLB (PullbackSections.sabT hC (spMap σ) D.tK).PP.isLB ((isGen_iff w).1 hw) ⊤
      (isAffineOpen_top _) (fun _ => trivial) D.princ.2.1

end GlobalTheory.CompanionTheory.Ar.Sl.FibrePol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formal_germ_lie_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie | exact GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie | (intros; apply GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.component_data_hodge_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at | exact GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at <;> assumption)
end
