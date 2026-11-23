module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle139
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle147
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle148
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundles
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat

theorem not_inFibre_of_complex {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) :
    ¬ InFibre ξ p ⟨centre z, hz⟩ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) ≠ 0 := fun h0 =>
    hp0 ((map_natCast (Scheme.stalkClosedPointTo z).hom p).symm.trans h0)
  obtain ⟨u, hu⟩ := CxVal.isUnit _ hs
  have hg : genMap ξ ⟨centre z, hz⟩ (p : X.presheaf.stalk (centre z)) = (p : Ω) := map_natCast _ _
  intro h
  refine h ⟨Nat.cast_ne_zero.2 hp.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  have h1 : genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = (p : Ω) := by rw [hu, hg]
  have h2 : genMap ξ ⟨centre z, hz⟩ ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)) *
      genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem frame_mem_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z hgen hfr k
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_of_complex hgen hr
  have hm : bb k ∈ (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) ⟨centre z, hgen⟩ := by
    rw [hfr.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hm' : ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.V a ⟨centre z, hgen⟩ ⊔ 𝔐.V b ⟨centre z, hgen⟩ := hm
  rw [hV, hV] at hm'
  refine (sup_le ?_ ?_ : 𝔐.dR a ⟨centre z, hgen⟩ ⊔ 𝔐.dR b ⟨centre z, hgen⟩ ≤ 𝔐.M.lat ⟨centre z, hgen⟩) hm'
  · exact fun x hx => hx.1
  · exact fun x hx => hx.1

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem epsMul_eq {R : Type} [CommRing R] (a : R) :
    GlobalTheory.CompanionTheory.Ar.epsMul a = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a := by
  ext x <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul]

theorem isTanAt_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} (v : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt Xo.univ.t.G x v ↔ Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨fun h => ⟨Over.w v, h⟩, fun h => h.2⟩

theorem isEigVec_iff {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X} (τ : E →+* ℂ)
    (v : epsAt x ⟶ Xo.univ.t.G) :
    IsEigVec Xo.univ.t.act x ((algebraMap c.F R).comp (tauIn c τ)) v ↔
      Formalism.L2.Pj.IsTanAt x v.left ∧ Formalism.L2.Pj.IsEigAt c τ v.left := by
  refine and_congr (isTanAt_iff v) (forall_congr' fun a => ?_)
  rw [epsMul_eq]
  exact Iff.rfl

theorem isComb_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} {n : ℕ} (a : Fin n → R)
    (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)) (w : epsAt x ⟶ Xo.univ.t.G) :
    IsComb a v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) a w.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], rfl⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], Over.OverMorphism.ext hw.symm⟩

theorem exists_frame {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) (x : Sp F ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F F := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] F := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S F ψa z τ w.left h1 h2
  exact ⟨a, (isComb_iff a v w).2 ha, fun b hb => hu b ((isComb_iff b v w).1 hb)⟩

end GlobalTheory.CompanionTheory.Ar.FrameEig


open GlobalTheory.CompanionTheory.Ar.FrameEig in
theorem GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  intro E _ _ _ H D l Xo c τ S _ _ z F _ ψ y hp hq hx hs
  obtain ⟨v, hv, fv⟩ := exists_frame z ψ (under y) hx τ D.p hp
  obtain ⟨w, hw, fw⟩ := exists_frame z ψ (under y) hx (ComplexEmbedding.conjugate τ) D.q hq
  exact ⟨v, w, hv, hw, fun U hU => ⟨hs, hU, fv, fw⟩⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_ringEquiv_of_genPt_eq {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (ξ' : Sp Ω' ⟶ X) (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom)
    (h' : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom) (he : genPt ξ = genPt ξ') :
    ∃ e : Ω ≃+* Ω', spMap e.toRingHom ≫ ξ = ξ' := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso (Scheme.stalkClosedPointTo ξ') := (ConcreteCategory.isIso_iff_bijective _).2 h'
  have hi : Inseparable (ξ (IsLocalRing.closedPoint Ω)) (ξ' (IsLocalRing.closedPoint Ω')) := .of_eq he
  let i : CommRingCat.of Ω ≅ CommRingCat.of Ω' :=
    (asIso (Scheme.stalkClosedPointTo ξ)).symm ≪≫ X.presheaf.stalkCongr hi ≪≫
      asIso (Scheme.stalkClosedPointTo ξ')
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  have e1 : Scheme.stalkClosedPointTo ξ ≫ i.hom =
      (X.presheaf.stalkCongr hi).hom ≫ Scheme.stalkClosedPointTo ξ' := by simp [i]
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have h3 : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk _ = X.fromSpecStalk _ :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.symm.specializes
  show Spec.map i.hom ≫ ξ = ξ'
  conv_lhs => rw [← h1]
  conv_rhs => rw [← h2]
  rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, h3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem bijective_stalk_of_cptOver {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (hβ : FracBase β) : Function.Bijective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hβ.1 hβ.2.2
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω))
  have hg := Z.gen.bij
  rw [Scheme.stalkClosedPointTo_comp] at hg
  exact (Function.Bijective.of_comp_iff _ hb).1 hg

theorem genPt_eq_of_cptOver {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Y : Model Xo c β} {Y' : Model Xo c β'} {U : Set (Xo.XF c)} (Z : CptOver Y U) (Z' : CptOver Y' U) :
    genPt Z.ξ₀ = genPt Z'.ξ₀ :=
  (((Z.closure _).1 Z'.genPt_mem).antisymm ((Z'.closure _).1 Z.genPt_mem)).eq

theorem cptOver_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c U hU
  refine ⟨Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) ⟨U, hU⟩,
    fun O _ β Y hβ => nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y U hU, ?_⟩
  intro O _ β Y O' _ β' Y' Z Z' hβ hβ' hg
  obtain ⟨e, he⟩ := exists_ringEquiv_of_genPt_eq Z.ξ₀ Z'.ξ₀ (bijective_stalk_of_cptOver Z hβ)
    (bijective_stalk_of_cptOver Z' hβ') (genPt_eq_of_cptOver Z Z')
  have h2 : spMap e.toRingHom ≫ spMap Z.inc = spMap Z'.inc := by
    rw [← Z.over_inc, ← Z'.over_inc, ← he, Category.assoc]
  have h4 : CommRingCat.ofHom Z.inc ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom Z'.inc :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  have h3 : e.toRingHom.comp Z.inc = Z'.inc := congrArg CommRingCat.Hom.hom h4
  rintro x ⟨f, hf, hx⟩
  have h5 : f.eval₂ Z.inc (e.symm x) = 0 := by
    apply e.injective
    have := Polynomial.hom_eval₂ f Z.inc e.toRingHom (e.symm x)
    rw [h3] at this
    simpa [hx] using this
  obtain ⟨a, ha⟩ := hg (e.symm x) ⟨f, hf, h5⟩
  refine ⟨a, ?_⟩
  rw [← h3]
  simp [ha]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermLie

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) :=
  PositivityTheory.HtPt.Cd.germ_lie

end GlobalTheory.CompanionTheory.Ar.GermLie
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockSumFrame

theorem isVB_comap_of_range {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] (A : Lat ξ E')
    (S : Submodule Ω E') (i : E →ₗ[Ω] E') (hinj : Function.Injective i) (hrange : LinearMap.range i = S) {r : ℕ}
    (h : (Lat.comap A S.subtype).IsVB r ⊤) : (Lat.comap A i).IsVB r ⊤ := by
  have hmem : ∀ x, i x ∈ S := fun x => hrange ▸ LinearMap.mem_range_self i x
  let e : E →ₗ[Ω] S := i.codRestrict S hmem
  have hei : ∀ x, ((e x : S) : E') = i x := fun x => rfl
  have he_inj : Function.Injective e := fun x y hxy => hinj (by rw [← hei, ← hei, hxy])
  have he_surj : Function.Surjective e := fun s => by
    have : (s : E') ∈ LinearMap.range i := hrange ▸ s.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  let eq : E ≃ₗ[Ω] S := LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩
  have heq : ∀ x, ((eq x : S) : E') = i x := fun x => rfl
  intro p hp
  obtain ⟨U, hpU, b, hspan, hfr⟩ := h p hp
  refine ⟨U, hpU, fun k => eq.symm (b k), ?_, fun q hq hqU => ?_⟩
  · have : Set.range (fun k => eq.symm (b k)) = eq.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← LinearEquiv.coe_coe, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨hli, hst⟩ := hfr q hq hqU
    refine ⟨hli.map' eq.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
    ext x
    have h1 : x ∈ Lat.comap A i q ↔ eq x ∈ Lat.comap A S.subtype q := Iff.rfl
    rw [h1, hst]
    let eR : E ≃ₗ[regAt ξ q] S := eq.restrictScalars (regAt ξ q)
    have hrng : Set.range b = eR '' Set.range (fun k => eq.symm (b k)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun k => (eq.apply_symm_apply (b k)).symm)
    rw [hrng, ← LinearEquiv.coe_coe, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := eR.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem frame_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ cc f b h hw hfr hd
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
    rw [Or.rk_bg, Or.rk_sm]
    exact Nat.add_sub_cancel' Dc.j_le_N
  have hsum := GlobalTheory.T.pair_lattice_sum_comap E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) (Or.bg_ne_sm τ τ)
  rw [hrk] at hsum
  have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
    isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
  obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y hT z w cc f h hw hd
  exact (GlobalTheory.T.segre_chart_bundle Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) cc f b hfr.1 hfr.2.1
    hfr.2.2.1).1 hfr _ c1 c2

end GlobalTheory.CompanionTheory.Ar.BlockSumFrame
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermUniv

theorem germ_chart_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m :=
  PositivityTheory.HtPt.Cd.germ_univ

end GlobalTheory.CompanionTheory.Ar.GermUniv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.exists_val_at_vert_factor_eq_norm_mul_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.segre_refine_line_bundles : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : Type) [Finite A] (Λ : A → Lat M.ξ Ω), (∀ p : Cpt M.ξ, ∃ c₀, InChart M.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p) → (∀ a, (Λ a).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (deg : A → K' → ℤ), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ CoordTie o M.ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ a, (Λ a).IsDegOn Set.univ y' (deg a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | exact GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  first | exact @LevelTowerAlt.determinant_lattice_generator | exact LevelTowerAlt.determinant_lattice_generator
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | exact GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.coords_reindex_degree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.flag_cm_type_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag | exact GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag <;> assumption)
end
