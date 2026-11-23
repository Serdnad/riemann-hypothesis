module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle085
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle200
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle202
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PointCompare

section Val
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [Field F] {z : Sp F ⟶ X}

theorem val_mul {a a' : Ω} {r r' : F} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨hs, s, e1, e2⟩ := h
  obtain ⟨_, s', e1', e2'⟩ := h'
  have f2 : RootHt.Pick.valMap z s = r := e2
  have f2' : RootHt.Pick.valMap z s' = r' := e2'
  refine ⟨hs, s * s', by rw [map_mul, e1, e1'], ?_⟩
  show RootHt.Pick.valMap z (s * s') = r * r'
  rw [map_mul, f2, f2']

theorem val_det (h : genPt ξ ⤳ centre z) {n : ℕ} {P : Matrix (Fin n) (Fin n) Ω} {A : Matrix (Fin n) (Fin n) F}
    (hP : ∀ i j, ValAt ξ z (P i j) (A i j)) : ValAt ξ z P.det A.det := by
  have : ∀ i j, ∃ s : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ s = P i j ∧
      (Scheme.stalkClosedPointTo z).hom s = A i j := fun i j => by
    obtain ⟨_, s, e1, e2⟩ := hP i j
    exact ⟨s, e1, e2⟩
  choose s e1 e2 using this
  refine ⟨h, (Matrix.of s).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext i j
    exact e1 i j
  · show RootHt.Pick.valMap z _ = A.det
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact e2 i j

end Val

section Gen
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {F : Type} [Field F] {x : Sp F ⟶ S}

theorem exists_comb {n : ℕ} (cf : Fin n → F) (v : Fin n → (epsAt x ⟶ G)) : ∃ w, IsComb cf v w :=
  ⟨_, fun i => LieTangent.epsScale x (cf i) ≫ v i, fun _ => rfl, rfl⟩

theorem frame_det {P : Type} [CommRing P] {act : OAct P G} {σ : P →+* F} {n : ℕ} {v v' : Fin n → (epsAt x ⟶ G)}
    {A : Matrix (Fin n) (Fin n) F} (hv : IsEigFrame act x σ v) (hv' : IsEigFrame act x σ v')
    (hA : ∀ i, IsComb (A i) v (v' i)) : A.det ≠ 0 := by
  have : ∀ i, ∃ cf, IsComb cf v' (v i) := fun i => (hv'.2 _ (hv.1 i)).exists
  choose C hC using this
  have ht : ∀ i, IsTanAt G x (v i) := fun i => (hv.1 i).1
  have h1 := GlobalTheory.T.is_comb_matrix_mul S G F x n n n v v' v (Matrix.of C) A ht hA hC
  have h2 := GlobalTheory.T.is_comb_identity_matrix S G F x n v ht
  have h3 : Matrix.of C * A = 1 := by
    ext i j
    have := (hv.2 _ (hv.1 i)).unique (h1 i) (h2 i)
    exact congrFun this j
  intro h0
  have := congrArg Matrix.det h3
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem expand (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (σ' : 𝓞 E →+* F) {n : ℕ} {c₀ b₁ : Fin n → Z.V}
    {v₀ v : Vecs y n} {t : Z.Ω} (hc : (Z.eig σ).IsFrameAt c₀ ⟨_, h⟩) (h₀ : Rep.IsValFam Z y c₀ v₀)
    (h₁ : Rep.IsValFam Z y b₁ v) (he : ∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)))
    (hf₀ : IsEigFrame Xo.univ.t.act (under y) σ' v₀) (hf : IsEigFrame Xo.univ.t.act (under y) σ' v)
    (hw : exteriorPower.ιMulti Z.Ω n b₁ = t • exteriorPower.ιMulti Z.Ω n c₀) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, IsComb (A i) v₀ (v i)) ∧ A.det ≠ 0 ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) t A.det := by
  have hb : ∀ i, b₁ i ∈ Z.eig σ ⟨_, h⟩ := fun i => by
    obtain ⟨v', hv', -⟩ := h₁ i
    exact ⟨RootHt.Pick.mem_lat_of_val Z.M hv' h, he i⟩
  have hco : ∀ i, ∃ P : Fin n → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩, ∑ j, P j • c₀ j = b₁ i := fun i => by
    have := hb i
    rw [hc.2] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose P hP using hco
  have hval : ∀ i j, ∃ r : F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (P i j : Z.Ω) r := fun i j =>
    RootHt.Pick.exists_valAt (P i j).2
  choose A hA using hval
  let Pm : Matrix (Fin n) (Fin n) Z.Ω := fun i j => (P i j : Z.Ω)
  have hb' : b₁ = fun i => ∑ j, Pm i j • c₀ j := by
    funext i
    rw [← hP i]
    rfl
  have hdet : t = Pm.det := by
    have h1 := GlobalTheory.T.iota_multi_change_of_basis_det Z.Ω Z.V n c₀ Pm
    rw [← hb', hw] at h1
    have h2 : (t - Pm.det) • exteriorPower.ιMulti Z.Ω n c₀ = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (GlobalTheory.T.iota_multi_ne_zero_of_lin_indep Z.Ω Z.V n c₀ hc.1))
  have hcomb : ∀ i, IsComb (Matrix.of A i) v₀ (v i) := fun i => by
    obtain ⟨w, hw'⟩ := exists_comb (Matrix.of A i) v₀
    obtain ⟨w', hw₁, hw₂⟩ := GlobalTheory.T.component_specialization_tangent_comb E H D l Xo c O β Y U Z F y n c₀ v₀ (Pm i) (Matrix.of A i) w h h₀ (hA i) hw'
    obtain ⟨v', hv₁, hv₂⟩ := h₁ i
    have e : ∑ j, Pm i j • c₀ j = b₁ i := by rw [hb']
    rw [e] at hw₁
    have e' := LieModel.ValAt.unique Z.gen hw₁ hv₁
    subst e'
    rw [← SameVec.unique_left hw₂ hv₂]
    exact hw'
  refine ⟨Matrix.of A, hcomb, frame_det hf₀ hf hcomb, ?_⟩
  rw [hdet]
  exact val_det h hA

end Main

theorem valAt_pull {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') {a : Ω} {r : ℂ}
    (h : ValAt ξ (y' ≫ π) a r) : ValAt ξ' y' a r := by
  obtain ⟨hp, s, hs, hr⟩ := h
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  refine ⟨hq, (π.stalkMap (centre y')).hom s, ?_, ?_⟩
  · exact (RegAtDom.genMap_stalkMap hdom (centre y') hq hp s).trans hs
  · rw [← hr, Scheme.stalkClosedPointTo_comp]
    rfl

theorem genPt_specializes {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') : genPt ξ ⤳ centre (y' ≫ π) := by
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  have := hq.map π.continuous
  rw [RegAtDom.map_genPt hdom] at this
  exact this

theorem point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' y' yy v vz w wz α κ r hξ hgen hyy hΦ hf hfz hb₁ hb₂
    hz₁ hz₂ hfr he₁ he₂ hα hκ hw₁ hw₂ hr
  obtain ⟨hq, -⟩ := id hr
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    rw [hyy]
    exact genPt_specializes hξ hq
  obtain ⟨hfr₁, hfr₂⟩ := hfr ⟨_, h⟩ rfl
  have hw₁' : exteriorPower.ιMulti Z.Ω D.p b₁ = α⁻¹ • exteriorPower.ιMulti Z.Ω D.p v₁ := by
    rw [hw₁, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hw₂' : exteriorPower.ιMulti Z.Ω D.q b₂ = κ⁻¹ • exteriorPower.ιMulti Z.Ω D.q v₂ := by
    rw [hw₂, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨A, hA, hA0, hAv⟩ := expand Z h τ (σ.comp (tauIn c τ)) hfr₁ hz₁ hb₁ he₁ hfz.2.2.1 hf.2.2.1 hw₁'
  obtain ⟨B, hB, -, hBv⟩ := expand Z h (ComplexEmbedding.conjugate τ)
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) hfr₂ hz₂ hb₂ he₂ hfz.2.2.2 hf.2.2.2 hw₂'
  rw [hyy] at hAv hBv
  have hA' := valAt_pull hξ hq hAv
  have hB' := valAt_pull hξ hq hBv
  have hm := val_mul hr hA'
  have e : α / κ * α⁻¹ = κ⁻¹ := by field_simp
  rw [e] at hm
  have hdet : r * A.det = B.det := LieTangent.valAt_unique hgen hm hB'
  have hc := hΦ.chg yy vz wz v w A B hfz hf hA hB
  rw [← hdet] at hc
  rw [← _root_.mul_assoc] at hc
  exact mul_right_cancel₀ hA0 hc

end GlobalTheory.CompanionTheory.Ar.Flat.PointCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hodge_component_matches_model_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | exact GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unit_trivial_on_both_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (_ : AbQuot t x) (d : ℕ) (_ : GermAt t x d) (u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ), (ax0 t x).appTop.hom u.val = 1 → (ax1 t x).appTop.hom u.val = 1 → u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_prime_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.RootHt.LieFun GlobalTheory.CompanionTheory.Ar.Flat.BdryModel
open scoped CategoryTheory.Obj

theorem exists_coords_of_isLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 _) E) :
    ∃ e : Fin n → E, (∀ i, (M.pt (e i)).left = (v i).left) ∧ ∀ x, ∃ c : Fin n → R, x = ∑ i, c i • e i := by
  have h1 : ∀ i, ∃ e, (iota R).hom ≫ M.pt e = v i := fun i => by
    obtain ⟨e, he⟩ := M.onto ((iota R).inv ≫ v i) ((tan_iff _).1 (by simpa using hv.1 i))
    exact ⟨e, by simp [he]⟩
  choose e he using h1
  let F : Multiplicative E →* (epsR R ⟶ G) := MonoidHom.mk' (fun x => (iota R).hom ≫ M.pt x.toAdd)
    (fun a b => by simp [M.add, MonObj.comp_mul])
  have hs : ∀ c : Fin n → R, (iota R).hom ≫ M.pt (∑ i, c i • e i) =
      (List.ofFn fun i => (iota R).hom ≫ M.pt (c i • e i)).prod := fun c => by
    change F (Multiplicative.ofAdd (∑ i, c i • e i)) = _
    rw [ofAdd_sum, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hl : ∀ (c : R) i, ((iota R).hom ≫ M.pt (c • e i)).left = spMap (epsScaleR c) ≫ (v i).left := fun c i => by
    rw [iota_left, M.smul, ← he, iota_left]; rfl
  refine ⟨e, fun i => ?_, fun x => ?_⟩
  · rw [← he, iota_left]
  · obtain ⟨c, ⟨u, hu, hx⟩, -⟩ := hv.2 _ ((tan_iff _).2 (M.tan x))
    refine ⟨c, ?_⟩
    have : u = fun i => (iota R).hom ≫ M.pt (c i • e i) := by
      funext i; ext1; rw [hu, hl]
    rw [this, ← hs] at hx
    exact M.inj ((cancel_epi (iota R).hom).1 hx)

section Base

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S} {x' : Sp R' ⟶ S}
  {G : Over S} [GrpObj G] {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

theorem pt_smul_eq (M : LieModel G x E) (c : R) (e : E) : M.pt (c • e) = epsScale x c ≫ M.pt e :=
  Over.OverMorphism.ext (M.smul c e)

theorem pt_sum_base (φ : R →+* R') (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (M : LieModel G x E)
    (M' : LieModel G x' E') {I : Type} (s : Finset I) (d : I → R) (e : I → E) (e' : I → E')
    (h : ∀ i, M'.pt (e' i) = epsBase φ hφ ≫ M.pt (e i)) :
    M'.pt (∑ i ∈ s, φ (d i) • e' i) = epsBase φ hφ ≫ M.pt (∑ i ∈ s, d i • e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [LieModel.pt_zero, LieModel.pt_zero, MonObj.comp_one]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, M'.add, M.add, MonObj.comp_mul, ih, pt_smul_eq, pt_smul_eq, h,
      ← Category.assoc, ← Category.assoc, base_scale]

end Base

theorem exists_frame {X : Scheme.{0}} {G : Over X} [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v₀ : Fin n → (Sp (DualNumber Γ(X, U)) ⟶ G.left))
    (hv₀ : ∀ (R' : Type) [CommRing R'] (f : Γ(X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left),
      IsGrpPullback G' G (spMap f ≫ hU.fromSpec) φ →
        ∃ v' : Fin n → (epsR R' ⟶ G'),
          (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
    {R : Type} [CommRing R] (f : Γ(X, U) →+* R) {x : Sp R ⟶ X} (hx : spMap f ≫ hU.fromSpec = x)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ e : Fin n → E, (∀ j, (M.pt (e j)).left = spMap (dualMap f) ≫ v₀ j) ∧
      ∀ y, ∃ c : Fin n → R, y = ∑ j, c j • e j := by
  have hz : 𝟙 (Sp R) ≫ (spMap f ≫ hU.fromSpec) = x := by rw [Category.id_comp, hx]
  subst hz
  have hφ := isGrpPullback_pullback G (spMap f ≫ hU.fromSpec)
  obtain ⟨v', hv1, hv2⟩ := hv₀ R f _ _ hφ
  obtain ⟨M', hM'⟩ := (LieMove.models_correspond (x := 𝟙 (Sp R)) hφ E).1 M
  obtain ⟨e, he1, he2⟩ := exists_coords_of_isLieBasis v' hv2 M'
  refine ⟨e, fun j => ?_, he2⟩
  rw [← hM' (e j), he1 j, hv1 j]
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = dualMap f := by
    ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]

theorem fromSpec_ringHom_ext {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {R : Type} [CommRing R]
    {a a' : Γ(X, W) →+* R} (h : spMap a ≫ hW.fromSpec = spMap a' ≫ hW.fromSpec) : a = a' := by
  have h1 := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
  exact congrArg CommRingCat.Hom.hom h1

theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (φ' : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap φ')) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom (dualMap (φ'.comp φ))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem germ_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {p : X} (hp : p ∈ W) :
    Spec.map (CommRingCat.ofHom (X.presheaf.germ W p hp).hom) ≫ hW.fromSpec = X.fromSpecStalk p :=
  hW.fromSpecStalk_eq_fromSpecStalk hp

theorem exists_affine_frame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (q : Cpt ξ) (N : ℕ) (b : Fin N → Li), IsCptGen ξ → (∀ k, b k ∈ M.lat q) → ∃ (W : X.Opens) (hW : IsAffineOpen W) (v : Fin N → (epsAt (R := Γ(X, W)) hW.fromSpec ⟶ G)), q.1 ∈ W ∧ (∀ k, IsTanAt G hW.fromSpec (v k)) ∧ ∀ (ψ : Γ(X, W) →+* ℂ) (z : Sp ℂ ⟶ X), spMap ψ ≫ hW.fromSpec = z → genPt ξ ⤳ centre z → ∀ k, ∃ w : epsAt z ⟶ G, M.ValAt z (b k) w ∧ w.left = spMap (dualMap ψ) ≫ (v k).left := by
  intro X G _ _ _ Ω _ ξ Li _ _ M q N b hξ hb
  obtain ⟨W₀, hW₀, hq, -, n, v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X G q.1 ⊤ trivial
  let f : Γ(X, W₀) →+* X.presheaf.stalk q.1 := (X.presheaf.germ W₀ q.1 hq).hom
  obtain ⟨e, he1, he2⟩ := exists_frame hW₀ v₀ hv₀ f (germ_fromSpec hW₀ hq) (stalkLie hξ M q)
  have hc := fun k => he2 (⟨b k, hb k⟩ : Stalk M q)
  choose c hc using hc

  letI : Algebra Γ(X, W₀) (X.presheaf.stalk q.1) := f.toAlgebra
  haveI := hW₀.isLocalization_stalk ⟨q.1, hq⟩
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (fun p : Fin N × Fin n => c p.1 p.2)
  choose a ha using hint
  have hunit : IsUnit (f s) :=
    IsLocalization.map_units (M := (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl) (X.presheaf.stalk q.1) ⟨s, hs⟩
  have hqW : q.1 ∈ X.basicOpen s := (X.mem_basicOpen s q.1 hq).2 hunit
  have hW : IsAffineOpen (X.basicOpen s) := hW₀.basicOpen s
  let g : Γ(X, W₀) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  have hg : spMap g ≫ hW₀.fromSpec = hW.fromSpec := IsAffineOpen.map_fromSpec hW₀ hW (homOfLE (X.basicOpen_le s)).op
  obtain ⟨u, hu⟩ : IsUnit (g s) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace s
  obtain ⟨E', _, _, ⟨M'⟩⟩ := lieModel_exists X G Γ(X, X.basicOpen s) hW.fromSpec
  obtain ⟨e', he'1, -⟩ := exists_frame hW₀ v₀ hv₀ g hg M'
  let d : Fin N → Fin n → Γ(X, X.basicOpen s) := fun k j => g (a (k, j)) * (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)
  let v : Fin N → (epsAt (R := Γ(X, X.basicOpen s)) hW.fromSpec ⟶ G) := fun k => M'.pt (∑ j, d k j • e' j)
  let θ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk q.1 := (X.presheaf.germ _ q.1 hqW).hom
  have hθ : Spec.map (CommRingCat.ofHom θ) ≫ hW.fromSpec = X.fromSpecStalk q.1 := germ_fromSpec hW hqW
  have hθg : θ.comp g = f := by
    refine RingHom.ext fun t => ?_
    exact congrArg (fun m => m.hom t) (X.presheaf.germ_res (homOfLE (X.basicOpen_le s)) q.1 hqW)
  have hθa : ∀ t, θ (g t) = f t := fun t => congrArg (fun m => m t) hθg
  have key : ∀ k, (stalkLie hξ M q).pt ⟨b k, hb k⟩ = epsBase θ hθ ≫ v k := by
    intro k
    have hd : ∀ j, θ (d k j) = c k j := fun j => by
      have h1 : f (a (k, j)) = f s * c k j := ha (k, j)
      have h2 : θ (g s) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) = 1 := by
        rw [← map_mul, ← hu, Units.mul_inv, map_one]
      rw [hθa] at h2
      calc θ (d k j) = f (a (k, j)) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) := by rw [map_mul, hθa]
        _ = (f s * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)) * c k j := by rw [h1]; ring
        _ = c k j := by rw [h2, _root_.one_mul]
    have := pt_sum_base θ hθ M' (stalkLie hξ M q) Finset.univ (d k) e' e (fun j => Over.OverMorphism.ext (by
      rw [he1 j]
      change _ = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M'.pt (e' j)).left
      rw [he'1 j, ← Category.assoc, spec_dual_comp, hθg]))
    rw [hc k]
    simpa only [hd] using this
  refine ⟨X.basicOpen s, hW, v, hqW, fun k => M'.tan _, ?_⟩
  intro ψ z hz h k
  subst hz
  have hp : centre (spMap ψ ≫ hW.fromSpec) ∈ X.basicOpen s := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨(spMap ψ) (IsLocalRing.closedPoint ℂ), rfl⟩
  let θp : Γ(X, X.basicOpen s) →+* X.presheaf.stalk (centre (spMap ψ ≫ hW.fromSpec)) :=
    (X.presheaf.germ _ _ hp).hom
  have hθp : Spec.map (CommRingCat.ofHom θp) ≫ hW.fromSpec = X.fromSpecStalk _ := germ_fromSpec hW hp
  have e1 : (genMap ξ q).comp θ = (genMap ξ ⟨_, h⟩).comp θp := fromSpec_ringHom_ext hW (by
    change Spec.map (CommRingCat.ofHom _) ≫ _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, ← spec_comp, Category.assoc, Category.assoc, hθ, hθp, spec_genMap, spec_genMap])
  have e2 : ψ = (Scheme.stalkClosedPointTo (spMap ψ ≫ hW.fromSpec)).hom.comp θp := fromSpec_ringHom_ext hW (by
    change _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, Category.assoc, hθp]
    exact (spec_centre _).symm)
  refine ⟨epsBase ψ rfl ≫ v k, ⟨h, epsBase θp hθp ≫ v k, ⟨isTanAt_base _ _ (M'.tan _), ?_⟩, ?_⟩, rfl⟩
  · have t : (M.pt (b k)).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ q))) ≫
        ((stalkLie hξ M q).pt ⟨b k, hb k⟩).left := (Stalk.tan_spec (⟨b k, hb k⟩ : Stalk M q)).2
    rw [t, key k]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, ← Category.assoc, spec_dual_comp, spec_dual_comp, e1]
  · change Spec.map (CommRingCat.ofHom (dualMap ψ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, spec_dual_comp, ← e2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem _root_.GlobalTheory.T.hodge_component_finite_charts : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.semi_abelian_of_pullback : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback | exact GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback | (intros; apply GlobalTheory.CompanionTheory.Ar.isSemiAbelian_of_isGrpPullback <;> assumption)
end
