module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle158
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle042
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle157
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGradedTensor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tau_conj (τ : E →+* ℂ) (a : E) : τ (IsCMField.complexConj E a) = ComplexEmbedding.conjugate τ a := by
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  rfl

theorem transition_unique (D : Datum H) {I : Type} [Fintype I] [DecidableEq I] (x e : I → D.La) (T T' : Matrix I I E)
    (hg : (gramE D e).det ≠ 0) (h : IsTransition D x e T) (h' : IsTransition D x e T') : T = T' := by
  have hmul : T * gramE D e = T' * gramE D e := by
    ext m j
    simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
    rw [← h m (e j), ← h' m (e j)]
  have hu : IsUnit (gramE D e).det := isUnit_iff_ne_zero.mpr hg
  calc T = T * gramE D e * (gramE D e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = T' * gramE D e * (gramE D e)⁻¹ := by rw [hmul]
    _ = T' := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

namespace GlobalTheory.CompanionTheory.Ar.Fl


open ChgGen in
theorem constMul_change_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (ρ : ℂ), LinearIndependent (𝓞 E) e → IsTransition (FU.Di i) x e T → T.det ≠ 0 → IsConstMul U τ φ FU i e ρ → IsConstMul U τ φ FU i x (ρ / τ T.det) := by
  intro E _ _ _ H D l Xo c g ty FU i U τ φ e x T ρ he hT hdet hC
  unfold IsConstMul at hC ⊢
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]
  obtain ⟨T₀, hT₀, hgram, -, n, S, hn, hS, hST⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hg : (gramE (FU.Di i) e).det ≠ 0 := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hTT : T₀ = T := transition_unique (FU.Di i) x e T₀ T hg hT₀ hT
  rw [hTT] at hgram hST
  have hconj : (⇑τ ∘ ⇑(IsCMField.complexConj E)) = ⇑(ComplexEmbedding.conjugate τ) :=
    funext fun a => tau_conj τ a
  have hlin : ∀ (σ : E →+* ℂ) (a : Fin D.p ⊕ Fin D.q → ℂ) (z : Fin D.p ⊕ Fin D.q → Fin g → ℂ),
      tyPart ty σ (∑ j, a j • z j) = ∑ j, a j • tyPart ty σ (z j) := by
    intro σ a z
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hinj : ∀ (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ), M.det ≠ 0 →
      ∀ u : Fin D.p ⊕ Fin D.q → Fin g → ℂ, (∀ m, ∑ l, M m l • u l = 0) → u = 0 := by
    intro M hM u hu
    funext l k
    have hv : M *ᵥ (fun l => u l k) = 0 := by
      funext m
      have := congrFun (hu m) k
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using this
    have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h2 := congrArg (fun v => M⁻¹ *ᵥ v) hv
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h2
    exact congrFun h2 l
  have hcomb : ∀ (Bm : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ)
      (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ) (W : Fin D.q → Fin g → ℂ) (m : Fin D.p ⊕ Fin D.q),
      ∑ j, (Bm * Mᵀ) j m • W j = ∑ l, M m l • ∑ j, Bm j l • W j := by
    intro Bm M W m
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, _root_.smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  intro P y v w V W C Fm B hPer hu hfr hV hW hCa hB hF
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : ∀ m k, P (x m) k = ∑ b, ty k (T m b) * P (e b) k := by
    intro m k
    have h1 : (n : ℂ) * P (x m) k = ∑ b, ty k (T m b) * P (e b) k * n := by
      have := congrArg (fun z => z k) (congrArg P (hS m))

      simp only [_root_.map_nsmul, _root_.map_sum, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hPer.1 (S m b) (e b) k, hST m b, _root_.map_mul, _root_.map_natCast]
      ring
    rw [← Finset.sum_mul, _root_.mul_comm (n : ℂ)] at h1
    exact mul_right_cancel₀ hn' h1
  have hPσ : ∀ (σ : E →+* ℂ) m, tyPart ty σ (P (x m)) = ∑ b, σ (T m b) • tyPart ty σ (P (e b)) := by
    intro σ m
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
      rw [hP m k, hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hBmat : B = Fm * T.map τ * (gramE (FU.Di i) e).map τ * (T.map (ComplexEmbedding.conjugate τ))ᵀ := by
    have h1 : B = Fm * (gramE (FU.Di i) x).map τ := by
      ext j m
      rw [← hF j m, Matrix.mul_apply]
      simp only [Matrix.map_apply, gramE, Matrix.of_apply]
    rw [h1, hgram, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hconj]
    simp only [Matrix.mul_assoc]
  have hTc : (T.map (ComplexEmbedding.conjugate τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (_root_.map_ne_zero _).mpr hdet
  have ha' : ∀ a, tyPart ty τ (∑ m, (C * T.map τ) a m • P (e m)) = V a := by
    intro a
    rw [← hCa a, hlin, hlin]
    simp only [hPσ τ, Matrix.mul_apply, Matrix.map_apply, Finset.smul_sum, Finset.sum_smul, _root_.smul_smul]
    exact Finset.sum_comm
  have hb' : ∀ m, tyPart ty (ComplexEmbedding.conjugate τ) (P (e m)) =
      ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m • W j := by
    have key := hinj (T.map (ComplexEmbedding.conjugate τ)) hTc
      (fun l => tyPart ty (ComplexEmbedding.conjugate τ) (P (e l)) -
        ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j l • W j) (by
        intro m
        simp only [smul_sub, Finset.sum_sub_distrib, Matrix.map_apply]
        rw [← hPσ (ComplexEmbedding.conjugate τ) m, hB m, hBmat, sub_eq_zero]
        exact hcomb _ _ W m)
    intro m
    exact sub_eq_zero.mp (congrFun key m)
  have hc' : ∀ j m, ∑ r, (Fm * T.map τ) j r * τ (sesq (FU.Di i) (e r) (e m)) =
      (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m := by
    intro j m
    rw [Matrix.mul_apply (M := Fm * T.map τ)]
    simp only [Matrix.map_apply, gramE, Matrix.of_apply]
  have key := hC P y v w V W (C * T.map τ) (Fm * T.map τ) (Fm * T.map τ * (gramE (FU.Di i) e).map τ)
    hPer hu hfr hV hW ha' hb' hc'
  rw [← Matrix.fromRows_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at key
  have hτ : τ T.det ≠ 0 := (_root_.map_ne_zero τ).mpr hdet
  rw [eq_div_iff hτ, ← key]
  ring

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formal_germ_dimension_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal | exact GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal | (intros; apply GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.FibreTaylor

theorem fibre_taylor_expansion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv (R := k) q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) :=
  PositivityTheory.HtPt.Cg.fibre_taylor

end GlobalTheory.CompanionTheory.Ar.FibreTaylor
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_lattice_degree_formula : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg | exact GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.curve_through_coordinates | exact GlobalTheory.CompanionTheory.Relay.curve_through_coordinates | (intros; apply GlobalTheory.CompanionTheory.Relay.curve_through_coordinates <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.LabConst

theorem valAt_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ)) (o : O) (r : R)
    (h : ValAt ξ z (algebraMap O Ω o) r) : r = ρ o := by
  obtain ⟨hsp, t, ht, rfl⟩ := h
  have hg' := ConstReg.genMap_germ_const ξ s hs ⟨centre z, hsp⟩ o
  have ht' := hg.inj ⟨centre z, hsp⟩ (ht.trans hg'.symm)
  rw [ht']
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem const_of_root {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (p : Polynomial ℤ) (hp : p.Monic)
    (hr : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, Polynomial.aeval (f b) p = 0)
    {b b' : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) 1) (hb' : b' ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    f b = f b' := by
  have hne : p.map (Int.castRingHom ℂ) ≠ 0 := (hp.map _).ne_zero
  have hfin : ((p.map (Int.castRingHom ℂ)).rootSet ℂ).Finite := Polynomial.rootSet_finite _ _
  haveI : Finite ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := hfin
  haveI : DiscreteTopology ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := inferInstance
  refine IsPreconnected.constant_of_mapsTo (convex_ball _ _).isPreconnected
    (T := (p.map (Int.castRingHom ℂ)).rootSet ℂ) ⟨inferInstance⟩ hf.continuousOn (fun x hx => ?_) hb hb'
  rw [Polynomial.mem_rootSet]
  refine ⟨hne, ?_⟩
  have h := hr x hx
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq] at h
  rw [Polynomial.coe_aeval_eq_eval]
  exact h

theorem labVal_const_of_isHolPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 R _ jj n ψ hψ
  have hB : ∀ b : Fin n → ℂ, ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ),
      𝔐.LabVal (spMap (ψ b) ≫ jj) id σ ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
    intro b
    obtain ⟨σ, h1, -, -, -, -, h6⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y S Ω K J y 𝔐 ℂ (spMap (ψ b) ≫ jj)
    obtain ⟨h7, h8, -⟩ := h6 (RingHom.id ℂ)
    exact ⟨σ, h1, by simpa using h7, by simpa using h8⟩
  choose σ hσ hc1 hc2 using hB
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = jj ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (jj ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have key : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ∃ r : R, ∀ b, σ b s a = ψ b r := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    refine ⟨ρ (IsIntegralClosure.mk' (𝓞 c.F) _ hint), fun b => ?_⟩
    refine valAt_const 𝔐.ξ 𝔐.tie.gen (𝔐.f ≫ Y.s) 𝔐.cst_over (spMap (ψ b) ≫ jj) ((ψ b).comp ρ) ?_ _ _ ?_
    · rw [Category.assoc, ← hρ]; simp [spMap]
    · have h := hσ b s a
      have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb (id s) a := by
        show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
        rw [IsIntegralClosure.algebraMap_mk']
      rw [he]; exact h
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hconst : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, σ b = σ 0 := by
    intro b hb
    funext s
    refine RingHom.ext fun a => ?_
    obtain ⟨r, hr⟩ := key s a
    obtain ⟨p, hpm, hpe⟩ := NumberField.RingOfIntegers.isIntegral a
    refine const_of_root (fun b => σ b s a) ?_ p hpm ?_ hb h0
    · have : (fun b => σ b s a) = fun b => ψ b r := funext hr
      rw [this]; exact hψ.2 r
    · intro x _
      have h1 : Polynomial.aeval a p = 0 := hpe
      have h2 : Polynomial.aeval (σ x s a) p = (σ x s).toIntAlgHom (Polynomial.aeval a p) :=
        Polynomial.aeval_algHom_apply (σ x s).toIntAlgHom a p
      rw [h2, h1, map_zero]
  refine ⟨σ 0, fun b hb => ?_, hc1 0, hc2 0⟩
  rw [← hconst b hb]
  exact hσ b

end GlobalTheory.CompanionTheory.Ar.Flat.LabConst
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  first | exact @PositivityTheory.HtPt.Mb.top_common | exact PositivityTheory.HtPt.Mb.top_common
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.exists_normal_dominating_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'], ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω') (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') ∧ Flat.NormalCpt M'.ξ ∧ IsFinite f ∧ ∀ p : Cpt M.ξ, NormAt M'.ξ f (algebraMap Ω Ω') p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation | exact GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation | (intros; apply GlobalTheory.CompanionTheory.Ar.NormEx.exists_normalisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.det_lattice_frame_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  first | exact @GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen | exact GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen | (intros; apply GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  first | exact @LevelTowerAlt.determinant_lattice_graded_tensor | exact LevelTowerAlt.determinant_lattice_graded_tensor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.component_data_intersection_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BigBlock.main | exact GlobalTheory.CompanionTheory.Ar.BigBlock.main | (intros; apply GlobalTheory.CompanionTheory.Ar.BigBlock.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem block_ratio_mem {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {c : (k : K) → J k} {p : Cpt ξ}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : J k) :
    y ⟨k, c k⟩ ≠ 0 ∧ y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  obtain ⟨h0, hc⟩ := hc
  have hck : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 h0) k (Finset.mem_univ k)
  refine ⟨hck k, ?_⟩
  have h := hc (Function.update c k i)
  have e : (∏ k', y ⟨k', Function.update c k i k'⟩) / (∏ k', y ⟨k', c k'⟩) = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb]
      exact div_self (hck b)
    · simp
  rw [← e]
  exact h

theorem tie_blocks : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' _ hy hx hd
  have h1 : CoordTie ℤ ξ' (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x' p.2) ⟨k, c' k⟩) := by
    simpa using CoordBase.coordTie_reindex (Equiv.funUnique Unit (Fin (N + 1))) hx
  have h2 : ∀ (k : K) (p : Cpt ξ'), ∃ i, InChart ξ'
      (fun i' : J k => (fun p : (Σ k, J k) => algebraMap Ω₀ Ω (y p)) ⟨k, i'⟩) i p := by
    intro k p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd p
    obtain ⟨c, hc⟩ := hy.cover ⟨f p.1, h⟩
    refine ⟨c k, ?_, fun i => ?_⟩
    · exact (map_ne_zero _).2 (block_ratio_mem hc k (c k)).1
    · have := hreg _ (block_ratio_mem hc k i).2
      rwa [map_div₀] at this
  have h3 := GlobalTheory.T.coords_join_blocks X' Ω ξ' Unit (fun _ => Fin (N + 1)) (fun p => x' p.2) K J
    (fun p => algebraMap Ω₀ Ω (y p)) h1 h2
  convert h3 using 2 with c'
  exact Fintype.prod_sum_type _

end GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks
end
end
