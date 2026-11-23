module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

section Frac

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem stalk_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ f g : Γ(X, U), IsUnit (X.presheaf.germ U p hp g) ∧
      s * X.presheaf.germ U p hp g = X.presheaf.germ U p hp f := by
  let : Algebra Γ(X, U) (X.presheaf.stalk p) := (X.presheaf.germ U p hp).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨f, g⟩, h⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl (S := X.presheaf.stalk p) s
  exact ⟨f, g, IsLocalization.map_units (X.presheaf.stalk p) g, h⟩

theorem genMap_germ_indep {U : X.Opens} {p q : Cpt ξ} (hp : p.1 ∈ U) (hq : q.1 ∈ U) (f : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp f) = genMap ξ q (X.presheaf.germ U q.1 hq f) := by
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  have key : ∀ r : Cpt ξ, ∀ hr : r.1 ∈ U, genMap ξ r (X.presheaf.germ U r.1 hr f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg f) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 f)
  rw [key p hp, key q hq]

theorem exists_frac {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) :
    ∃ (P Q : MvPolynomial κ ℤ) (t : X.presheaf.stalk p.1), IsUnit t ∧
      genMap ξ p t = MvPolynomial.aeval (fun j => x j / x c) Q ∧
      a * MvPolynomial.aeval (fun j => x j / x c) Q = MvPolynomial.aeval (fun j => x j / x c) P := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hp.1
  have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨f, g, hg, e⟩ := stalk_frac hU hpU s
  have hA : ∀ f : Γ(X, U), ∃ P : MvPolynomial κ ℤ, MvPolynomial.aeval (fun j => x j / x c) P =
      genMap ξ p (X.presheaf.germ U p.1 hpU f) := by
    intro f
    have hm : genMap ξ p (X.presheaf.germ U p.1 hpU f) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hp.1 _).2 fun q hq => ?_
      have hqU : q.1 ∈ U := (hmem q.1).2 ⟨q.2, hq⟩
      rw [genMap_germ_indep hpU hqU]
      exact ⟨_, rfl⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hm
    obtain ⟨P, hP⟩ := hm
    exact ⟨P, hP⟩
  obtain ⟨P, hP⟩ := hA f
  obtain ⟨Q, hQ⟩ := hA g
  refine ⟨P, Q, X.presheaf.germ U p.1 hpU g, hg, hQ.symm, ?_⟩
  rw [hP, hQ, ← map_mul, e]

end Frac

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}

theorem val_intCast (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_finsetProd (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (a : I → Ω) (r : I → ℂ)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def ratioAt (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) (c' : (k : K) → J k) : ℂ :=
  ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_ratio {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (ratioAt c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_finsetProd hz _ _ _ fun k _ => ?_
  obtain ⟨-, h2⟩ := hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  obtain ⟨r, hr, e⟩ := h2 (c' k)
  rw [e, mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem val_ratioPoly {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ValAt ξ z (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P)
      (MvPolynomial.aeval (ratioAt c w) P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_intCast hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (val_ratio hz hw hc i)

theorem continuousAt_ratioAt {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (c' : (k : K) → J k) : ContinuousAt (fun w => ratioAt c w c') w₀ :=
  tendsto_finsetProd _ fun k _ =>
    ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_ratioPoly {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (ratioAt c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_ratioAt hc i)

end Values

theorem val_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  intro X Ω _ ξ K _ J _ y hall hT z₀ w₀ h₀ a hw ha
  choose c hc using hw.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hch := in_chart h₀ hw hc'
  obtain ⟨P, Q, t, ht, hQ, hPQ⟩ := exists_frac hT hch ha
  have hvQ := val_ratioPoly (hall _) hw hc' Q
  have hvt : ValAt ξ z₀ (MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)
      ((Scheme.stalkClosedPointTo z₀).hom t) := ⟨h₀, t, hQ, rfl⟩
  have hne : MvPolynomial.aeval (ratioAt c w₀) Q ≠ 0 := by
    rw [val_unique hT.gen hvQ hvt]
    exact (ht.map (Scheme.stalkClosedPointTo z₀).hom).ne_zero
  have hQa : MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q ≠ (0 : Ω) := by
    rw [← hQ]
    exact (ht.map (genMap ξ _)).ne_zero
  have haeq : a = MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P *
      (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)⁻¹ := by
    rw [← hPQ, mul_inv_cancel_right₀ hQa]
  refine ⟨fun w => MvPolynomial.aeval (ratioAt c w) P / MvPolynomial.aeval (ratioAt c w) Q,
    (continuousAt_ratioPoly hc' P).div (continuousAt_ratioPoly hc' Q) hne,
    {w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (ratioAt c w) Q ≠ 0}, ?_, ?_⟩
  · have e1 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 w₀, ∀ k, w ⟨k, c k⟩ ≠ 0 :=
      eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
    exact e1.and ((continuousAt_ratioPoly hc' Q).eventually_ne hne)
  · rintro z w ⟨h1, h2⟩ hwz
    rw [haeq]
    show ValAt ξ z _ (_ / _)
    rw [div_eq_mul_inv]
    exact val_mul (val_ratioPoly (hall _) hwz h1 P) (val_inv₀ h2 (val_ratioPoly (hall _) hwz h1 Q))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

namespace OpenNear

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {T : Type} (s : Finset T) {a : T → Ω} {r : T → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem val_aeval {κ : Type} {a : κ → Ω} {r : κ → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i, ValAt ξ z (a i) (r i)) (P : MvPolynomial κ ℤ) :
    ValAt ξ z (MvPolynomial.aeval a P) (MvPolynomial.aeval r P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_int hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (h i)

theorem genMap_germ {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) (p : Cpt ξ) (hp : p.1 ∈ W) :
    genMap ξ p (X.presheaf.germ W p.1 hp Q) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
  have h2 : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ W p.1 hp Q) =
      X.presheaf.germ W (genPt ξ) hW Q := by
    rw [← h]; rfl
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem isUnit_germ_iff (hξ : IsCptGen ξ) {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) {z : Sp ℂ ⟶ X}
    (hz : centre z ∈ W) {v : ℂ}
    (hv : ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q)) v) :
    IsUnit (X.presheaf.germ W (centre z) hz Q) ↔ v ≠ 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  have hs' : s = X.presheaf.germ W (centre z) hz Q :=
    hξ.inj ⟨centre z, h⟩ (hs.trans (genMap_germ hW Q ⟨centre z, h⟩ hz).symm)
  subst hs'
  have := Scheme.isLocalHom_stalkClosedPointTo' z
  constructor
  · exact fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero
  · exact fun hv => (isUnit_map_iff (Scheme.stalkClosedPointTo z).hom _).1 (isUnit_iff_ne_zero.2 hv)

def segreRatio {K : Type} [Fintype K] {J : K → Type} (c : (k : K) → J k) (w : (Σ k, J k) → ℂ)
    (c' : (k : K) → J k) : ℂ := ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_segreRatio {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X}
    {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_prod _ hz fun k _ => ?_
  obtain ⟨r, hr, hr'⟩ := (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).2 (c' k)
  rw [hr', mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem continuousAt_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ContinuousAt (fun w => segreRatio c w c') w₀ := by
  refine tendsto_finsetProd _ fun k _ => ?_
  exact ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_aeval_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (segreRatio c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_segreRatio hc i)

end OpenNear


open OpenNear in
theorem open_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (U : X.Opens), CoordsAt ξ y z₀ w₀ → centre z₀ ∈ U →
      ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → centre z ∈ U := by
  intro X Ω _ ξ K _ J _ y hgen ht z₀ w₀ U hw₀ hU
  choose c hc using hw₀.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hin₀ := in_chart (hgen (centre z₀)) hw₀ hc'
  obtain ⟨W, hWa, hW⟩ := ht.affine c hin₀.1
  have hz₀W : centre z₀ ∈ W := (hW _).2 ⟨hgen _, hin₀⟩
  obtain ⟨Q, hQU, hQ₀⟩ := hWa.exists_basicOpen_le (V := U) ⟨centre z₀, hU⟩ hz₀W
  have hgW : genPt ξ ∈ W := (hgen _).mem_open W.isOpen hz₀W
  have hreg : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q) ∈
      Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    rw [ht.ring c hin₀.1]
    intro p hp
    exact ⟨X.presheaf.germ W p.1 ((hW _).2 ⟨p.2, hp⟩) Q, OpenNear.genMap_germ hgW Q p _⟩
  rw [Algebra.adjoin_range_eq_range_aeval] at hreg
  obtain ⟨P, hP⟩ := hreg
  have hval : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → (∀ k, w ⟨k, c k⟩ ≠ 0) →
      ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q))
        (MvPolynomial.aeval (segreRatio c w) P) := by
    intro z w hw hcw
    rw [← hP]
    exact val_aeval (hgen _) (val_segreRatio (hgen _) hw hcw) P
  have hne₀ : MvPolynomial.aeval (segreRatio c w₀) P ≠ 0 :=
    (isUnit_germ_iff ht.gen hgW Q hz₀W (hval z₀ w₀ hw₀ hc')).1
      ((Scheme.mem_basicOpen X Q _ hz₀W).1 hQ₀)
  refine ⟨{w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (segreRatio c w) P ≠ 0}, ?_, ?_⟩
  · refine Filter.Eventually.and ?_ ((continuousAt_aeval_segreRatio hc' P).eventually_ne hne₀)
    exact Filter.eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
  · rintro z w ⟨hcw, hne⟩ hw
    have hzW : centre z ∈ W := (hW _).2 ⟨hgen _, in_chart (hgen _) hw hcw⟩
    exact hQU ((Scheme.mem_basicOpen X Q _ hzW).2
      ((isUnit_germ_iff ht.gen hgW Q hzW (hval z w hw hcw)).2 hne))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.val_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.coords_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem eq_of_germ_comp {R : Type} [CommRing R] [IsLocalRing R] {z z' : Spec (CommRingCat.of R) ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (h : z (IsLocalRing.closedPoint R) ∈ U)
    (h' : z' (IsLocalRing.closedPoint R) ∈ U)
    (e : X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo z =
      X.presheaf.germ U _ h' ≫ Scheme.stalkClosedPointTo z') : z = z' := by
  have key : ∀ (t : Spec (CommRingCat.of R) ⟶ X) (ht : t (IsLocalRing.closedPoint R) ∈ U),
      t = Spec.map (X.presheaf.germ U _ ht ≫ Scheme.stalkClosedPointTo t) ≫ hU.fromSpec := by
    intro t ht
    rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk ht]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t).symm
  rw [key z h, key z' h', e]

theorem val_int {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) {A : Type} (s : Finset A) (f : A → Ω) (g : A → R)
    (h : ∀ i ∈ s, ValAt ξ z (f i) (g i)) : ValAt ξ z (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.ArchB.val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact RootHt.ArchB.val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique


open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  intro X Ω _ ξ K _ J y T _ hall z z' w hz hz'
  have hξ := T.gen
  have h := hall (centre z)
  have h' := hall (centre z')
  choose c hc using hz.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have in1 := RootHt.ArchB.in_chart (c := c) h hz hc0
  have in2 := RootHt.ArchB.in_chart (c := c) h' hz' hc0
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T in1 in2
  have hxc : x c ≠ 0 := in1.1
  obtain ⟨U, hU, hUm⟩ := T.affine c hxc
  have hzU : centre z ∈ U := (hUm _).2 ⟨h, in1⟩
  have hzU' : centre z' ∈ U := (hUm _).2 ⟨h', in2⟩

  have hval : ∀ (t : Spec (CommRingCat.of ℂ) ⟶ X), CoordsAt ξ y t w → ∀ (k : K) (i : J k),
      ValAt ξ t (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro t ht k i
    obtain ⟨-, h2⟩ := ht.2 k (c k) (hc k)
    obtain ⟨r, hr, e⟩ := h2 i
    rw [e, mul_div_assoc, div_self (hc0 k), _root_.mul_one]
    exact hr
  have hrat : ∀ j : (k : K) → J k, x j / x c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ := fun j => by
    rw [hx]
    exact (Finset.prod_div_distrib _ _).symm
  have key : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ r : ℂ, ValAt ξ z a r ∧ ValAt ξ z' a r := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      refine ⟨∏ k, w ⟨k, j k⟩ / w ⟨k, c k⟩, ?_, ?_⟩
      · simp only [hrat]
        exact val_prod h _ _ _ fun k _ => hval z hz k (j k)
      · simp only [hrat]
        exact val_prod h' _ _ _ fun k _ => hval z' hz' k (j k)
    | algebraMap n =>
      refine ⟨(n : ℂ), ?_, ?_⟩
      · simpa using val_int h n
      · simpa using val_int h' n
    | add a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r + s, RootHt.ArchB.val_add h1 h3, RootHt.ArchB.val_add h2 h4⟩
    | mul a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r * s, RootHt.ArchB.val_mul h1 h3, RootHt.ArchB.val_mul h2 h4⟩
  refine eq_of_germ_comp hU hzU hzU' ?_
  ext s
  have hgm : ∀ (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U),
      genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) :=
    fun p q hp hq => GlobalTheory.CompanionTheory.Ar.genMap_germ_eq_genMap_germ ξ U p q hp hq s
  have ha : genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    refine (T.ring c hxc _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hUm _).2 ⟨p.2, hp⟩
    rw [hgm ⟨centre z, h⟩ p hzU hpU]
    exact ⟨_, rfl⟩
  obtain ⟨r, h1, h2⟩ := key _ ha
  have e1 : ValAt ξ z (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hzU s)) := ⟨h, _, rfl, rfl⟩
  have e2 : ValAt ξ z' (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z').hom (X.presheaf.germ U (centre z') hzU' s)) :=
    ⟨h', _, (hgm ⟨centre z', h'⟩ ⟨centre z, h⟩ hzU' hzU), rfl⟩
  exact (RootHt.ArchB.val_unique hξ e1 h1).trans (RootHt.ArchB.val_unique hξ h2 e2)
end
