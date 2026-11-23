module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle262
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameTotalBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle263
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.all_weight_sections_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (Z : Comp Xo c), secZ Xo c a = GlobalTheory.AllWt.secZ Xo c (exZ Dw a) ∧ cuspZ Xo c U a = GlobalTheory.AllWt.cuspW Xo c U (a, 0) ∧ cuspOn U h a Z = GlobalTheory.AllWt.cuspOn U Z (a, 0) ∧ (∀ f : GlobalTheory.AllWt.cuspOn U Z (a, 0), f ∈ GlobalTheory.AllWt.latOn U Z (a, 0) ↔ (f : Rul Xo c) ∈ latOn U h a Z) ∧ ∀ σ, GoodEmb c σ → ∀ k, ∀ y ∈ ((U σ).X k).dom, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z ↔ Over (U σ) (e Z) k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.bridge_allWt | exact GlobalTheory.CompanionTheory.Ar.Rec.bridge_allWt | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.bridge_allWt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem coordsAt_torusSmul {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) {a : K → ℂ} (ha : ∀ k, a k ≠ 0) : CoordsAt ξ y z (torusSmul a w) := by
  have hs : ∀ q : Σ k, J k, torusSmul a w q = a q.1 * w q := fun q => rfl
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 k
    refine ⟨c, ?_⟩
    rw [hs]
    exact (isUnit_iff_ne_zero.2 (ha k)).mul hc
  · have hc' : IsUnit (w ⟨k, c⟩) := by
      rw [hs] at hc
      exact isUnit_of_mul_isUnit_right hc
    obtain ⟨hy, hv⟩ := h.2 k c hc'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, hr, he⟩ := hv i
    refine ⟨r, hr, ?_⟩
    rw [hs, hs]
    show a k * w ⟨k, i⟩ = r * (a k * w ⟨k, c⟩)
    rw [he]
    ring

theorem valAt_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R}
    (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

theorem isCMFam_of_labVal (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X}
    {σ : CMType H → (𝓞 E →+* ℂ)} (hL : Or.𝔐.LabVal z Or.sm σ) : IsCMFam σ := by
  obtain ⟨σ₀, h0, -, -, -, -, hcm⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hs : ∀ τ, σ τ = σ₀ (Or.sm τ) := fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL τ a) (h0 (Or.sm τ) a)
  obtain ⟨h1, h2, -⟩ := hcm (RingHom.id ℂ)
  have he : σ = fun τ => σ₀ (Or.sm τ) := funext hs
  rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · rw [he, h]
    exact h2
  · rw [he, h]
    exact h1

theorem eq_cuspW_of_fibre (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ} (hU : Or.𝔐.IsCuspWeight Or.sm U)
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hz : Or.𝔐.Interior z)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {σ : CMType H → (𝓞 E →+* ℂ)}
    (hF : FibreLat Or.𝔐.t z R) (hL : Or.𝔐.LabVal z Or.sm σ) : U w = R.cuspW σ := by
  obtain ⟨g', Λ', i₁, i₂, R', σ', hF', hL', he⟩ := hU z w hw hz
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.T.fibre_lattice_linear_equiv E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  rw [he]
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm

theorem cuspWeight_torus_and_sheets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q U hU
  refine ⟨fun w hw w' hw' => ?_, fun m t ht => ?_⟩
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hw.1
    have hI : Or.𝔐.Interior z := by
      by_contra hn
      exact hw.2 ((Or.bd z w hz).2 hn)
    obtain ⟨u, hu, a, ha, rfl⟩ := hw'
    rw [show u = w from hu]
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU z w hz hI
    rw [he]
    exact eq_cuspW_of_fibre Or hU (coordsAt_torusSmul Or.𝔐.ξ hz ha) hI R hF hL
  · obtain ⟨z, hz, hI, hF, hL⟩ := Q.fibre m t ht
    exact eq_cuspW_of_fibre Or hU hz hI _ hF hL

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx

theorem not_inFibre_centre {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
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

theorem posDef_of_dual {V : Type} [AddCommGroup V] [Module ℂ V] (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) {N : ℕ} (x : Fin N → V)
    (g : Fin N → V →ₗ[ℂ] ℂ) (hg : ∀ j k, g j (x k) = if j = k then 1 else 0) :
    (Matrix.of fun p q => h (x p) (x q)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨Matrix.IsHermitian.ext fun p q => ?_, fun c hc => ?_⟩
  · simp only [Matrix.of_apply]
    rw [hh (x p) (x q)]
    simp
  · set u : V := ∑ k, c k • x k with hu
    have e : star c ⬝ᵥ (Matrix.of fun p q => h (x p) (x q)).mulVec c = h u u := by

      simp only [hu, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, dotProduct, Matrix.mulVec,
      Matrix.of_apply, Finset.mul_sum, Pi.star_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [RCLike.star_def]
      ring
    have hu0 : u ≠ 0 := fun h0 => hc (funext fun j => by
      have := congrArg (g j) h0

      simpa [hu, map_sum, hg, Finset.sum_ite_eq] using this)
    rw [e, Complex.pos_iff]
    refine ⟨hp u hu0, ?_⟩
    have := (Complex.conj_eq_iff_im.1 (hh u u).symm)
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_dual_sum (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li,
      (∀ j k, π j ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) = if j = k then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hspan⟩ := hfr
  have hdis : Disjoint (𝔐.Vgen a ⊔ 𝔐.Vgen b) (⨆ s ∈ ({a, b} : Set (CMType H ⊕ CMType H))ᶜ, 𝔐.Vgen s) :=
    (hind.disjoint_biSup_biSup (s := {a, b}) (t := {a, b}ᶜ) disjoint_compl_right).mono_left
      (sup_le (le_biSup 𝔐.Vgen (by simp)) (le_biSup 𝔐.Vgen (by simp)))
  obtain ⟨C, hC, hc⟩ := hdis.symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.projectionOnto _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ w : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (w : 𝔐.Li) = w := fun w =>
    Submodule.projectionOnto_apply_left hc.symm w
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases hs : s' ∈ ({a, b} : Set (CMType H ⊕ CMType H))
      · have hxW : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases hs with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases hs with rfl | rfl
          · rw [hV s']; exact Submodule.mem_sup_left hx
          · rw [hV s']; exact Submodule.mem_sup_right hx
        have hm : (⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) q := hxV
        rw [hspan] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show x = ((⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) from rfl, hpr, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k

        simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        refine sum_mem fun k _ => mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxC : x ∈ C := hC (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem hs hx.2))
        have : pr x = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hxC
        simp [this]
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy

theorem exists_gramAt_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z hgen hpol hfr
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_centre hgen hr
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨f, hHI, hh, hp⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z Vz MR hpol
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sum 𝔐 hind ⟨centre z, hgen⟩ hV hlat a b bb hfr
  have hbL : ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, hgen⟩ := fun k => by
    have hm : bb k ∈ (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) ⟨centre z, hgen⟩ := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    have hm' : ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.V a ⟨centre z, hgen⟩ ⊔ 𝔐.V b ⟨centre z, hgen⟩ := hm
    rw [hV, hV] at hm'
    refine (sup_le ?_ ?_ : 𝔐.dR a ⟨centre z, hgen⟩ ⊔ 𝔐.dR b ⟨centre z, hgen⟩ ≤ 𝔐.M.lat ⟨centre z, hgen⟩) hm'
    · exact fun x hx => hx.1
    · exact fun x hx => hx.1
  have hval : ∀ k, ∃ x : Vz, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt x) := fun k => by
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff z _).2 ⟨hgen, hbL k⟩
    obtain ⟨x, rfl⟩ := MR.onto w hw.isTanAt
    exact ⟨x, hw⟩
  choose x hx using hval
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (x k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg _ _ _ (hx k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact CxVal.one hgen
    · exact ⟨hgen, 0, map_zero _, map_zero _⟩
  choose g hg using hg
  exact ⟨Matrix.of fun p q => f (x p) (x q), ⟨fun k => MR.pt (x k), hx, fun p q => (hHI _ _ _).2 rfl⟩,
    posDef_of_dual f hh hp x g hg⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.root_origin_frame_total_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q → p ∈ SS → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → ∃ κz : T.V, FinRd.Roots.lieEig Or MC ρC σ ≤ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC ∧ (∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC, κz • w ∈ FinRd.Roots.lieEig Or MC ρC σ) ∧ FinRd.absT p la T e (algebraMap T.V T.Fr κz) = (p : ℝ) ^ (-Small.htExp p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie.lieEig_htDual | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie.lieEig_htDual | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie.lieEig_htDual <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_model_prime_bound : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main | exact GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_comp_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes <;> assumption)
end
