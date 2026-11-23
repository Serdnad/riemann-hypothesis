module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle200
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle150
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle201
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle199
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle202
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lie_model_action_specialize : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (F : Type) [Field F] (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) (W : Type) [AddCommGroup W] [Module F W] (Mz : LieModel G z W) (A : Type) [CommRing A] (act : OAct A G) (ρ : A →+* Module.End Ω V) (ρz : A →+* Module.End F W) (K : Type) [Field K] (inc : K →+* Ω) (βF : K →+* F) (σ : A →+* K) (n : ℕ) (e : Fin n → A) (cf : Fin n → K) (r : ℕ) (b : Fin r → V), IsCptGen ξ → Smooth G.hom → M.IsActOf act.act ρ → Mz.IsActOf act.act ρz → (∀ k : K, ValAt ξ z (inc k) (βF k)) → ∑ k, cf k * σ (e k) = 1 → (∀ (a : A) (w : V), ρ a (∑ k, inc (cf k) • ρ (e k) w) = inc (σ a) • ∑ k, inc (cf k) • ρ (e k) w) → (M.eigLat ρ (inc.comp σ)).IsFrameAt b ⟨centre z, h⟩ → ∃ u : Fin r → W, (∀ i, M.ValAt z (b i) (Mz.pt (u i))) ∧ Submodule.span F (Set.range u) = eigSp ρz (βF.comp σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span | exact GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span | (intros; apply GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | exact GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Good

theorem coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem join_blocks {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {M : ℕ} (y₂ : (Σ _ : Unit, Fin M) → Ω) (hy : IsRelevant (mCoordIdeal y))
    (h₂ : ∃ i, y₂ ⟨(), i⟩ ≠ 0) : ∀ k, ∃ i, joinVec y y₂ ⟨k, i⟩ ≠ 0 := by
  rintro (k | u)
  · obtain ⟨i, hi⟩ := hy k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  · obtain ⟨i, hi⟩ := h₂
    exact ⟨i, hi⟩

theorem exists_good_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  intro hRes K _ ι _ Ω _ _ y e β b hV hβ hβP
  obtain ⟨M, y₂, J, ⟨i₀, hi₀⟩, hfield, hJh, hJ, hsnc, hz⟩ :=
    GlobalTheory.T.adjoin_coords_arith_var hRes K ι Ω y e β b hV hβ hβP
  have hj := (GlobalTheory.T.block_join_inclusions_compat).1 K ι Unit (fun _ => Fin M) Ω y y₂
  have hb₁ := hj.1
  have hcomp : joinVec y y₂ ∘ joinInl ι (fun _ : Unit => Fin M) = y := hj.2.2.1
  have hblocks := join_blocks y y₂ hV.2.1.2.2 ⟨i₀, hi₀⟩
  have harith : IsArithVar (mCoordIdeal (joinVec y y₂)) (e + 1) := by
    refine GlobalTheory.T.isArithVar_of_block_algebraic K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y₂) (e + 1) hb₁ hblocks ?_ ?_
    · rw [hcomp]; exact hV
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y₂) e J
    harith hJh hJ hsnc
  obtain ⟨Amp, h₁, h₂, h₃⟩ := GlobalTheory.T.embedded_resolution_ample_metric (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M)
    (mCoordIdeal (joinVec y y₂)) J e R hR
  exact ⟨K ⊕ Unit, inferInstance, joinIdx ι fun _ : Unit => Fin M, inferInstance, Sum.inl,
    joinInl ι fun _ : Unit => Fin M, joinVec y y₂, J, R, Amp, hb₁, hcomp, hfield, harith, hR, h₁, h₂, h₃, hz⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.Good
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | exact GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left :=
  PositivityTheory.Xgn.framed_point_specialization
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

section Curve

variable {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {z : Fin n → ℂ}

def diagLine (z : Fin n → ℂ) (T : ℂ) : Fin n → ℂ := fun i => z i + T

theorem diagLine_zero (z : Fin n → ℂ) : diagLine z 0 = z := by
  funext i; simp [diagLine]

theorem diagLine_mem_ball (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {T : ℂ}
    (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : diagLine z T ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hT ⊢
  rw [pi_norm_lt_iff one_pos]
  intro i
  have h₁ := norm_le_pi_norm z i
  calc ‖z i + T‖ ≤ ‖z i‖ + ‖T‖ := norm_add_le _ _
    _ < 1 := by linarith

theorem analyticOnNhd_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticOnNhd ℂ (fun T => ψ (diagLine z T) x) (Metric.ball (0 : ℂ) (1 - ‖z‖)) := by
  have hl : DifferentiableOn ℂ (diagLine z) (Metric.ball (0 : ℂ) (1 - ‖z‖)) :=
    (differentiable_pi.2 fun i => (differentiable_const (z i)).add differentiable_id).differentiableOn
  exact ((h.2 x).comp hl fun T hT => diagLine_mem_ball hz hT).analyticOnNhd Metric.isOpen_ball

theorem zero_mem_ball_norm (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 - ‖z‖) := by
  have := mem_ball_zero_iff.1 hz
  simpa using this

theorem analyticAt_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticAt ℂ (fun T => ψ (diagLine z T) x) 0 :=
  analyticOnNhd_diagLine h hz x 0 (zero_mem_ball_norm hz)

def taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : R →+* PowerSeries ℂ where
  toFun x := Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x)
  map_one' := by
    simp only [map_one]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_one]
  map_zero' := by
    simp only [map_zero]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
  map_mul' x y := by
    simp only [map_mul]
    exact Formalism.L2.Th1.F.Taylor.taylor0_mul (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)
  map_add' x y := by
    simp only [map_add (f := _)]
    exact Formalism.L2.Th1.F.Taylor.taylor0_add (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)

theorem constantCoeff_comp_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (PowerSeries.constantCoeff (R := ℂ)).comp (taylorHom h hz) = ψ z := by
  ext x
  have e := Formalism.L2.Th1.F.Taylor.coeff_taylor0 (fun T => ψ (diagLine z T) x) 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, diagLine_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
  exact e

theorem eq_zero_of_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {x : R}
    (hx : taylorHom h hz x = 0) {T : ℂ} (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : ψ (diagLine z T) x = 0 := by
  have h₀ : Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x) = Formalism.L2.Th1.F.taylor0 (fun _ => (0 : ℂ)) := by
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
    exact hx
  have he := Formalism.L2.Th1.F.Taylor.taylor0_inj (analyticAt_diagLine h hz x) analyticAt_const h₀
  exact (analyticOnNhd_diagLine h hz x).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected (zero_mem_ball_norm hz) he hT

theorem exists_diagLine_mem_punct (a : ℕ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    ∃ T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖), diagLine z T ∈ punct n a 1 := by
  have hinf : (Metric.ball (0 : ℂ) (1 - ‖z‖)).Infinite :=
    infinite_of_mem_nhds 0 (Metric.isOpen_ball.mem_nhds (zero_mem_ball_norm hz))
  obtain ⟨T, hT, hn⟩ := hinf.exists_notMem_finset (Finset.univ.image fun i : Fin n => -z i)
  refine ⟨T, hT, diagLine_mem_ball hz hT, fun i _ he => hn ?_⟩
  refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
  have : z i + T = 0 := he
  linear_combination -this

end Curve

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem range_jK_taylorHom_subset {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a)
    {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    Set.range (Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz)) ⊆ Set.range C.j := by
  have := C.j_open
  rintro _ ⟨q, rfl⟩
  obtain ⟨T, hT, hp⟩ := exists_diagLine_mem_punct a hz
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hw : spMap (C.ψ (diagLine z T)) s ∈ Set.range C.j :=
    ⟨C.pt (diagLine z T) s, by rw [← (C.pt_eq _ hp).1, Scheme.Hom.comp_apply]⟩
  refine Specializes.mem_open ?_ C.j.isOpenEmbedding.isOpen_range hw
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  rw [Scheme.Hom.comp_apply] at hx
  have h₁ : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (taylorHom C.hol hz x) ∈ q.asIdeal := hx
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h₁
  have h₂ : C.ψ (diagLine z T) x = 0 := eq_zero_of_taylorHom C.hol hz h₁ hT
  show C.ψ (diagLine z T) x ∈ s.asIdeal
  rw [h₂]
  exact Ideal.zero_mem _

section Pulled

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem polAt_of_pulled {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K : Type} [Field K] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : Out.RelAmple u.G u.PP.L)
    (hk : Out.KTriv u.G u.PP.L) (j' : Sp K ⟶ S') (h : j' ≫ f = j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K)) (p : Sp K ⟶ S) (_ : p = 𝟙 _ ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (𝟙 _ ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ (h.trans (Category.id_comp _).symm) n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (𝟙 _ ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

end Pulled

theorem exists_curve_through_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  intro E _ _ _ H D l Xo σ n a C z hz
  have := C.j_open
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (taylorHom C.hol hz)) C.t
  have hc : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
    ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  have hsurj : Function.Surjective (PowerSeries.constantCoeff (R := ℂ)) := fun c =>
    ⟨PowerSeries.C c, by simp⟩
  refine ⟨PowerSeries ℂ, inferInstance, inferInstance, inferInstance, taylorHom C.hol hz,
    PowerSeries.constantCoeff (R := ℂ), _, m, hc, hsurj, ?_, constantCoeff_comp_taylorHom C.hol hz, ?_⟩
  · have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  · have hr := range_jK_taylorHom_subset C hz
    let y := IsOpenImmersion.lift C.j _ hr
    have hy : y ≫ C.j = Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz) := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y C.tV
    obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
    obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
    exact polAt_of_pulled m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (Out.jK (PowerSeries ℂ)) hy.symm

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_comp_comparison_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverLie.main | exact GlobalTheory.CompanionTheory.Ar.CoverLie.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverLie.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_iso_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | exact GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.coord_degree_bound_of_flag : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ ((vf j).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (f j)).left)) ∧
        M.ValAt _ e ve ∧ (ve.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt s).left) ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | exact GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem _root_.GlobalTheory.T.component_point_cm_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap βF → Set.range y ⊆ U → ∀ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (n : ℕ) (b : Fin n → Z.V), (Z.eig σ).IsFrameAt b ⟨_, h⟩ → ∃ v : Vecs y n, IsValFam Z y b v ∧ IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c σ)) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem lieValAt_spMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (hξ : IsCptGen ξ) {F F' : Type} [Field F]
    [Field F'] (f : F →+* F') {z : Sp F ⟶ X} {z' : Sp F' ⟶ X} (hz : spMap f ≫ z = z') {e : V}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : M.ValAt z e w) :
    M.ValAt z' e w' := by
  letI : Algebra F F' := f.toAlgebra
  subst hz
  obtain ⟨hc, v, hext, hw0⟩ := h
  have hbot : ∀ x : PrimeSpectrum F, x.asIdeal = ⊥ := fun x =>
    (Ideal.eq_bot_or_top _).resolve_right x.isPrime.ne_top
  have hp : (spMap f) (IsLocalRing.closedPoint F') = IsLocalRing.closedPoint F :=
    PrimeSpectrum.ext ((hbot _).trans (hbot _).symm)
  have hcen : GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) = GlobalTheory.CompanionTheory.Ar.centre z := by
    change z ((spMap f) (IsLocalRing.closedPoint F')) = z (IsLocalRing.closedPoint F)
    rw [hp]
  have hc' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) := hcen ▸ hc
  exact GlobalTheory.CompanionTheory.Ar.LieFib.valAt_base M z hc hc' v hext w' w hw hw0

theorem isValFam_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) (y' : Sp F' ⟶ Xo.XF c), y' = spMap f ≫ y → ∀ (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (v' : Vecs y' n), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsValFam Z y b v → IsValFam Z y' b v' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F F' _ _ f y y' hy n b v v' hv' hv
  subst hy
  simp only [GlobalTheory.CompanionTheory.Ar.Flat.Rep.IsValFam] at hv ⊢
  intro i
  obtain ⟨u, hval, t, ht1, ht2, ht3⟩ := hv i
  have hzz : spMap f ≫ (y ≫ Y.j) = (spMap f ≫ y) ≫ Y.j := (Category.assoc _ _ _).symm
  refine ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase f hzz ≫ u, ?_, ?_⟩
  · exact lieValAt_spMap Z.M Z.gen f hzz rfl hval
  · simp only [GlobalTheory.CompanionTheory.Ar.Flat.SameVec]
    refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ t, ?_, ?_, ?_⟩
    · rw [Category.assoc, ht1]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_alg, Category.assoc]
    · rw [Category.assoc, ht2, hv' i]
    · rw [Category.assoc, ht3]
      try rfl

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end
