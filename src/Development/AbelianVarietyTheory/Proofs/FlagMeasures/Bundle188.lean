module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle166
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IsoCount

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem isTraceDef_of_pd (H : HermSpace K V) (hp : GlobalTheory.Mass.PD H.B.flip) : IsTraceDef H := by
  intro x hx
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := H.B x x)
  have h2 : (0 : ℝ) < (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re := by
    have : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
    rw [h1, Complex.re_sum]
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) Finset.univ_nonempty
  have h3 : (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re = ((Algebra.trace ℚ K (H.B x x) : ℚ) : ℝ) := by
    simp
  rw [h3] at h2
  exact_mod_cast h2

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def fixAut (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {η | η ∈ isomGrp H ∧ imLat η L = L ∧ ∀ y ∈ U, η y = y}
  one_mem' := ⟨(isomGrp H).one_mem, Formalism.HermitianLatticesTheory.genusBasic_gmap_one L, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, haL, haU⟩ ⟨hb, hbL, hbU⟩
    refine ⟨mul_mem ha hb, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, hbL, haL]
    · show a (b y) = y
      rw [hbU y hy, haU y hy]
  inv_mem' := by
    rintro a ⟨ha, haL, haU⟩
    refine ⟨inv_mem ha, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv a L
      rwa [haL] at this
    · show a.symm y = y
      rw [LinearEquiv.symm_apply_eq, haU y hy]


omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem map_eq_of_fix {U : Submodule K V} {g : V ≃ₗ[K] V} (h : ∀ y ∈ U, g y = y) :
    U.map (g : V →ₗ[K] V) = U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g : V →ₗ[K] V) x = x := h x hx
    rw [this]; exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

def toQuot (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) :
    fixAut H U L →* ((V ⧸ U) ≃ₗ[K] (V ⧸ U)) :=
  MonoidHom.mk' (fun g => Submodule.Quotient.equiv U U g.1 (map_eq_of_fix g.2.2.2)) (by
    intro a b
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl)

theorem toQuot_mk (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) (g : fixAut H U L)
    (x : V) : toQuot H U L g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g.1 x) := rfl

theorem toQuot_injective {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    (L : Submodule (𝓞 K) V) : Function.Injective (toQuot H U L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  ext x
  have h1 : Submodule.Quotient.mk (p := U) (g.1 x) = Submodule.Quotient.mk x := by
    rw [← toQuot_mk, hg]; rfl
  have hu : g.1 x - x ∈ U := (Submodule.Quotient.eq U).1 h1
  have h2 := (mem_isomGrp H g.1).1 g.2.1 x (g.1 x - x)
  rw [g.2.2.2 _ hu] at h2
  have h3 : H.B (g.1 x - x) (g.1 x - x) = 0 := by
    rw [map_sub H.B, LinearMap.sub_apply, h2, sub_self]
  by_contra hne
  have h4 := hH (g.1 x - x) (sub_ne_zero.2 hne)
  rw [h3, map_zero] at h4
  exact lt_irrefl _ h4

variable [FiniteDimensional K V]

theorem fixAut_finite {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) : (fixAut H U L : Set (V ≃ₗ[K] V)).Finite :=
  (autCard_eq_natCard hH hL).1.subset fun _ hg => ⟨hg.1, hg.2.1⟩

theorem card_fixAut_dvd (hM : MinkowskiBound) {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) :
    Nat.card (fixAut H U L) ∣ minkowskiM (Module.finrank ℚ K * Module.finrank K (V ⧸ U)) := by
  have hfin : Finite (fixAut H U L) := (fixAut_finite hH U hL).to_subtype
  have e := MonoidHom.ofInjective (toQuot_injective hH U L)
  rw [Nat.card_congr e.toEquiv]
  refine GlobalTheory.AutLattice.card_dvd_minkM hM K (V ⧸ U) (L.map (U.mkQ.restrictScalars (𝓞 K)))
    (hL.toIsLattice.fg.map _) ?_ _ (Finite.of_equiv _ e.toEquiv) ?_
  · have : ((L.map (U.mkQ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) (V ⧸ U)) : Set (V ⧸ U))
        = U.mkQ '' (L : Set V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  · rintro _ ⟨g, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨g.1 x, ?_, rfl⟩
    have h := g.2.2.1
    have h' : g.1 x ∈ imLat g.1 L := ⟨x, hx, rfl⟩
    rwa [h] at h'

end

theorem isoCnt : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hp U L L' hL _
  have hH := isTraceDef_of_pd H hp
  set S := {η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨η, hη, hηL, hηU⟩
  · rw [h0]; simp
  have h1 : S.encard ≤ (fixAut H U L : Set (V ≃ₗ[K] V)).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun a => η⁻¹ * a) ?_ ?_
    · rintro a ⟨ha, haL, haU⟩
      refine ⟨mul_mem (inv_mem hη) ha, ?_, fun y hy => ?_⟩
      · unfold imLat at *
        rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, haL, ← hηL, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
      · show η.symm (a y) = y
        rw [LinearEquiv.symm_apply_eq, haU y hy, hηU y hy]
    · intro a _ b _ hab
      simpa using hab
  have hn : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h2
    rw [Formalism.HermitianLatticesTheory.fDeg, h2, IsTotallyComplex.finrank]
  have hq : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  have h2 := (card_fixAut_dvd hM hH U hL).trans (Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial _)
  have h3 := (Nat.le_of_dvd (Nat.factorial_pos _) h2).trans (Nat.factorial_le_pow _)
  have e : 2 * (Module.finrank ℚ K * Module.finrank K (V ⧸ U))
      = 4 * (Module.finrank K V - Module.finrank K U) * Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hn, hq]; ring
  rw [e] at h3
  have h4 : (fixAut H U L : Set (V ≃ₗ[K] V)).encard = (Nat.card (fixAut H U L) : ℕ∞) := by
    rw [← (fixAut_finite hH U hL).cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl
  rw [h4] at h1
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe]
  exact_mod_cast h3

end GlobalTheory.IsoCount
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

section Abstract

variable {G H L : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [CompleteSpace H] in
theorem inner_of_norm (A : H →L[ℂ] H) (hA : ∀ u, ‖A u‖ = ‖u‖) (x y : H) : ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := { toLinearMap := (A : H →ₗ[ℂ] H), norm_map' := hA }
  exact e.inner_map_map x y

theorem inner_intertwiners (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g u, ‖σ g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, σ g u ∈ S) → S = ⊥ ∨ S = ⊤)
    (R : G → (L →L[ℂ] L)) (hR : ∀ g u, ‖R g u‖ = ‖u‖) (w : H) (hw : ‖w‖ = 1)
    (T T' : H →L[ℂ] L) (hT : ∀ g, T.comp (σ g) = (R g).comp T) (hT' : ∀ g, T'.comp (σ g) = (R g).comp T')
    (u u' : H) : ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ := by
  have hinv : ∀ g (v : H), σ g (σ g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  have hSin : ∀ v x, ⟪v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ = ⟪T v, T' x⟫_ℂ := by
    intro v x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have hcomm : ∀ g, (ContinuousLinearMap.adjoint T) ∘L T' * σ g = σ g * ((ContinuousLinearMap.adjoint T) ∘L T') := by
    intro g
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hSin]
    have h1 : T v = R g (T (σ g⁻¹ v)) := by
      have := congrArg (fun F : H →L[ℂ] L => F (σ g⁻¹ v)) (hT g)
      simp only [ContinuousLinearMap.comp_apply, hinv] at this
      exact this
    have h2 : T' (σ g x) = R g (T' x) := by
      have := congrArg (fun F : H →L[ℂ] L => F x) (hT' g)
      simpa only [ContinuousLinearMap.comp_apply] using this
    have h3 : ⟪v, σ g (((ContinuousLinearMap.adjoint T) ∘L T') x)⟫_ℂ
        = ⟪σ g⁻¹ v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ := by
      conv_lhs => rw [← hinv g v]
      exact inner_of_norm (σ g) (hσ g) _ _
    rw [h3, hSin, h1, h2, inner_of_norm (R g) (hR g)]
  obtain ⟨c, hc⟩ := GlobalTheory.schur_unitary_irreducible G H σ hσ hirr _ hcomm
  have key : ∀ a b, ⟪T a, T' b⟫_ℂ = c * ⟪a, b⟫_ℂ := by
    intro a b
    rw [← hSin, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  rw [key, key w w, hww, mul_one]


omit [CompleteSpace H] [CompleteSpace L] in
theorem exists_frame (V : Submodule ℂ (H →L[ℂ] L)) [FiniteDimensional ℂ V] (w : H)
    (hV : ∀ T ∈ V, ∀ T' ∈ V, ∀ u u', ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ) :
    ∃ T : Fin (Module.finrank ℂ V) → (H →L[ℂ] L), (∀ i, T i ∈ V) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧
      (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = V := by
  classical
  let Φ : V →ₗ[ℂ] L := (ContinuousLinearMap.apply ℂ L w : (H →L[ℂ] L) →ₗ[ℂ] L) ∘ₗ V.subtype
  have hΦ : ∀ T : V, Φ T = (T : H →L[ℂ] L) w := fun T => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun u => ?_
    have h := hV T T.2 T T.2 u u
    rw [← hΦ, hT, inner_zero_left, zero_mul] at h
    simpa using (inner_self_eq_zero.mp h)
  have hdim : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ V :=
    (LinearEquiv.ofInjective Φ hinj).finrank_eq.symm
  let b := (stdOrthonormalBasis ℂ (LinearMap.range Φ)).reindex (finCongr hdim)
  have he : ∀ x, (((LinearEquiv.ofInjective Φ hinj).symm x : V) : H →L[ℂ] L) w = (x : L) := by
    intro x
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective Φ hinj).apply_symm_apply x)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hin : ∀ i j u u', ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
      (((LinearEquiv.ofInjective Φ hinj).symm (b j) : V) : H →L[ℂ] L) u'⟫_ℂ
      = (if i = j then 1 else 0) * ⟪u, u'⟫_ℂ := by
    intro i j u u'
    rw [hV _ ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2 _ ((LinearEquiv.ofInjective Φ hinj).symm (b j)).2,
      he, he, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal i j]
  refine ⟨fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L),
    fun i => ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2, ?_, ?_, ?_⟩
  · intro i u
    have h : ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
        (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [hin]
      simp
    have h2 : ‖(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    nlinarith [norm_nonneg ((((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u), norm_nonneg u]
  · intro i j hij u u'
    rw [hin]
    simp [hij]
  · have hbasis : Submodule.span ℂ (Set.range fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) = ⊤ := by
      have := (b.toBasis.map (LinearEquiv.ofInjective Φ hinj).symm).span_eq
      rw [← this, Module.Basis.coe_map, OrthonormalBasis.coe_toBasis]
      rfl
    have hr : Set.range (fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L))
        = V.subtype '' Set.range (fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hbasis, Submodule.map_top, Submodule.range_subtype]

end Abstract

theorem exists_orthonormal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R → ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re := by
  intro B d hd hfin hle
  haveI := hfin
  obtain ⟨hU, hI, -, hw, -⟩ := GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree B d hd
  obtain ⟨h1, hmul, hnorm, -⟩ := hU
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := h1, map_mul' := fun a b => hmul a b }
  have hR := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.1
  have hirr : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ u ∈ S, σ g u ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hSinv
    have hI' : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ v ∈ S, B.σs g v ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
      simpa [IsIrr] using hI
    exact hI' S hS hSinv
  have hV : ∀ T ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ T' ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ u u',
      ⟪T u, T' u'⟫_ℂ = ⟪T (B.tens B.w), T' (B.tens B.w)⟫_ℂ * ⟪u, u'⟫_ℂ := by
    intro T hT T' hT' u u'
    exact inner_intertwiners σ (fun g u => hnorm g u) hirr (fun g => B.R (g, 1)) (fun g u => hR (g, 1) u)
      (B.tens B.w) hw T T' (fun g => hle hT g) (fun g => hle hT' g) u u'
  exact exists_frame (B.I.eHom B.σs B.μf B.fund B.R B.Re) (B.tens B.w) hV

end GlobalTheory.IntertwinerFrame
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.unipotentRadical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧ ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  first | exact @GlobalTheory.RadVol.radical_volume_growth | exact GlobalTheory.RadVol.radical_volume_growth | (intros; apply GlobalTheory.RadVol.radical_volume_growth <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.HtProd

theorem prod_shift_eq (N : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ b b', N ≤ b' → F b b' = 1) :
    ∏ c ∈ Finset.range N, ∏ b ∈ Finset.range N, F b (b + c + 1) =
      ∏ b ∈ Finset.range N, ∏ b' ∈ Finset.range N, if b < b' then F b b' else 1 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_filter]
  have h1 : ∏ c ∈ Finset.range N, F b (b + c + 1) = ∏ x ∈ Finset.Ico (b + 1) (b + 1 + N), F b x := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    omega
  rw [h1]
  symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
    exact hF _ _ (by omega)

theorem prod_range_split (a : ℕ) (g : ℕ → ℝ) :
    ∏ b ∈ Finset.range (2 * a + 1), g b = (∏ i : Fin a, g i) * g a * ∏ i : Fin a, g (2 * a - i) := by
  have e : 2 * a + 1 = (a + 1) + a := by omega
  rw [e, Finset.prod_range_add, Finset.prod_range_succ, Fin.prod_univ_eq_prod_range g a,
    Fin.prod_univ_eq_prod_range (fun i => g (2 * a - i)) a, ← Finset.prod_range_reflect (fun i => g (2 * a - i)) a]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  congr 1
  omega

theorem prod_symm_split {a : ℕ} (P : Fin a → Fin a → ℝ) (hP : ∀ i k, P i k = P k i) :
    ∏ i, ∏ k, P i k = (∏ i, ∏ k, if i < k then P i k else 1) ^ 2 * ∏ i, P i i := by
  have h1 : ∀ i k, P i k = (if i < k then P i k else 1) * (if k < i then P k i else 1) *
      (if i = k then P i k else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hP i k]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => h1 i k]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => if k < i then P k i else 1), sq]
  simp

theorem htProd : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ),
    (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i →
    (∀ b, 2 * a + 1 ≤ b → r b = 0) →
    (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) →
    h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) →
    ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1),
      h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  intro n f a j r τ h hr hra hr0 hτ ha h1
  rw [prod_shift_eq (2 * a + 1) (fun b b' => h b ^ r b' / h b' ^ r b)
    (fun b b' hb => by simp [hr0 b' hb, h1 b' hb])]
  unfold layerProd
  rw [← hra]
  simp only [prod_range_split, id]
  have c1 : ∀ i : Fin a, (i : ℕ) < a := fun i => i.2
  have c2 : ∀ i k : Fin a, (i : ℕ) < 2 * a - k := fun i k => by omega
  have c3 : ∀ k : Fin a, ¬ a < (k : ℕ) := fun k => by omega
  have c4 : ∀ k : Fin a, a < 2 * a - k := fun k => by omega
  have c5 : ∀ i k : Fin a, ¬ 2 * a - i < (k : ℕ) := fun i k => by omega
  have c6 : ∀ i : Fin a, ¬ 2 * a - i < a := fun i => by omega
  have c7 : ∀ i k : Fin a, (2 * a - i < 2 * a - k) ↔ k < i := fun i k => by
    rw [Fin.lt_def]; omega
  have c8 : ∀ i k : Fin a, ((i : ℕ) < k) ↔ i < k := fun i k => Iff.rfl
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, lt_irrefl, if_true, if_false, ha,
    fun i => (hr i).1, fun i => (hr i).2, fun i => (hτ i).2.1, fun i => (hτ i).2.2,
    Finset.prod_const_one, one_mul, mul_one, one_pow, div_one, Finset.prod_mul_distrib,
    Finset.prod_filter]
  have d1 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k)) ^ j i =
      (τ i / τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d2 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ i * τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d3 : ∀ i k : Fin a, (τ i ^ (2 * f * j i))⁻¹ ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ k / τ i) ^ (2 * j k * j i * f) := fun i k => by
    rw [← d1, inv_pow, inv_pow, div_inv_eq_mul, mul_comm, div_eq_mul_inv]
  have d4 : ∀ i : Fin a, (τ i ^ (2 * f * j i)) ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← pow_mul]
    congr 1
    ring
  have d5 : ∀ i : Fin a, 1 / (τ i ^ (2 * f * j i))⁻¹ ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← d4, inv_pow, one_div, inv_inv]
  have d6 : ∀ i : Fin a, (τ i * τ i) ^ (2 * j i * j i * f) = ((τ i ^ 2) ^ (j i ^ 2 * f)) ^ 2 := fun i => by
    rw [← sq, ← pow_mul (τ i ^ 2)]
    congr 1
    ring
  simp only [d1, d2, d3, d4, d5]
  rw [Finset.prod_comm (f := fun i k => if k < i then (τ k / τ i) ^ (2 * j k * j i * f) else 1),
    prod_symm_split (fun i k => (τ i * τ k) ^ (2 * j i * j k * f))
      (fun i k => by rw [mul_comm (τ i)]; congr 1; ring)]
  simp only [d6, Finset.prod_pow]
  ring

end GlobalTheory.HtProd
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselSchur_translated_matrixCoefficient : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  first | exact @GlobalTheory.SgInf.schur_translated_coef | exact GlobalTheory.SgInf.schur_translated_coef | (intros; apply GlobalTheory.SgInf.schur_translated_coef <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq : ∀ (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r)) (f g : Mat k r → B), IsHaarOn (GG k r) μG → ContinuousOn f (GG k r) → ContinuousOn g (GG k r) → (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x)) → ∀ x ∈ GG k r, f x = g x := by
  first | exact @GlobalTheory.SgInf.AeqCont.eqOn_of_ae | exact GlobalTheory.SgInf.AeqCont.eqOn_of_ae | (intros; apply GlobalTheory.SgInf.AeqCont.eqOn_of_ae <;> assumption)
end
