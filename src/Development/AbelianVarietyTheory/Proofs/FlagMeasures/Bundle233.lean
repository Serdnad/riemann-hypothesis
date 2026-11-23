module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle207
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaProductGaugeSandwichNearOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle226
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle227
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.MapRadial

theorem continuous_hs {n : ℕ} : Continuous (Formalism.REAL.hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold Formalism.REAL.hs
  fun_prop

theorem hs_nonneg' {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs
  positivity

theorem measurable_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Measurable fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact (continuous_hs.comp (this.sub continuous_const)).measurable

theorem measurable_hs_loc (j : ℕ) : Measurable fun x : Fin j → Fin j → ℂ =>
    Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1) := by
  have h0 : Continuous fun x : Fin j → Fin j → ℂ => Matrix.of x := continuous_id
  have h1 : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := h0.matrix_det.measurable
  have h2 : ∀ r s, Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).adjugate r s :=
    fun r s => (h0.matrix_adjugate.matrix_elem r s).measurable
  refine (continuous_hs.comp (h0.sub continuous_const)).measurable.add ?_
  unfold Formalism.REAL.hs
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (((h1.inv.mul (h2 r s)).sub measurable_const).norm).pow_const 2

theorem isRadial_map_lev : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  intro n n₀ a j ε ε₀ B B₀ hF θ hθ hθe c hc
  have hG : IsRadial (ENNReal.ofReal c • Formalism.REAL.muG ε₀) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2) := by
    have := ((GlobalTheory.GaugeWhole.gauge_whole n₀ ε₀).1 c hc).2.2.2
    simpa [IsRadial] using this
  haveI : SigmaFinite (Formalism.REAL.muG ε₀) := by
    unfold Formalism.REAL.muG
    infer_instance
  have hP := GlobalTheory.T.euclideanBallAsymptotics_finite_pi a (fun i => Fin (j i) → Fin (j i) → ℂ)
    (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) _ (fun i => 2 * j i ^ 2)
    (fun i => measurable_hs_loc (j i)) (fun i x => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun i => GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse (j i))
  have h2 := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ _ _ _ _ _ _
    (Finset.measurable_sum _ fun i _ => (measurable_hs_loc (j i)).comp (measurable_pi_apply i))
    (measurable_hs_uMat ε₀)
    (fun x => Finset.sum_nonneg fun i _ => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun g => hs_nonneg' _) hP hG
  have hd : n₀ ^ 2 + 2 * ∑ i, j i ^ 2 = ∑ i, 2 * j i ^ 2 + n₀ ^ 2 := by
    rw [Finset.mul_sum, add_comm]
  rw [hd]
  have hae1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)),
      ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    have h0 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      rw [ae_iff]
      simpa using (haarLoc_conj_and_null (j i)).2
    exact (Measure.quasiMeasurePreserving_eval
      (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) i).ae (Measure.ae_smul_measure h0 _)
  have hae := (Measure.quasiMeasurePreserving_fst (ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀)).ae hae1
  unfold IsRadial at h2 ⊢
  refine h2.congr fun r => ?_
  rw [Measure.map_apply hθ (measurableSet_le (measurable_hs_uMat ε).sqrt measurable_const)]
  congr 1
  refine measure_congr ?_
  filter_upwards [hae] with z hz
  have e := hs_lev_sub_one n n₀ a j ε ε₀ B B₀ hF (fun i => Matrix.of (z.1 i)) (uMat z.2)
  rw [← hθe z hz] at e
  exact Iff.of_eq (congrArg (fun t => Real.sqrt t ≤ r) e.symm)

end GlobalTheory.LeviIso.MapRadial
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PerpReduce

section Lat

variable {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)

instance ringHomSurjective_mapRingEquiv : RingHomSurjective (RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E) :=
  ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩

def vecMap (n : ℕ) : (Fin n → E') →ₛₗ[(RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E)] (Fin n → E) where
  toFun y := fun i => e (y i)
  map_add' a b := by funext i; simp
  map_smul' r a := by
    funext i
    show e ((r : E') * a i) = e (r : E') * e (a i)
    rw [map_mul]

def latMap (L : Submodule (𝓞 E') (Fin n → E')) : Submodule (𝓞 E) (Fin n → E) := L.map (vecMap e n)

theorem mem_latMap (L : Submodule (𝓞 E') (Fin n → E')) (y : Fin n → E') :
    (fun i => e (y i)) ∈ latMap e L ↔ y ∈ L := by
  refine ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
  have : z = y := funext fun i => e.injective (congrFun h i)
  exact this ▸ hz

theorem exists_vec (x : Fin n → E) : ∃ y : Fin n → E', x = fun i => e (y i) :=
  ⟨fun i => e.symm (x i), by funext i; simp⟩

theorem latMap_fg (L : Submodule (𝓞 E') (Fin n → E')) (h : L.FG) : (latMap e L).FG := h.map _

theorem latMap_span (L : Submodule (𝓞 E') (Fin n → E'))
    (h : Submodule.span E' (L : Set (Fin n → E')) = ⊤) :
    Submodule.span E (latMap e L : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := exists_vec e x
  have hy : y ∈ Submodule.span E' (L : Set (Fin n → E')) := h ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ((mem_latMap e L y).2 hy)
  | zero =>
    have : (fun i => e ((0 : Fin n → E') i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => e ((a + b) i)) = (fun i => e (a i)) + (fun i => e (b i)) := by funext i; simp
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => e ((r • a) i)) = e r • (fun i => e (a i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem mem_range_iff (a : E') :
    e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.symm b, ?_⟩
    show e.symm (b : E) = a
    rw [show (b : E) = e a from hb]; simp
  · rintro ⟨b, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e b, rfl⟩

variable [StarRing E] [StarRing E'] (he : ∀ y, e (star y) = star (e y))
include he

theorem hform_map (J : Matrix (Fin n) (Fin n) E') (y x : Fin n → E') :
    Formalism.UG.hform (starRingEnd E) (J.map e) (fun i => e (y i)) (fun i => e (x i)) =
      e (Formalism.UG.hform (starRingEnd E') J y x) := by
  simp [Formalism.UG.hform, starRingEnd_apply, he]

theorem isHerm_map {J : Matrix (Fin n) (Fin n) E'} (hJ : Formalism.UG.IsHerm (starRingEnd E') J) :
    Formalism.UG.IsHerm (starRingEnd E) (J.map e) := by
  ext i j
  have h : star (J j i) = J i j := congrFun (congrFun hJ i) j
  show star (e (J j i)) = e (J i j)
  rw [← h, he]

theorem latMap_dual {J : Matrix (Fin n) (Fin n) E'} {L : Submodule (𝓞 E') (Fin n → E')}
    (h : ∀ x : Fin n → E', x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (starRingEnd E') J y x ∈ (algebraMap (𝓞 E') E').range) (x : Fin n → E) :
    x ∈ latMap e L ↔
      ∀ y ∈ latMap e L, Formalism.UG.hform (starRingEnd E) (J.map e) y x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨x, rfl⟩ := exists_vec e x
  rw [mem_latMap, h]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec e y
    rw [hform_map e he, mem_range_iff]
    exact H y ((mem_latMap e L y).1 hy)
  · rw [← mem_range_iff e, ← hform_map e he]
    exact H _ ((mem_latMap e L y).2 hy)

end Lat

theorem det_map_ne {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)
    {J : Matrix (Fin n) (Fin n) E'} (h : J.det ≠ 0) : (J.map e).det ≠ 0 := by
  have := (IsUnit.mk0 _ h).map (e : E' →+* E)
  rw [RingHom.map_det] at this
  exact this.ne_zero

def sibOf (I I' : AutInst) (e : I'.E ≃+* I.E) (he : ∀ y, e (star y) = star (e y)) : Sib I :=
  have h := fun v : InfinitePlace I.F =>
    GlobalTheory.AutInhab.exists_frame (GlobalTheory.AutInhab.isHerm_map I.cm (isHerm_map e he I'.J_herm) (I.φ v))
      (GlobalTheory.AutInhab.isUnit_det_map (det_map_ne e I'.J_det) (I.φ v))
  { n := I'.n
    J := I'.J.map e
    J_herm := isHerm_map e he I'.J_herm
    J_det := det_map_ne e I'.J_det
    L := latMap e I'.L
    L_span := latMap_span e _ I'.L_span
    L_fg := latMap_fg e _ I'.L_fg
    L_dual := latMap_dual e he I'.L_dual
    ε := fun v => (h v).choose
    P := fun v => (h v).choose_spec.choose
    P_unit := fun v => (h v).choose_spec.choose_spec.1
    P_spec := fun v => (h v).choose_spec.choose_spec.2 }

theorem exists_sib : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  intro I I' e s x A xf ⟨he, hn, hx, hxA, hA, hxL, hL⟩
  refine ⟨sibOf I I' e he, A, ⟨hn, hx, hxA, hA, hxL, fun y => ?_⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec (n := I'.n) e y
    exact (mem_latMap e I'.L y).trans (hL y)
  · intro c μ _ _ c' μ' _ _ hc hc'
    refine GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus (sibOf I I' e he).inst I' e (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) 1 he rfl ?_
      (fun y => ?_) c μ c' μ' hc hc'
    · show (1 : Matrix (Fin I'.n) (Fin I'.n) I.E)ᴴ * I'.J.map e * (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) =
        I'.J.map e
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · rw [GlobalTheory.GaussMean.Test.lamX_one]
      show _ ↔ (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) *ᵥ (fun i => e (y i)) ∈ latMap e I'.L
      rw [Matrix.one_mulVec, mem_latMap]

end GlobalTheory.PerpReduce
end
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.besselModelMatrix_skew_coordinates_rational_aut : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  first | exact @GlobalTheory.DegVol.RefCovSkew.coords_skew | exact GlobalTheory.DegVol.RefCovSkew.coords_skew | (intros; apply GlobalTheory.DegVol.RefCovSkew.coords_skew <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawa_product_gauge_sandwich_near_one : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ u ∈ SN, ∀ m ∈ SM, ∀ k ∈ MainNotions, nrm (uMat u - 1) < t → nrm (uMat m - 1) < t → nrm (uMat k - 1) < t → ∀ σ γ : ℝ, σ = max (nrm (uMat (u * m * k) - 1)) (len (crd EL (uMat k - 1))) → γ = gau EN EM EK EL (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1)) → γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ nrm (uMat u - 1) ≤ C * γ ∧ nrm (uMat m - 1) ≤ C * γ ∧ nrm (uMat k - 1) ≤ C * γ := by
  first | exact @GlobalTheory.IwSand.gau_sandwich | exact GlobalTheory.IwSand.gau_sandwich | (intros; apply GlobalTheory.IwSand.gau_sandwich <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.BoundedUnfold

theorem multiplicity_le (I : AutInst) (g : ℕ) (S : Set I.Ginf) (y z : I.GA) (hn : 1 ≤ I.n)
    (hS : ∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) :
    {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite ∧
    (({γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.ncard : ℕ) : ℝ) ≤
      (1 + 4 * Real.sqrt I.n / tau1 I y ^ 2) ^ (2 * (I.n ^ 2 * I.f)) := by
  classical
  have hτ : 0 < tau1 I y := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y
  rcases Set.eq_empty_or_nonempty
      {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} with h0 | ⟨γ0, hγ0⟩
  · rw [h0]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty, Nat.cast_zero]
    positivity
  · obtain ⟨hCfin, hCcard⟩ :=
      GlobalTheory.RationalCount.count_le I y y (fun _ => Real.log 2) hn (fun _ => (Real.log_pos one_lt_two).le)

    have hf : ∀ γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g},
        (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹) γ ∈
          {a : I.GA | a ∈ I.GFset ∧ (y⁻¹ * a * y).2 ∈ I.Kset ∧
            ∀ v, dOp (uMat ((y⁻¹ * a * y).1 v)) ≤ (fun _ => Real.log 2) v} := by
      intro γ hγ
      have hγ' : y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g := hγ
      have hγ0' : y⁻¹ * (γ0.1 * z) ∈ S ×ˢ I.Kg g := hγ0
      have key : y⁻¹ * (γ.1 * γ0.1⁻¹) * y = (y⁻¹ * (γ.1 * z)) * (y⁻¹ * (γ0.1 * z))⁻¹ := by
        group
      refine ⟨?_, ?_, ?_⟩
      · exact (GlobalTheory.RatDiscrete.ratSub I).mul_mem γ.2 ((GlobalTheory.RatDiscrete.ratSub I).inv_mem γ0.2)
      · rw [key]
        have h1 := hγ'.2.1
        have h2 := hγ0'.2.1
        simp only [AutInst.Kset, Set.mem_ofPred_eq] at h1 h2 ⊢
        rw [Prod.snd_mul, Prod.snd_inv]
        push_cast
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      · intro v
        rw [key, Prod.fst_mul, Prod.fst_inv]
        exact hS _ hγ'.1 _ hγ0'.1 v
    have hinj : Set.InjOn (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹)
        {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} :=
      fun a _ b _ hab => Subtype.ext (mul_right_cancel hab)
    have hAfin : {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite :=
      Set.Finite.of_finite_image (hCfin.subset (Set.image_subset_iff.2 hf)) hinj
    refine ⟨hAfin, ?_⟩
    refine le_trans (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn _ hf hinj hCfin)) (le_trans hCcard ?_)
    have hsum : (∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) = (I.f : ℝ) * Real.log 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, GlobalTheory.RationalCount.card_places]
    have hE : Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) ≤ 2 := by
      rw [hsum]
      rcases Nat.eq_zero_or_pos I.f with hf0 | hfpos
      · rw [hf0]; norm_num
      · have : (I.f : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'
        rw [mul_div_cancel_left₀ _ this, Real.exp_log two_pos]
    apply pow_le_pow_left₀ (by positivity)
    have h2 : 2 * Real.sqrt I.n * Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) /
        (tau1 I y * tau1 I y) ≤ 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by
      gcongr
    calc _ ≤ 1 + 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by linarith
      _ = 1 + 4 * Real.sqrt I.n / tau1 I y ^ 2 := by ring

theorem lintegral_le_multiplicity : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  intro B S y Φ hn hg hSm hS hΦ hΦl hΦr
  classical
  have hL : ∀ a : B.I.GA, Measurable (fun q : B.I.GA => a * q) := fun a =>
    (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf a).measurable
  have hKm : MeasurableSet (B.I.Kg B.g) :=
    ((GlobalTheory.CongTop.adelic_topology B.I).2.2.2.2.2.2 B.g hg).1.measurableSet
  have hUm : MeasurableSet (S ×ˢ B.I.Kg B.g) := hSm.prod hKm

  have step1 : B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) =
      ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) := by
    rw [AutInst.muA, ← Measure.prod_restrict, lintegral_prod (fun p => Φ (y * p)) (hΦ.comp (hL y)).aemeasurable]
    have inner : ∀ a : B.I.Ginf, ∫⁻ k in B.I.Kg B.g, Φ (y * (a, k)) ∂B.μf =
        Φ (y * (a, 1)) * B.μf (B.I.Kg B.g) := by
      intro a
      rw [← setLIntegral_const]
      refine setLIntegral_congr_fun hKm (fun k hk => ?_)
      have e : y * (a, k) = y * (a, 1) * (1, k) := by
        rw [mul_assoc]
        congr 1
        exact Prod.ext (mul_one a).symm (one_mul k).symm
      rw [e, hΦr k hk]
    simp_rw [inner]
    rw [lintegral_mul_const (f := fun a : B.I.Ginf => Φ (y * (a, 1))) _
      (hΦ.comp ((hL y).comp measurable_prodMk_right))]
    exact mul_comm _ _

  have hH : Measurable (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q)) :=
    ((hΦ.comp (hL y)).indicator hUm).comp (hL y⁻¹)
  have step2 : ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) =
      ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
    rw [← lintegral_indicator hUm,
      ← (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf y).lintegral_comp hH]
    congr 1
    funext a
    rw [inv_mul_cancel_left]

  have hfd := GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec
  have : Countable (GlobalTheory.RatDiscrete.ratSub B.I) :=
    Set.Countable.to_subtype (s := (GlobalTheory.RatDiscrete.ratSub B.I : Set B.I.GA))
      (GlobalTheory.RatDiscrete.countable_GFset B.I)
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA := ⟨fun c => hL c.1⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun c s hs => (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf c.1).measure_preimage
      hs.nullMeasurableSet⟩

  have hpt : ∀ z : B.I.GA, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
      (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ≤
        ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * Φ z := by
    intro z
    obtain ⟨hAf, hAc⟩ := multiplicity_le B.I B.g S y z hn hS
    have hHA : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) =
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator
            (fun _ => Φ z) γ := by
      intro γ
      by_cases h : y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
        show Φ (y * (y⁻¹ * (γ.1 * z))) = Φ z
        rw [mul_inv_cancel_left]
        exact hΦl γ.1 γ.2 z
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show γ ∉ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
    have hsum1 : ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
        {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ :=
      tsum_eq_sum (s := hAf.toFinset) (fun γ hγ => Set.indicator_of_notMem (by simpa using hγ) _)
    have hsum2 : ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset, Φ z :=
      Finset.sum_congr rfl (fun γ hγ => Set.indicator_of_mem (by simpa using hγ) _)
    rw [tsum_congr hHA, hsum1, hsum2, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hAf]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hAc
  calc B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I)
      = ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
        rw [step1, step2]
    _ = ∫⁻ z in B.fund, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
          (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ∂(B.I.muA B.μf) := by
        rw [hfd.lintegral_eq_tsum''
          (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q))]
        rw [lintegral_tsum (f := fun (γ : GlobalTheory.RatDiscrete.ratSub B.I) (z : B.I.GA) =>
            (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)))
          (fun γ => (hH.comp (hL γ.1)).aemeasurable)]
        simp only [Subgroup.smul_def]
        rfl
    _ ≤ ∫⁻ z in B.fund, ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^
          (2 * (B.I.n ^ 2 * B.I.f))) * Φ z ∂(B.I.muA B.μf) := lintegral_mono hpt
    _ = _ := lintegral_const_mul _ hΦ

end GlobalTheory.BoundedUnfold
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.psi_restriction_holomorphic_near_one : PsLocal := by
  first | exact @GlobalTheory.Dec.psLocal | exact GlobalTheory.Dec.psLocal | (intros; apply GlobalTheory.Dec.psLocal <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relative_weight_term_datum_pos : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d0 d : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → (∃ t, LocNG.IsTermOver P d t) → 0 < LocNG.Datum.wt d0 d := by
  first | exact @GlobalTheory.WtPos.wt_pos | exact GlobalTheory.WtPos.wt_pos | (intros; apply GlobalTheory.WtPos.wt_pos <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitarySubgroupChart_surjective_near_origin : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  first | exact @GlobalTheory.GaugeSubChartSurj.chart_surj | exact GlobalTheory.GaugeSubChartSurj.chart_surj | (intros; apply GlobalTheory.GaugeSubChartSurj.chart_surj <;> assumption)
end
