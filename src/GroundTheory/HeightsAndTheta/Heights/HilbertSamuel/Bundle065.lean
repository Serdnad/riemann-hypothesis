module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SupBoundBlock.eval_torus_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      c k₀ ^ n * eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem SupBoundBlock.normRatio_torus {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hA : A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [SupBoundBlock.eval_torus_blockDeg hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, hk]]
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem SupBoundBlock.isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem SupBoundBlock.proof (hS : SupNormAgainstL2.Statement) (hR : ResolutionPullback.Statement)
    (hN : NonvanishingDense.Statement) : SupBoundBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨A, L, W, dV, -, hW, hμ, hsec⟩ := hR D K ι Ω d
  obtain ⟨⟨C, hC⟩, -⟩ := hS A L W dV hW
  refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w (map (Int.castRingHom ℂ) f)‖ / d.A.h w ^ n with hg
  set M := max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f with hM
  obtain ⟨s, hs, hps⟩ := hsec n f hf

  have hL2 : Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt 2 * blockL2Norm d n f := by
    have hI : sectionL2NormSq W dV n s = ∫ x, g (blockPt d x) ^ 2 ∂d.dV := by
      rw [sectionL2NormSq, hμ]
      exact integral_congr_ae (Eventually.of_forall hps)
    have h2 : 0 ≤ ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV := integral_nonneg fun _ => sq_nonneg _
    rw [hI, blockL2Norm, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf

  have hres : ∀ x, g (blockPt d x) ≤ M := by
    intro x
    have h1 : g (blockPt d x) ≤ Real.sqrt (ptNormSq W n s x) := by
      rw [hps x, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    have h3 := hC n hn s hs x
    rw [hpow] at h3
    have ha : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc g (blockPt d x) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := h1.trans h3
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * blockL2Norm d n f) := by
          gcongr
      _ = M := by rw [hM]; ring

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (SupBoundBlock.normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hres x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem HermLine.zcomb_isConjInvariantH {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B)
    (p q : ℤ) : IsConjInvariantH (HermLine.zcomb A B p q) := fun z => by
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem fsH_isConjInvariantH (ι : K → Type) [∀ k, Fintype (ι k)] : IsConjInvariantH (fsH ι) := fun z => by
  show ∏ k, (fsMetric (ι := ι k)).ρ (fun i => (starRingEnd ℂ) (z ⟨k, i⟩)) ^ (1 : K → ℤ) k =
    ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ (1 : K → ℤ) k
  exact Finset.prod_congr rfl fun k _ => by rw [ProjLine.isConjInvariant_fs (fun i => z ⟨k, i⟩)]

theorem zcomb_metric_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (q k p n : ℕ) :
    a ^ (q * n) = (a ^ ((q : ℤ) - k * p) * b ^ (p : ℤ)) ^ n * (a ^ (k : ℤ) * b ^ (-1 : ℤ)) ^ (p * n) := by
  rw [← zpow_natCast a, ← zpow_natCast (_ * _) n, ← zpow_natCast (_ * _) (p * n), mul_zpow, mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ ha, ← zpow_add₀ hb]
  have e1 : ((q : ℤ) - k * p) * (n : ℤ) + (k : ℤ) * ((p * n : ℕ) : ℤ) = ((q * n : ℕ) : ℤ) := by push_cast; ring
  have e2 : (p : ℤ) * (n : ℤ) + (-1 : ℤ) * ((p * n : ℕ) : ℤ) = 0 := by push_cast; ring
  rw [e1, e2, zpow_zero, mul_one]

theorem G2.proof (hK : KodairaSection.Statement) (hS : SectionProduct.Statement)
    (hP : PerturbSemipos.Statement) (hG : NefAmpleGeneric.Statement) (hF : NefAmpleFibre.Statement)
    (hL : ZCombLimit.Statement) : G2.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨k, e, C, hk, hC, he0, he, heb⟩ := hK K ι Ω y D M P0 hD har hb hM
  have hHs : IsSmoothHerm (fsH ι) := by
    have h := (hP K ι P0 (mCoordIdeal y) M 0 1 hM.semipos le_rfl zero_le_one).1
    have h' : (HermLine.zcomb M (fsH ι) 0 1).h = (fsH ι).h := by
      funext z
      simp [HermLine.zcomb]
    unfold IsSmoothHerm at h ⊢
    rwa [h'] at h
  refine ⟨k, e, C, hk, hC, he0, he, heb, fun p q hp hpq => ?_,
    hL K ι Ω y D M (fsH ι) II k hII har hM.semipos.1 hHs⟩
  have hkq : k * p ≤ q := hpq.le
  have ha : (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a =
      ((q - k * p : ℕ) : ℤ) • M.a + fun _ => ((p : ℕ) : ℤ) := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, Nat.cast_sub hkq]
  have hb0 : (0 : ℤ) ≤ (q : ℤ) - k * p := by
    have : ((k * p : ℕ) : ℤ) ≤ q := by exact_mod_cast hkq
    push_cast at this
    linarith
  refine ⟨hP K ι P0 (mCoordIdeal y) M _ _ hM.semipos hb0 (Nat.cast_nonneg p),
    HilbertSamuel.HermLine.zcomb_isConjInvariantH hM.conjInv (fsH_isConjInvariantH ι) _ _, ?_, fun ℓ hℓ => ?_, ?_⟩
  · rw [ha]
    exact hG K ι Ω y D M P0 (q - k * p) p har hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos (by omega) hp
  · rw [ha]
    exact hF K ι Ω y D M.a (q - k * p) p ℓ har hM.nef (by omega) hp hℓ
  intro n s hs
  have hB : e ∈ chartLat y (HermLine.zcomb M (fsH ι) k (-1)).a 1 := by
    have h' : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
      funext i
      simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
      ring
    rw [h']
    exact he
  have hdeg : ((q * n : ℕ) : ℤ) • M.a = (n : ℤ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a +
      ((p * n : ℕ) : ℤ) • (HermLine.zcomb M (fsH ι) k (-1)).a := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  have hmet : ∀ z ∈ mcPts (mCoordIdeal y), M.h z ^ (q * n) =
      (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).h z ^ n *
        (HermLine.zcomb M (fsH ι) k (-1)).h z ^ (p * n) := fun z hz =>
    zcomb_metric_identity (M.pos z hz.1).ne' ((fsH ι).pos z hz.1).ne' q k p n
  obtain ⟨hmem, hbd⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p)
    (HermLine.zcomb M (fsH ι) k (-1)) M n (p * n) (q * n) s e hdeg hmet hs hB
  refine ⟨hmem, fun c hc => ?_⟩
  have h := hbd c (Real.exp C) hc heb
  rwa [← Real.exp_nat_mul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def EuclideanSectionsPower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ (m * q)))] [IsZLattice ℝ (imageLattice (φ (m * q)))],
          -Real.log (ZLattice.covolume (imageLattice (φ (m * q)))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeExtension.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    ∃ Ψ : EuclideanSpace ℝ (Fin R') →ₗ[ℝ] EuclideanSpace ℝ (Fin R),
      (∀ x, Ψ (φ' x) = φ (ψ x)) ∧ (∀ y, ‖Ψ y‖ ≤ ‖y‖) ∧ Function.Injective Ψ

def SpanningExtension.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι]
    (v : ι → V) (S : Set V), LinearIndependent ℝ v → Submodule.span ℝ S = ⊤ →
    ∃ w : Fin (Module.finrank ℝ V - Fintype.card ι) → V, (∀ j, w j ∈ S) ∧ LinearIndependent ℝ (Sum.elim v w)

def CovolumeLeGram.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → EuclideanSpace ℝ (Fin n)), (∀ i, x i ∈ L) →
    LinearIndependent ℝ x → Fintype.card ι = n → ZLattice.covolume L ≤ Real.sqrt (Matrix.gram ℝ x).det

def GramContraction.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Ψ : EuclideanSpace ℝ ι →ₗ[ℝ] V) (u : ι → EuclideanSpace ℝ ι) (w : κ → V),
    (∀ y, ‖Ψ y‖ ≤ ‖y‖) →
      (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det ≤ (Matrix.gram ℝ u).det * ∏ j, ‖w j‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

open Veronese

def VeroneseMonoBasis.Statement : Prop :=
  ∀ D n : ℕ, ∃ b : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → MvPolynomial (Ix (Idx D)) ℚ,
    IsSecBasis (Veronese.x D) n b ∧
      ∀ k, aeval (Veronese.x D) (b k) = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i

def VeroneseGramMono.Statement : Prop :=
  ∀ (D n r : ℕ) (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ)
    (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ),
    (∀ k, aeval (Veronese.x D) (b k) =
      ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i) →
    Veronese.gram D n b = A.map (Int.cast : ℤ → ℝ) *
      Matrix.diagonal (fun l => monoNormSq (adtEnum D (2 * n) l)) * (A.map (Int.cast : ℤ → ℝ)).transpose

theorem adtEnum_zero_eq (D : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) 0).card) :
    adtEnum D 0 l = 0 := by
  have h := Finset.Nat.mem_antidiagonalTuple.mp
    (((Finset.Nat.antidiagonalTuple (D + 1) 0).equivFin.symm l).2)
  funext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
