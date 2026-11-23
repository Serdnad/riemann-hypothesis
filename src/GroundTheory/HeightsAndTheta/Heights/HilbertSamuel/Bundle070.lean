module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnGenericDeg_of_semipos (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) {P P0 : Ideal (MRing ι)} {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP0 : P0 ≤ P) (hs : IsSemipositiveRel P0 P M) : NefOnGenericDeg P M.a := by
  classical
  intro W hW hPW
  have h1 : 0 ≤ geomDeg W M 1 := hN K ι P P0 M hP0 hs W hW hPW
  have h2 := hD K ι W 1 (fun _ => M) hW (fun _ => hs.1)
  have h3 : geomDeg W M 1 = (genDeg W 1 M.a : ℝ) := by
    rw [geomDeg, genDeg]
    convert h2 using 2
    rfl
  exact_mod_cast h3 ▸ h1

theorem continuousOn_zcomb_fsH {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hM : IsSmoothHerm M) (k : ℤ) :
    ContinuousOn (HermLine.zcomb M (fsH ι) k (-1)).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hH : ContinuousOn (fsH ι).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).continuousOn
  exact (hM.continuousOn.zpow₀ k fun z hz => Or.inl (M.pos z hz).ne').mul
    (hH.zpow₀ (-1) fun z hz => Or.inl ((fsH ι).pos z hz).ne')

theorem KodairaSection.proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) (hS : SectionSupBound.Statement) : KodairaSection.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 hD1 har hb hM
  obtain ⟨k, e, hk, he0, heQ⟩ :=
    hK K ι Ω y D M.a hD1 har hb (nefOnGenericDeg_of_semipos hN hD hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos) hM.big
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  have ha : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  obtain ⟨C, hC0, hB⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) k (-1)) 1 ((n : Ω) * e)
    (continuousOn_zcomb_fsH hM.semipos.1 k) (by rw [ha]; exact hne)
  exact ⟨k, (n : Ω) * e, C, hk, hC0, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0, hne, hB⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ (b : K → ℤ) {t : Ω} (ht : t ∈ chartLatQ y (b - 1) 1) :
    (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 := by
  intro c' hc'
  have h := ht c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩ := by
    intro k
    rw [eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]
    congr 1
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  have heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
    simp only [hk, Finset.prod_div_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

theorem finrank_chartLatQ_le (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    Module.finrank ℚ (chartLatQ y b 1) ≤
      Module.finrank ℚ (chartLatQ y (b - 1) 1) + Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) := by
  by_cases hfin : FiniteDimensional ℚ (chartLatQ y b 1)
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨s, hsV⟩, hs⟩
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩
  have hφ := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]

end Mul

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionSupBound

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, hk]]
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem proof (hI : BlockResolutionImageSup.Statement) (hN : NonvanishingDense.Statement) :
    BlockResolutionSupBound.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨C, hC⟩ := hI D K ι Ω d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w f‖ / d.A.h w ^ n with hg
  set M := C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f with hM

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hC n hn f hf x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end BlockResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HyperplaneRegularSection

theorem exists_notMem_of_finite {V : Type*} [AddCommGroup V] [Module ℚ V] (S : Set (Submodule ℚ V))
    (hS : S.Finite) (htop : ∀ W ∈ S, W ≠ ⊤) : ∃ v : V, ∀ W ∈ S, v ∉ W := by
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℚ) (E := V) (s := hS.toFinset)
    (by rw [Set.Finite.mem_toFinset]; exact fun h => htop ⊤ h rfl)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨v, fun W hW hvW => hv ?_⟩
  exact Set.mem_biUnion ((Set.Finite.mem_toFinset hS).mpr hW) hvW

theorem mem_span_of_mul_mem {A : Type*} [CommRing A] [IsNoetherianRing A] (f w u : A)
    (hw : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {f}), w ∉ p) (h : w * u ∈ Ideal.span {f}) :
    u ∈ Ideal.span {f} := by
  by_contra hu
  have hx : (Ideal.Quotient.mk (Ideal.span {f}) u) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : w ∈ {r : A | ∃ x : A ⧸ Ideal.span {f}, x ≠ 0 ∧ r • x = 0} :=
    ⟨_, hx, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]; exact h⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hmem
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hmem
  exact hw p hp hwp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isNoetherianRing_chartRingQ (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) :
    IsNoetherianRing (chartRingQ y c') := by
  classical
  refine isNoetherianRing_of_fg ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

def gen (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (i : ι k) : chartRingQ y c' :=
  ⟨y ⟨k, i⟩ / y ⟨k, c' k⟩, Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩⟩

def eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) : chartRingQ y c' :=
  ∏ k, gen y c' k (c k)

def avoidSub (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (p : Ideal (chartRingQ y c')) :
    Submodule ℚ (ι k → ℚ) :=
  (p.restrictScalars ℚ).comap (Fintype.linearCombination ℚ (gen y c' k))

def twist (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_add (y : (Σ k, ι k) → Ω) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) :
    twist y c' (a + a') = twist y c' a * twist y c' a' := by
  simp only [twist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc' k)]
  congr 1
  simp only [Pi.add_apply]
  ring


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_zero (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) : twist y c' 0 = 1 := by
  simp [twist]


omit [∀ k, Fintype (ι k)] in
theorem coe_eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) :
    (eqn y c c' : Ω) = (∏ k, y ⟨k, c k⟩) * twist y c' 1 := by
  simp only [eqn, gen, twist, Pi.one_apply]
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end HyperplaneRegularSection


set_option synthInstance.maxHeartbeats 400000 in
open HyperplaneRegularSection in
theorem HyperplaneRegularSection.proof : HyperplaneRegularSection.Statement := by
  intro K _ ι _ Ω _ _ y c e hc
  classical
  have hnoeth : ∀ c' : ∀ k, ι k, IsNoetherianRing (chartRingQ y c') := isNoetherianRing_chartRingQ y

  have hlam : ∀ k, ∃ v : ι k → ℚ, ∑ i, v i • y ⟨k, i⟩ ≠ 0 ∧
      ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
        ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}),
          Fintype.linearCombination ℚ (gen y c' k) v ∉ p := by
    intro k
    let S : Set (Submodule ℚ (ι k → ℚ)) :=
      {LinearMap.ker (Fintype.linearCombination ℚ fun i => y ⟨k, i⟩)} ∪
        ⋃ c' : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0},
          avoidSub y c'.1 k '' associatedPrimes (chartRingQ y c'.1)
            (chartRingQ y c'.1 ⧸ Ideal.span {eqn y c c'.1})
    have hS : S.Finite := (Set.finite_singleton _).union
      (Set.finite_iUnion fun c' => (associatedPrimes.finite _ _).image _)
    have htop : ∀ W ∈ S, W ≠ ⊤ := by
      intro W hW hWtop
      rcases hW with hW | hW
      · rw [Set.mem_singleton_iff] at hW
        have h1 : Pi.single (c k) (1 : ℚ) ∈ W := hWtop ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, Fintype.linearCombination_apply_single, one_smul] at h1
        exact hc k h1
      · obtain ⟨c', p, hp, rfl⟩ := Set.mem_iUnion.mp hW
        have h1 : Pi.single (c'.1 k) (1 : ℚ) ∈ avoidSub y c'.1 k p := hWtop ▸ Submodule.mem_top
        rw [avoidSub, Submodule.mem_comap, Submodule.restrictScalars_mem,
          Fintype.linearCombination_apply_single, one_smul,
          show gen y c'.1 k (c'.1 k) = 1 from Subtype.ext (div_self (c'.2 k))] at h1
        exact (IsAssociatedPrime.isPrime hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨v, hv⟩ := exists_notMem_of_finite S hS htop
    refine ⟨v, fun h0 => hv _ (Or.inl rfl) ?_, fun c' hc' p hp hvp =>
      hv _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨c', hc'⟩, p, hp, rfl⟩)) hvp⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h0
  choose v hv0 hvp using hlam
  set m := ∏ k, y ⟨k, c k⟩ with hm_def
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  set l : K → Ω := fun k => ∑ i, v k i • y ⟨k, i⟩ with hl
  set σ : Ω := ∏ k, l k ^ e k with hσ

  have hφ : ∀ (c' : ∀ k, ι k) (k : K),
      ((Fintype.linearCombination ℚ (gen y c' k) (v k) : chartRingQ y c') : Ω) = l k / y ⟨k, c' k⟩ := by
    intro c' k
    simp [Fintype.linearCombination_apply, gen, hl, Finset.sum_div, smul_div_assoc]
  let w : ∀ c' : ∀ k, ι k, chartRingQ y c' := fun c' =>
    ∏ k, Fintype.linearCombination ℚ (gen y c' k) (v k) ^ e k
  have hw : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (w c' : Ω) = σ * twist y c' (fun k => (e k : ℤ)) := by
    intro c' hc'
    simp only [w, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, hφ, twist, hσ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, zpow_neg, Nat.cast_one, one_mul, zpow_natCast, div_eq_mul_inv]
  have hwp : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}), w c' ∉ p := by
    intro c' hc' p hp hwp
    have := IsAssociatedPrime.isPrime hp
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hwp
    exact hvp k c' hc' p hp (this.mem_of_pow_mem _ hk)
  refine ⟨σ, Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hv0 k), ?_, ?_⟩
  · intro c' hc'
    show σ * twist y c' (fun k => (e k : ℤ)) ∈ chartRingQ y c'
    rw [← hw c' hc']
    exact (w c').2
  · intro b s hs h c' hc'
    have hnc := hnoeth c'
    have hT : twist y c' 1 * twist y c' (-1) = 1 := by
      rw [← twist_add y hc', add_neg_cancel, twist_zero]
    have hM : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    let u : chartRingQ y c' := ⟨s * twist y c' b, hs c' hc'⟩
    let u' : chartRingQ y c' :=
      ⟨σ * s / m * twist y c' (b + (fun k => (e k : ℤ)) - 1), h c' hc'⟩
    have key : w c' * u = eqn y c c' * u' := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, u, u']
      rw [hw c' hc', coe_eqn, ← hm_def, sub_eq_add_neg, twist_add y hc', twist_add y hc']
      linear_combination (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ)))) * hM +
        (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ))) * (m * m⁻¹)) * hT
    have hu : u ∈ Ideal.span {eqn y c c'} :=
      mem_span_of_mul_mem _ _ _ (hwp c' hc') (by
        rw [key]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    have ha' : (a : Ω) * (m * twist y c' 1) = s * twist y c' b := by
      rw [← coe_eqn]
      exact congrArg Subtype.val ha
    show s / m * twist y c' (b - 1) ∈ chartRingQ y c'
    have heq : s / m * twist y c' (b - 1) = a := by
      rw [sub_eq_add_neg, twist_add y hc', div_eq_mul_inv]
      linear_combination (-(m⁻¹ * twist y c' (-1))) * ha' + ((a : Ω) * (twist y c' 1 * twist y c' (-1))) * hM +
        (a : Ω) * hT
    rw [heq]
    exact a.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    IsBlockImage y k₀ M N x →
    ∃ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι (GlobalTheory κ)) (Sum.inr : Unit → K ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZeroCocycleSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ),
    ∀ v ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y ℤ s a = v

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
