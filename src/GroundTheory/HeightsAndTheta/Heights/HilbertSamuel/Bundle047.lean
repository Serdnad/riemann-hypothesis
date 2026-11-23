module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedSectionStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 2 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    MixedKleiman.AtDim (d - 1) →
    ∀ q p : ℕ, 1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) →
      0 ≤ II K ι P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by

      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_

    rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF

    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set MeasureTheory Manifold EmbeddingWeight

noncomputable section

namespace PiecesAdditiveAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_weight {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {J : Type} [Fintype J]
    {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    ∃ u : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
      (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) ∧
      ∀ z ∈ mcPts P, u z = (S i).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let T : J → Set ((Σ k, ι k) → ℂ) := fun j => mcPts P ∩ S j ∩ {z | ∀ k, blockNormSq z k = 1}
  let C : J → Set ((Σ k, ι k × ι k) → ℂ) := fun j => projPt '' T j
  have hT : ∀ j, IsCompact (T j) := by
    intro j
    refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
    have : T j = ({z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ S j) ∩
        {z | ∀ k, blockNormSq z k = 1} := by
      ext z
      simp only [T, mcPts, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
        by_contra hcon
        push Not at hcon
        have := h3 k
        simp [blockNormSq, hcon] at this
    rw [this]
    exact ((isClosed_zeros P).inter (hS j)).inter isCompact_sphere.isClosed
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (hT j).image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hmem : ∀ j, ∀ z ∈ mcPts P, z ∈ S j → projPt z ∈ C j := by
    intro j z hz hzj
    obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1
    exact ⟨_, ⟨⟨mcPts_smul hP c hc hz, hsm j c z hc hzj⟩, hc1⟩, projPt_smul c hc z⟩
  have hdisj : ∀ j j', j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨⟨hzP, hzs⟩, -⟩, rfl⟩ ⟨w, ⟨⟨hwP, hwt⟩, -⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (hsm j c z hc hzs) hwt)
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
    (isClosed_biUnion_finset fun j _ => (hC j).isClosed) (hC i).isClosed
    (Set.disjoint_iUnion₂_left.2 fun j hj => hdisj j i (Finset.ne_of_mem_erase hj))
  refine ⟨fun z => f (projPt z), ?_, fun c z hc => by simp only [projPt_smul c hc], ?_⟩
  · exact (contMDiff_iff_contDiff.mp f.contMDiff).comp_contDiffOn contDiffOn_projPt
  · intro z hz
    obtain ⟨j, hj, -⟩ := huniq z hz
    by_cases hji : j = i
    · subst hji
      rw [Set.indicator_of_mem hj]
      exact h1.self_of_nhdsSet _ (hmem j z hz hj)
    · have hzi : z ∉ S i := fun h => hji ((huniq z hz).unique hj h)
      rw [Set.indicator_of_notMem hzi]
      exact h0.self_of_nhdsSet _
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hmem j z hz hj⟩)


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_sum (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {J : Type} [Fintype J] (c : J → ℝ) (g : J → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ i, c i * g i z) y w = ∑ i, c i * sheetDensity P Ψ φ (g i) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem integrable_piece (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    {J : Type} [Fintype J] {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y,
      sheetDensity P Ψ (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w) := by
  obtain ⟨u, hus, hui, hu⟩ := exists_weight hP.2.1.2.1 hS hsm huniq i
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.ofWeight u hui
  have hB : IsSmoothHerm B := Real.contDiff_exp.comp_contDiffOn hus.neg
  have hlog : ∀ z, logNorm B 1 z = u z := by
    intro z
    simp [logNorm, B, HermLine.ofWeight]
  have hhom : IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec : IsSectionOn P B 1 := ⟨0, fun k => by simp [B, HermLine.ofWeight], hhom, hnot⟩
  refine (hInt K ι P e Ψ L B 1 hP hΨ hL hB hsec).congr (Eventually.of_forall fun y => ?_)
  refine finsum_mem_congr rfl fun w _ => ?_
  exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.sheetDensity_congr_mcPts P Ψ (fun _ _ _ => rfl)
    (fun z hz => (hlog z).trans (hu z hz)) y w

end PiecesAdditiveAlt


open PiecesAdditiveAlt in
theorem PiecesAdditive.proof (hInt : PtsIntegrableStatement) : PiecesAdditive.Statement := by
  intro K _ ι _ P e L J _ S c hP hL hS hsm huniq
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hlin : ∀ y, (∑ᶠ w ∈ fibre P hΨ.choose y, sheetDensity P hΨ.choose (pot L)
        (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) y w) =
        ∑ i, c i * ∑ᶠ w ∈ fibre P hΨ.choose y,
          sheetDensity P hΨ.choose (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w := by
      intro y
      have hfin := fibreFinite K ι P e _ hP hΨ.choose_spec y
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, sheetDensity_sum, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [hlin]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_piece hInt hP hΨ.choose_spec hL hS hsm huniq i).const_mul (c i)]
    simp only [integral_const_mul]
  · simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter.AvoidRing (isMultiHomog_mul isMultiHomog_pow)

noncomputable section

namespace ClosedPtGenUniform

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem genNear_of_mul_eq_pow {d : K → ℤ} {a q b : MRingOver S ι} {α β δ : K → ℕ} {m : ℕ}
    (h : GenNear S ι 𝓜 d a α) (hq : IsMultiHomog q β) (hab : a * q = b ^ m) (hdeg : m • δ = α + β) :
    GenNear S ι 𝓜 d b δ := by
  intro I x hx
  obtain ⟨n, t, c, r, p, z, ht, htc, hp, hz, he⟩ := h I x hx
  refine ⟨m * n, t, c, r, fun j => q ^ n * p j, z, ht, htc, fun j => ?_, hz, ?_⟩
  · have h' := isMultiHomog_mul (isMultiHomog_pow hq n) (hp j)
    convert h' using 1
    funext k
    have hk := congrFun hdeg k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [mul_comm m n, mul_assoc, hk]
    ring
  · rw [pow_mul, ← hab, mul_pow, show a ^ n * q ^ n * t = q ^ n * (a ^ n * t) by ring, mul_smul, he,
      Finset.smul_sum]
    simp_rw [mul_smul]

theorem genNear_mul_pow (hM : GenNearMul.Statement) (hgr : KH.IsMGraded S ι 𝓜) {W : Ideal (MRingOver S ι)}
    (hW : W ≤ Module.annihilator (MRingOver S ι) M) {d n : K → ℤ} {f g : MRingOver S ι} {δ γ : K → ℕ}
    (hf : IsMultiHomog f δ) (hg : IsMultiHomog g γ) (hfd : GenNear S ι 𝓜 d f δ)
    (hgn : GenNear S ι (KH.quotPart S W) n g γ) :
    ∀ a : ℕ, GenNear S ι 𝓜 (d + a • n) (f * g ^ a) (δ + a • γ) := by
  intro a
  induction a with
  | zero => simpa using hfd
  | succ a ih =>
    have h' := hM S K ι M 𝓜 W (d + a • n) n (f * g ^ a) g (δ + a • γ) γ hgr hW
      (isMultiHomog_mul hf (isMultiHomog_pow hg a)) hg ih hgn
    rw [succ_nsmul, succ_nsmul, pow_succ, ← mul_assoc, ← add_assoc, ← add_assoc]
    exact h'

end ClosedPtGenUniform


open ClosedPtGenUniform in
theorem ClosedPtGenUniform.proof (hG : GradedSubmodules.Statement) (hF : ClosedPtFibreLift.Statement)
    (hN : ChartNakayamaGen.Statement) (hM : GenNearMul.Statement) : ClosedPtGenUniform.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e P hP
  classical
  obtain ⟨hPprime, hPhom, hPrel⟩ := hP.1
  choose i hi using hPrel

  let I : KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hI : ∀ k, ∀ j ∈ I.1 k, (X ⟨k, j⟩ : MRingOver S ι) ∉ P := by
    intro k j hj
    rw [Finset.mem_singleton.mp hj]
    exact hi k
  have : IsNoetherianRing (MRingOver S ι) := inferInstance

  obtain ⟨hWhom, hMsub⟩ := hG S K ι M 𝓜 hgr
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVPM : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) M) :=
    hV.trans (LinearMap.annihilator_le_of_injective (P • ⊤ : Submodule (MRingOver S ι) M).subtype
      (P • ⊤ : Submodule (MRingOver S ι) M).injective_subtype)
  obtain ⟨cM, hcM⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) M) (subGrading 𝓜 (P • ⊤)) inferInstance
    (hMsub P hPhom).1 hVPM e
  obtain ⟨fM, δM, hfM, hfMP, hgenM⟩ := hN S K ι M 𝓜 P (e + cM • N) hS hfin hgr hPprime hPhom I hI
    (hF S K ι M 𝓜 P (e + cM • N) hS hfin hgr hP (hcM cM le_rfl) I hI)

  set W := Module.annihilator (MRingOver S ι) M with hWdef
  have hWgr : KH.IsMGraded S ι (KH.quotPart S W) := QuotPartGraded.proof S K ι W hWhom
  have hQfin : Module.Finite (MRingOver S ι) (MRingOver S ι ⧸ W) := inferInstance
  obtain ⟨-, hQsub⟩ := hG S K ι (MRingOver S ι ⧸ W) (KH.quotPart S W) hWgr
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ W) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVQ : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ W) := by
    rw [Ideal.annihilator_quotient]
    exact hV
  have hVPQ : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)) :=
    hVQ.trans (LinearMap.annihilator_le_of_injective
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).subtype
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).injective_subtype)
  obtain ⟨cO, hcO⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W))
    (subGrading (KH.quotPart S W) (P • ⊤)) inferInstance (hQsub P hPhom).1 hVPQ 0
  have hgenO : ∀ n : ℕ, cO ≤ n → ∃ (g : MRingOver S ι) (γ : K → ℕ), IsMultiHomog g γ ∧ g ∉ P ∧
      GenNear S ι (KH.quotPart S W) (0 + n • N) g γ := fun n hn =>
    hN S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hPprime hPhom I hI
      (hF S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hP (hcO n hn) I hI)
  set n₁ := cO + 1 with hn₁
  obtain ⟨g₁, γ₁, hg₁, hg₁P, hgen₁⟩ := hgenO n₁ (by omega)
  obtain ⟨g₂, γ₂, hg₂, hg₂P, hgen₂⟩ := hgenO (n₁ + 1) (by omega)

  refine ⟨fM * g₁ * g₂, δM + γ₁ + γ₂, cM + n₁ * n₁, isMultiHomog_mul (isMultiHomog_mul hfM hg₁) hg₂, ?_, ?_⟩
  · intro hmem
    rcases hPprime.mem_or_mem hmem with h | h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hfMP h
      · exact hg₁P h
    · exact hg₂P h
  intro c hc
  have hpos : 0 < n₁ := by omega
  set q := (c - cM) / n₁ with hq
  set s := (c - cM) % n₁ with hs
  have hdm : n₁ * q + s = c - cM := Nat.div_add_mod (c - cM) n₁
  have hsn : s < n₁ := Nat.mod_lt _ hpos
  have hqn : n₁ ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hpos]
    omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_trans hsn.le hqn)
  have hca : c = cM + a * n₁ + s * (n₁ + 1) := by
    have h1 : c - cM + cM = c := Nat.sub_add_cancel (by omega)
    rw [← h1, ← hdm, ha]
    ring
  have hA := genNear_mul_pow hM hgr le_rfl hfM hg₁ hgenM hgen₁ a
  have hB := genNear_mul_pow hM hgr le_rfl (isMultiHomog_mul hfM (isMultiHomog_pow hg₁ a)) hg₂ hA hgen₂ s
  have htw : e + cM • N + a • (0 + n₁ • N) + s • (0 + (n₁ + 1) • N) = e + c • N := by
    rw [hca]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    push_cast
    ring
  rw [htw] at hB
  refine genNear_of_mul_eq_pow hB
    (isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_pow hfM (a + s)) (isMultiHomog_pow hg₁ (s + 1)))
      (isMultiHomog_pow hg₂ (a + 1))) (m := a + s + 1) (by ring) ?_
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResChiIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d d' : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B → d'.x = matAct B d.x →
    (∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k)) →
    ∀ n : ℕ, resChi d' n - resChi d n = latLogIndex d.x d'.x n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
