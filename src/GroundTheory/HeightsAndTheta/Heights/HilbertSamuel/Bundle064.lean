module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageArith.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsArithVar (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (D + 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockImageChi.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d₀.k₀) ℤ)
    (N : Matrix (ι d₀.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
    IsBlockImage d₀.y d₀.k₀ M N d'.x →
    (∀ z ∈ mcPts (mCoordIdeal d₀.y), d₀.A.h z = d'.m.ρ (blockMapC d₀.k₀ M z)) →
    (∀ g : (Ix (Fin r) → ℂ) → ℂ, ContinuousOn g {0}ᶜ → (∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) →
      ∫ a, g (resPt d' a) ∂d'.dV = ∫ a, g (blockMapC d₀.k₀ M (blockPt d₀ a)) ∂d₀.dV) →
    ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageInverse.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω) (J : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y →
      ∃ (F : MvPolynomial (Ix (Fin r)) ℤ) (e : ℕ) (G : MRing ι) (dG : K → ℕ),
        IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e) ∧ F ∉ coordIdeal ℤ x ∧
        IsMultiHomog G dG ∧ G ∉ mCoordIdeal y ∧
        (∀ z, eval z (map (Int.castRingHom ℂ) G) = eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F)) ∧
        (∀ u ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x), eval u (map (Int.castRingHom ℂ) F) ≠ 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), z ∉ mcPts J ∧ SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) u) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 → z ∉ mcPts J) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), ∀ z' ∈ mcPts (mCoordIdeal y),
          eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 →
          SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) (blockMapC k₀ M z') → SameOrbit z z')

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PerturbedSemipositivity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem blocks_mem_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 z := by
  have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  exact Filter.eventually_all.mpr hopen

theorem contDiffAt_log_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h := hA.contDiffAt (blocks_mem_nhds hz)
  exact (h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'

theorem levi_const_mul {f : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : (Σ k, ι k) → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * f y) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  simp only [zero_add] at h
  rw [h, h0, zero_add]

end PerturbedSemipositivity


open PerturbedSemipositivity in
theorem PerturbSemipos.proof : PerturbSemipos.Statement := by
  intro K _ ι _ P0 P M b a hM hb ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    unfold IsSmoothHerm at hMs hH ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hH.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y) := by
      filter_upwards [blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := contDiffAt_log_h M hM.1 hz'
    have hfH := contDiffAt_log_h (fsH ι) hH hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w := FsLineLevi.proof K ι z w hz'
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionAnyDegree

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionAnyDegree.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionAnyDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

def L2GramLattice.Statement : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module.Free ℤ E] [Module.Finite ℤ E] (X : Type) [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : E →+ (X → ℂ)),
    (∀ s, AEStronglyMeasurable (w s) μ) → (∀ s, ∃ C : ℝ, ∀ᵐ z ∂μ, ‖w s z‖ ≤ C) →
    (∀ (r : ℕ) (x : Fin r → E), LinearIndependent ℤ x → ∀ c : Fin r → ℝ,
      (∀ᵐ z ∂μ, ∑ i, (c i : ℂ) * w (x i) z = 0) → c = 0) →
    ∃ φ : E →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ E)),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w s z‖ ^ 2 ∂μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsBoundedAt (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (c : ℝ) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

def secNormAt (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z}

def sectionL2Norm (μ : Measure ((Σ k, ι k) → ℂ)) (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) : ℝ :=
  Real.sqrt (∫ z, secNormAt y A τ s z ^ 2 ∂μ)

def IsZariskiDenseMeasure (P : Ideal (MRing ι)) (μ : Measure ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ (d : K → ℕ) (f : MRingOver ℂ ι), IsMultiHomog f d → (∀ᵐ z ∂μ, eval z f = 0) →
    ∀ z ∈ mcPts P, eval z f = 0

theorem isBoundedAt_of_isBoundedH {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {c : ℝ}
    {s : Ω} (hs : IsBoundedH P y A τ c s) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : IsBoundedAt y A τ c s z :=
  fun dg dh g h hg hh hd he => hs dg dh g h z hg hh hd he hz

theorem secNormAt_le {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {c : ℝ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hc : 0 ≤ c) (hs : IsBoundedAt y A τ c s z) : secNormAt y A τ s z ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, hs⟩

theorem secNormAt_nonneg (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) :
    0 ≤ secNormAt y A τ s z := by
  rcases Set.eq_empty_or_nonempty {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z} with h | h
  · simp [secNormAt, h]
  · exact le_csInf h fun _ hx => hx.1

end Objects

def SectionL2Lattice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∀ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ → μ (mcPts (mCoordIdeal y))ᶜ = 0 →
      IsZariskiDenseMeasure (mCoordIdeal y) μ →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ (n : ℕ) (s : chartLat y A.a n), ‖φ n s‖ = sectionL2Norm μ y A n (s : Ω)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
