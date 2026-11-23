module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix Metric

noncomputable section

namespace IsolatedFibreOpenOfGeneric

theorem isClosed_zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroLocus J) := by
  have h : zeroLocus J = ⋂ q ∈ J, {x | eval x q = 0} := by
    ext x
    simp [zeroLocus]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem eval_linPoly {n k : ℕ} (B : Matrix (Fin k) (Fin n) ℂ) (z : Fin n → ℂ) (i : Fin k) :
    eval z (linPoly B.mulVecLin i) = (B *ᵥ z) i := by
  simp [linPoly, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem finiteProjection_near (hGen : GenericProjectionFinite.Statement) {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsAffVariety J k) (A : Matrix (Fin k) (Fin n) ℂ) :
    ∃ M : Matrix (Fin k) (Fin n) ℂ,
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), IsFiniteProjection J (A + t • (M - A)).mulVecLin := by
  obtain ⟨⟨S, ⟨M, f, hfS, hf⟩, hS⟩, -⟩ := hGen n k J hJ.isPrime hJ.dim
  refine ⟨M, ?_⟩
  set a : Fin k × Fin n → ℂ := fun p => A p.1 p.2
  set b : Fin k × Fin n → ℂ := fun p => (M - A) p.1 p.2
  have hg : ∀ t : ℂ, eval (fun p : Fin k × Fin n => (A + t • (M - A)) p.1 p.2) f = eval (a + t • b) f :=
    fun t => rfl
  have han : ∀ t : ℂ, AnalyticAt ℂ (fun t : ℂ => eval (a + t • b) f) t := fun t =>
    (AnalyticOnNhd.eval_mvPolynomial f _ trivial).comp
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  rcases (han 0).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (fun t _ => han t)
      isPreconnected_univ (Set.mem_univ 0) h0 (Set.mem_univ 1)
    apply hf
    have h1 : (fun p : Fin k × Fin n => M p.1 p.2) = a + (1 : ℂ) • b := by
      funext p
      simp [a, b]
    rw [h1]
    exact hz
  · filter_upwards [hne] with t ht
    exact hS _ ⟨f, hfS, by rw [hg]; exact ht⟩

theorem proof (hGen : GenericProjectionFinite.Statement) (hFin : FiniteMapOpen.Statement) :
    IsolatedFibreOpen.Statement := by
  intro n k J A x hJ hx ⟨W, hW, hiso⟩ W' hW'
  have hZc : IsClosed (zeroLocus J) := isClosed_zeroLocus J
  have hAc : ∀ B : Matrix (Fin k) (Fin n) ℂ, Continuous fun z : Fin n → ℂ => B *ᵥ z :=
    fun B => continuous_const.matrix_mulVec continuous_id

  obtain ⟨r0, hr0, hr0W⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hW')
  have hr : 0 < r0 / 2 := half_pos hr0
  have hcb : closedBall x (r0 / 2) ⊆ W ∩ W' :=
    (closedBall_subset_ball (half_lt_self hr0)).trans hr0W
  have hSc : IsCompact (zeroLocus J ∩ closedBall x (r0 / 2)) :=
    (isCompact_closedBall x _).inter_left hZc
  have hKc : IsCompact (zeroLocus J ∩ sphere x (r0 / 2)) := (isCompact_sphere x _).inter_left hZc

  have hAK : A *ᵥ x ∉ (fun z => A *ᵥ z) '' (zeroLocus J ∩ sphere x (r0 / 2)) := by
    rintro ⟨z, ⟨hzZ, hzs⟩, hzA⟩
    have hzx : z = x := hiso z (hcb (sphere_subset_closedBall hzs)).1 hzZ hzA
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 ((hKc.image (hAc A)).isClosed.isOpen_compl) _ hAK
  obtain ⟨M, hM⟩ := finiteProjection_near hGen hJ A
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hAc (M - A)).continuousOn
  have hAt : ∀ (t : ℂ) (z : Fin n → ℂ), (A + t • (M - A)) *ᵥ z = A *ᵥ z + t • ((M - A) *ᵥ z) :=
    fun t z => by rw [add_mulVec, smul_mulVec]
  have hclose : ∀ t : ℂ, ‖t‖ * C < ε / 4 → ∀ z ∈ zeroLocus J ∩ closedBall x (r0 / 2),
      dist ((A + t • (M - A)) *ᵥ z) (A *ᵥ z) < ε / 4 := by
    intro t ht z hz
    rw [dist_eq_norm, hAt, add_sub_cancel_left, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg t)).trans_lt ht

  have hstep : ∀ t : ℂ, IsFiniteProjection J (A + t • (M - A)).mulVecLin → ‖t‖ * C < ε / 4 →
      ball (A *ᵥ x) (ε / 4) ⊆
        (fun z => (A + t • (M - A)) *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) := by
    intro t hfin ht
    set B := A + t • (M - A) with hB
    have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => linPoly B.mulVecLin i) =
        projAlgHom J B.mulVecLin := by
      rw [MvPolynomial.comp_aeval]
      rfl
    have hTo : IsOpen ((fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2))) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨z, ⟨hzZ, hzb⟩, rfl⟩
      have h := hFin n k J (fun i => linPoly B.mulVecLin i) hJ.isPrime (by rw [hcomp]; exact hfin.1)
        (by rw [hcomp]; exact hfin.2) z hzZ (ball x (r0 / 2)) (isOpen_ball.mem_nhds hzb)
      simpa only [eval_linPoly] using h
    have hTS : (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) ⊆
        (fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) :=
      Set.image_mono (Set.inter_subset_inter_right _ ball_subset_closedBall)
    have hSim : IsClosed ((fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2))) :=
      (hSc.image (hAc B)).isClosed
    have hxS : x ∈ zeroLocus J ∩ closedBall x (r0 / 2) := ⟨hx, mem_closedBall_self hr.le⟩
    have hsub : ball (A *ᵥ x) (ε / 2) ⊆ (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) := by
      refine (convex_ball _ _).isPreconnected.subset_of_closure_inter_subset hTo ?_ ?_
      · refine ⟨B *ᵥ x, ?_, x, ⟨hx, mem_ball_self hr⟩, rfl⟩
        rw [mem_ball]
        linarith [hclose t ht x hxS]
      · rintro _ ⟨hcl, hball⟩
        obtain ⟨z, hzS, rfl⟩ := closure_minimal hTS hSim hcl
        refine ⟨z, ⟨hzS.1, ?_⟩, rfl⟩
        by_contra hzb
        have hzs : z ∈ sphere x (r0 / 2) :=
          mem_sphere.2 (le_antisymm (mem_closedBall.1 hzS.2) (not_lt.1 (by simpa [mem_ball] using hzb)))
        apply hεK (show A *ᵥ z ∈ ball (A *ᵥ x) ε from ?_) ⟨z, ⟨hzS.1, hzs⟩, rfl⟩
        rw [mem_ball] at hball ⊢
        have h1 := hclose t ht z hzS
        rw [dist_comm] at h1
        linarith [dist_triangle (A *ᵥ z) (B *ᵥ z) (A *ᵥ x)]
    exact (ball_subset_ball (by linarith)).trans (hsub.trans hTS)

  have h0 : Tendsto (fun t : ℂ => ‖t‖ * C) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => ‖t‖ * C := continuous_norm.mul continuous_const
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    simpa using h
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ * C < ε / 4 := h0.eventually (gt_mem_nhds (by positivity))
  refine mem_of_superset (ball_mem_nhds (A *ᵥ x) (by positivity : (0 : ℝ) < ε / 4)) ?_
  intro y hy
  have hz : ∀ t : ℂ, ∃ z : Fin n → ℂ,
      (∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y) →
        z ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ z = y := by
    intro t
    by_cases h : ∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose zf hzf using hz
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      zf t ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ zf t = y := by
    filter_upwards [hM, hsmall] with t h1 h2
    exact hzf t (hstep t h1 h2 hy)
  obtain ⟨a, haS, hacl⟩ := hSc (f := map zf (𝓝[≠] (0 : ℂ)))
    (le_principal_iff.2 (hev.mono fun t ht => ht.1))
  have hlim : Tendsto (fun t => A *ᵥ zf t) (𝓝[≠] (0 : ℂ)) (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [hev] with t ht
    rw [← ht.2, hAt, sub_add_cancel_left, norm_neg, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ht.1) (norm_nonneg _)
  have hay : A *ᵥ a = y :=
    eq_of_nhds_neBot (hacl.map (hAc A).continuousAt (tendsto_map'_iff.2 hlim))
  exact ⟨a, ⟨haS.1, (hcb haS.2).2⟩, hay⟩

end IsolatedFibreOpenOfGeneric

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteGermProjectionCover.proof (hopen : IrreducibleGermProjectionOpenNear.Statement)
    (hcov : ProperOpenProjectionCover.Statement) : FiniteGermProjectionCover.Statement := by
  intro σ _ X w d A hX hirr hiso hinj
  obtain ⟨N₀, hN₀, hop⟩ := hopen σ X w d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩
  intro B D hBo hBN hwB hDo hDc hmaps hprop hisoB
  have hBN' : B ⊆ N := fun x hx => (hBN hx).2

  have hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} := by
    ext z
    constructor
    · rintro ⟨hzX, hzB⟩
      have h1 : z ∈ X ∩ N := ⟨hzX, hBN' hzB⟩
      rw [hXN] at h1
      exact ⟨hzB, h1.2⟩
    · rintro ⟨hzB, hz⟩
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN' hzB, hz⟩
      rw [← hXN] at h2
      exact ⟨h2.1, hzB⟩

  have hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x) := by
    intro x hx V hV
    have h1 := hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B)
      (Filter.inter_mem hV (hBo.mem_nhds hx.2))
    have h2 : X ∩ (V ∩ B) = X ∩ B ∩ V := by
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rwa [h2] at h1
  obtain ⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩ :=
    hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB
  exact ⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionOffZerosDense.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement)
    (hCl : FiniteProjectionSheetedClosureEquations.Statement) :
    FiniteProjectionOffZerosDense.Statement := by
  intro σ _ X w d A hX hirr hiso hinj δ hδ hδne
  obtain ⟨ℓ, N, a, δ₀, q, ha, hδ₀, hq, hδ₀ne, hp, hsep, hcoord⟩ := hPF σ X w d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X w d A hX hirr hiso hinj ℓ N a δ₀ q ha hδ₀ hq hδ₀ne hp hsep hcoord
  obtain ⟨m, c, hc, hcY, hcl⟩ := hCl σ X w d A hX hiso hinj (fun y => δ₀ y * δ y) (hδ₀.mul hδ)
    ⟨M, hM, fun y hy hne => hMsh y hy (left_ne_zero_of_mul hne)⟩
  have hcomp : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → AnalyticAt ℂ (fun z => f (A z)) w :=
    fun hf => hf.comp (A.analyticAt w)
  have hnot : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → (¬ ∀ᶠ y in 𝓝 (A w), f y = 0) →
      ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f (A z) = 0 := fun hf hne h => hne (hinj _ hf h)
  have hvan : ∀ k, ∀ᶠ z in 𝓝 w, z ∈ X → c k z = 0 := by
    intro k
    have h1 : ∀ᶠ z in 𝓝 w, z ∈ X → (c k z * δ₀ (A z)) * δ (A z) = 0 := by
      filter_upwards [hcY] with z hz hzX
      by_cases h : δ₀ (A z) * δ (A z) = 0
      · rw [mul_assoc, h, mul_zero]
      · rw [hz hzX h k, zero_mul, zero_mul]
    rcases hirr.2 (fun z => c k z * δ₀ (A z)) (fun z => δ (A z)) ((hc k).mul (hcomp hδ₀)) (hcomp hδ)
      h1 with h2 | h2
    · rcases hirr.2 (c k) (fun z => δ₀ (A z)) (hc k) (hcomp hδ₀) h2 with h3 | h3
      · exact h3
      · exact absurd h3 (hnot hδ₀ hδ₀ne)
    · exact absurd h2 (hnot hδ hδne)
  have hall : ∀ᶠ z in 𝓝 w, z ∈ X → ∀ k, c k z = 0 := by
    filter_upwards [Filter.eventually_all.2 hvan] with z hz hzX k using hz k hzX
  refine ⟨_, hall.and hcl, ?_⟩
  rintro z ⟨hzX, hz1, hz2⟩
  refine closure_mono ?_ (hz2 hzX (hz1 hzX))
  rintro x ⟨hx, hne⟩
  exact ⟨hx, right_ne_zero_of_mul hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter Matrix ComplexSets

noncomputable section

namespace IsolatedFibreOpenPoly

variable {n d : ℕ}

def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)

def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)

def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)

def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)

def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0

theorem lastRows_mulVec (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by
  funext i
  simp [lastRows, Matrix.mulVec, dotProduct, ite_mul]

theorem firstPart_graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by
  funext j
  simp [firstPart, graphPt, Fin.append_left]

theorem graphPt_natAdd (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]

theorem continuous_firstPart : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _

theorem eval_graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphSubst]
  | add q r hq hr => simp only [map_add (f := _), hq, hr]
  | mul_X q i hq =>
    simp only [map_mul, graphSubst, aeval_X, eval_X]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [graphPt, Fin.append_left]
    · simp [graphPt, Fin.append_right]

theorem graphSubst_rename (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by
  rw [graphSubst, aeval_rename]
  have h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X := by
    funext j
    simp [Fin.append_left]
  rw [h, aeval_X_left_apply]

theorem graphSubst_surjective (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) :=
  fun q => ⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩

theorem isPrime_graphIdeal {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by
  have := hP
  unfold graphIdeal
  infer_instance

theorem ringKrullDim_graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))

theorem graphPt_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by
  intro q hq
  rw [← eval_graphSubst]
  exact hx _ hq

theorem firstPart_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h

theorem natAdd_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h

theorem eq_graphPt_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]

theorem proof (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm

end IsolatedFibreOpenPoly

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def WeierstrassDivisionAtPoint.Statement : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y₀ : τ → ℂ) (c : τ) (d : ℕ) (F g : (τ → ℂ) → ℂ),
    AnalyticAt ℂ F y₀ → AnalyticAt ℂ g y₀ →
    analyticOrderAt (fun s : ℂ => F (y₀ + Pi.single c s)) 0 = d →
    ∃ (q : (τ → ℂ) → ℂ) (a : Fin d → (τ → ℂ) → ℂ),
      AnalyticAt ℂ q y₀ ∧ (∀ j, AnalyticAt ℂ (a j) (zeroCoordinate c y₀)) ∧
      ∀ᶠ y in 𝓝 y₀, g y = q y * F y + ∑ j : Fin d, a j (zeroCoordinate c y) * (y c - y₀ c) ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
