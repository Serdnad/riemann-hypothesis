module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle030
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle036
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem mem_N_of_succ {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rcases r with a | l <;> rcases s with b | j
  · exact hg _ _ (by simp [lev])
  · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    by_cases hp : l.val + 1 = p
    · rw [h0 l b hp]
      simp
    · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact hg _ _ (by simpa [lev] using hrs)

theorem inv_rowE_val (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := rfl

theorem succ_decomp : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  intro k _ n _ _ c p g hg
  set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0
    with hu
  have hE : rowE c p u ∈ N k n c (p + 1) := rowE_mem u (Nat.lt_succ_self p)
  have h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1) := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)
  refine ⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩
  refine mem_N_of_succ h1 ?_
  intro l s hl
  have hg' := (mem_N_iff g).1 hg
  have key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l) :=
    fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩
  have hd : g.val (Sum.inr l) (Sum.inr l) = 1 := by
    have := hg' (Sum.inr l) (Sum.inr l) le_rfl
    simpa using this
  have hus : u s = g.val (Sum.inr l) (Sum.inl s) := by
    simp only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply,
    Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hus]
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hd]
  ring

end GlobalTheory.RootEx.RadicalDecomp
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise

namespace GlobalTheory.RootEx.QuotLinear

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem isClosed_N : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = ⋂ r, ⋂ s, ⋂ (_ : lev p s ≤ lev p r),
      {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
    ext g
    simp only [SetLike.mem_coe, Radical.mem_N_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq ?_ continuous_const
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

theorem continuous_embX : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  change Continuous fun x : GL n k => (fromBlocks x.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  exact Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const continuous_const

theorem exists_compact_prod {K : Set (GL (n ⊕ Fin c) k)} (hK : IsCompact K) :
    ∃ (A : Set (GL n k)) (B : Set (N k n c p)), IsCompact A ∧ IsCompact B ∧
      ∀ (x : GL n k) (u : N k n c p), embX c x * (u : GL (n ⊕ Fin c) k) ∈ K → x ∈ A ∧ u ∈ B := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
    fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
  have hb : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem _ _
  have hφ : Continuous φ :=
    (hb.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hb.comp Units.continuous_coe_inv))
  have hA := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.image hφ)
  have hB := (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hA.image (continuous_embX (c := c))).inv.mul hK)
  refine ⟨_, _, hA, hB, fun x u h => ?_⟩
  have hx : x ∈ (Units.embedProduct (Matrix n n k)) ⁻¹' (φ '' K) := by
    refine ⟨_, h, ?_⟩
    have e : (embX c x * (u : GL (n ⊕ Fin c) k))⁻¹ =
        embX c x⁻¹ * (embX c x * (u : GL (n ⊕ Fin c) k)⁻¹ * (embX c x)⁻¹) := by
      rw [map_inv]; group
    simp only [φ]
    rw [e, Radical.toBlocks₁₁_embX_mul x u.2,
      Radical.toBlocks₁₁_embX_mul x⁻¹ (Radical.conj_mem x (inv_mem u.2))]
    rfl
  refine ⟨hx, ?_⟩
  refine ⟨(embX c x)⁻¹, ?_, _, h, by simp⟩
  rw [Set.mem_inv, inv_inv]
  exact ⟨x, hx, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem finiteOnCompacts_volN (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (volN ν n c p) := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨fun K hK => ?_⟩
  unfold volN
  rw [(Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]
  refine (hK.image ?_).measure_lt_top
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

theorem integrable_average (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    (∀ x : GL n k, Integrable (fun u : N k n c p => F (embX c x * (u : GL (n ⊕ Fin c) k) * h)) (volN ν n c p)) ∧
    Integrable (fun x : GL n k =>
      ∫ u : N k n c p, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) μX := by
  haveI := finiteOnCompacts_volN (n := n) (c := c) (p := p) ν
  haveI : LocallyCompactSpace (N k n c p) :=
    (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c p) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c p) := sigmaFinite_of_locallyFinite
  have hK : IsCompact ((fun g => g * h⁻¹) '' tsupport F) := hF.2.isCompact.image (by fun_prop)
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_compact_prod (p := p) hK
  have hz : ∀ (x : GL n k) (u : N k n c p), ¬ (x ∈ A ∧ u ∈ B) →
      F (embX c x * (u : GL (n ⊕ Fin c) k) * h) = 0 := fun x u hn => by
    by_contra h0
    exact hn (hAB x u ⟨_, subset_tsupport _ h0, by simp⟩)
  have hc : Continuous fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h) :=
    hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const)
  refine ⟨fun x => ?_, ?_⟩
  · exact (hc.comp (Continuous.prodMk_right x)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hB fun u hu => hz x u fun h => hu h.2)
  · have hi : Integrable (fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h))
        (μX.prod (volN ν n c p)) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hA.prod hB) fun z hz' => hz z.1 z.2 hz')
    exact hi.integral_prod_left

theorem isQuotInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f f' : GL (n ⊕ Fin c) k → ℂ) (a z z' : ℂ), IsQuotInt ν μX μG p f z → IsQuotInt ν μX μG p f' z' → IsQuotInt ν μX μG p (fun h => a * f h + f' h) (a * z + z') := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν _ μX _ μG _ f f' a z z' ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩
  refine ⟨a • F + F', add_mem (Submodule.smul_mem _ a hF) hF', fun h => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := integrable_average (p := p) ν μX hF h
    obtain ⟨j1, j2⟩ := integrable_average (p := p) ν μX hF' h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h1', ← integral_const_mul, ← integral_add (i2.const_mul a) j2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_add ((i1 x).const_mul a) (j1 x), integral_const_mul]
  · have i : Integrable F μG := hF.1.continuous.integrable_of_hasCompactSupport hF.2
    have j : Integrable F' μG := hF'.1.continuous.integrable_of_hasCompactSupport hF'.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i.const_mul a) j, integral_const_mul, h2, h2']

end GlobalTheory.RootEx.QuotLinear
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx

theorem integral_mul_mem_SB {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [R1Space X]
    [MeasurableSpace E] (μ : Measure E) (G : X × E → ℂ) (hG : G ∈ SB (X × E)) (χ : E → ℂ) :
    (fun x => ∫ e, G (x, e) * χ e ∂μ) ∈ SB X := by
  obtain ⟨h1, h2⟩ := hG
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have hK : IsCompact (Prod.snd '' tsupport G) := h2.isCompact.image continuous_snd
    have h := hK.eventually_forall_of_forall_eventually (x₀ := x₀)
      (P := fun x y => G (x, y) = G (x₀, y)) (by
        intro y _
        have ha := h1.eventually_eq (x₀, y)
        have hc : Continuous fun z : X × E => ((x₀, z.2) : X × E) := by fun_prop
        have hb := (h1.comp_continuous hc).eventually_eq (x₀, y)
        filter_upwards [ha, hb] with z hz hz'
        exact hz.trans hz'.symm)
    filter_upwards [h] with x hx
    congr 1
    funext e
    by_cases he : e ∈ Prod.snd '' tsupport G
    · rw [hx e he]
    · have : ∀ x', G (x', e) = 0 := fun x' =>
        image_eq_zero_of_notMem_tsupport fun h' => he ⟨_, h', rfl⟩
      rw [this, this]
  · refine HasCompactSupport.intro (h2.isCompact.image continuous_fst) fun x hx => ?_
    have : ∀ e, G (x, e) = 0 := fun e =>
      image_eq_zero_of_notMem_tsupport fun h' => hx ⟨_, h', rfl⟩
    simp [this]

section
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}

theorem affPt_of_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by
  obtain ⟨⟨r, s⟩, h⟩ := rs
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
  congr 1
  rcases r with r | r <;> rcases s with s | s
  · exact h.elim
  all_goals rfl

theorem affPt_inl_inl (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by
  simp [affPt, basePt, Free]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_affPt_uncurry (p : ℕ) :
    Continuous fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt p z.1 z.2 := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · have := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt_of_free p z.1 z.2 ⟨(r, s), h⟩
    simp only at this
    simp only [this]
    fun_prop
  · simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | r <;> rcases s with s | s
    · exact continuous_fst.matrix_elem r s
    all_goals exact continuous_const

theorem isClosedEmbedding_affPt_uncurry [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k),
        fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} =>
          M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2)) ?_ ?_
    (continuous_affPt_uncurry p)
  · rintro ⟨x, e⟩
    refine Prod.ext ?_ ?_
    · ext r s
      simp [affPt_inl_inl]
    · funext rs
      simp [affPt_of_free]
  · refine Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_
    exact continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const

theorem comp_affPt_mem_SB [T2Space k] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) ∈ SB _ :=
  ⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p),
    hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩

end

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}


open scoped Classical in
open Classical in
theorem integrable_opE_integrand (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc : Continuous fun e => affPt (c := c) p x₀ e :=
    (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
    exact continuous_finsetSum _ fun i _ => hc.matrix_elem _ _
  · refine HasCompactSupport.mul_right ?_
    have h2 := (comp_affPt_mem_SB p hΦ).2
    refine HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩


omit [BorelSpace k] [DecidableEq n] [DecidableEq n'] in
theorem opE_mem_SB (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : opE ψ ν p Φ ∈ SB (Matrix n n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  exact integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ)
    (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))

theorem opE_smul_add (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] (z : ℂ) {Φ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by
  funext x₀
  have h1 := (integrable_opE_integrand p hψ ν hΦ x₀).const_mul z
  have h2 := integrable_opE_integrand p hψ ν hΨ x₀
  simp only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1
  funext e
  ring

end

theorem opE_SB_and_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure], (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p Φ ∈ SB (Matrix n n' k)) ∧ ∀ (z : ℂ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ p ψ hψ ν _ =>
    ⟨fun _ hΦ => opE_mem_SB p ψ ν hΦ, fun z _ hΦ _ hΨ => opE_smul_add p hψ ν z hΦ hΨ⟩

end GlobalTheory.RootEx
end
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem affine_mul_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (d : ℕ) (p q : A) (c : ℕ → A) :
    ∃ c' : ℕ → A, c' (d + 1) = p * c d ∧ ∀ u : ℂ, (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • c' i := by
  refine ⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A)
    + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (p q : Fin t → A) :
    ∃ c : ℕ → A, c t = (List.ofFn p).prod ∧ ∀ u : ℂ, (List.ofFn fun k => u • p k + q k).prod
      = ∑ i ∈ range (t + 1), u ^ i • c i := by
  induction t with
  | zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩
  | succ t ih =>
    obtain ⟨c, hct, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    obtain ⟨c', hct', hc'⟩ := affine_mul_polyMap_top t (p 0) (q 0) c
    refine ⟨c', ?_, fun u => ?_⟩
    · rw [hct', hct, List.ofFn_succ, List.prod_cons]
    · rw [List.ofFn_succ, List.prod_cons, hc u, hc' u]

theorem qdet_polyMap_monic (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  have h : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℕ → A,
      c n = (List.ofFn fun k : Fin n => if σ k = k then (1 : A) else 0).prod ∧ ∀ u : ℂ,
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (n + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hct, hc⟩ := prod_affine_polyMap_top n
      (fun k => if σ k = k then (1 : A) else 0)
      (fun k => Tm E (-(k : ℂ)) (σ k) k)
    refine ⟨c, hct, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Tm
    simp only [id]
    split_ifs
    · rw [← add_assoc, ← Algebra.algebraMap_eq_smul_one, ← map_add (f := _)]
      congr 2
      all_goals ring
    · simp
  choose c hct hc using h
  have htop : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → c σ n = 0 := by
    intro σ hσ
    rw [hct σ]
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext hne)
    apply List.prod_eq_zero
    rw [List.mem_ofFn]
    exact ⟨k, if_neg hk⟩
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [hct 1]
      simp
    · intro σ _ hσ
      rw [htop σ hσ, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  · unfold qdet qminor
    simp only [hc, mul_sum, smul_sum, mul_smul_comm]
    exact sum_comm

end GlobalTheory
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  first | exact @GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | exact GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | (intros; apply GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.rightConv_eq_smul_of_inner_translates_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ {H : Subgroup G} (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → (∀ γ ∈ Γ, ∀ x, φ (γ * x) = φ x) → ∀ c : ℂ, (∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = c * ∫ x in 𝓕, star (φ (x * (h' : G))) * φ x ∂μ) → ∀ x, ∫ h, α h * φ (x * (h : G)) ∂m = c * φ x := by
  first | exact @GlobalTheory.rightConv_eq_smul_of_inner_translates | exact GlobalTheory.rightConv_eq_smul_of_inner_translates | (intros; apply GlobalTheory.rightConv_eq_smul_of_inner_translates <;> assumption)
end
