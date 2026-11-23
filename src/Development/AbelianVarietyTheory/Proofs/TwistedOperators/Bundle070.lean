module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle063
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle068
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem normal_one (c : ℕ) (h : 0 + c = s) : IsNormalRep T ϖ 0 c h 1 := by
  refine ⟨0, 0, fun i => by simp, fun i => zero_mem _, ?_⟩
  rw [lat_bas hb]
  ext y
  simp [mem_normal, mem_latOf_one, mem_pow_zero]

include hϖ hψ hb hs hp hJ

theorem exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by
  induction j with
  | zero =>
    intro c h g hg
    rw [hA.zero] at hg
    obtain rfl : g = 1 := hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h g' hg'
    obtain ⟨g, hg, a, ha, hf⟩ := Set.mem_iUnion₂.1 ((hA.bij j c h).mapsTo hg')
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih _ _ g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c ψ ν _ _ g a hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ hψ he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) a) (hl ▸ om_per hϖ (hp _ _ _) (r * g) a) h0
    obtain ⟨r₃, hr₃, hl₃⟩ := lat_of_coset (hJ _ _ _) ha
    refine ⟨r₂ * r₃⁻¹, mul_mem hr₂ (inv_mem hr₃), e, z, he, hz, ?_⟩
    rw [lat_bas hb, latOf_mul_congr _ hl₃, ← hl₂]
    congr 1
    group

end GlobalTheory.LatClass
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  first | exact @GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | exact GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | (intros; apply GlobalTheory.PrCompactOpen.isCO_prX_Cgrp <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.isQuotInt_cosetFn_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  first | exact @GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | exact GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | (intros; apply GlobalTheory.CosetQuotInt.isQuotInt_cosetFn <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A C : Type} [Fintype A] [DecidableEq C]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_eq_add_offBlock (P : Finset C) (Y Y' : Matrix A C k) (T : Matrix A P k) :
    setCols P Y' T = setCols P Y T + setCols P (Y' - Y) 0 := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_of_add (P : Finset C) (Y : Matrix A C k) (x t : (Σ _ : A, P) → k) :
    setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩) =
      setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) + setCols P 0 (Matrix.of fun i j => t ⟨i, j⟩) := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_left (P : Finset C) (T : Matrix A P k) :
    Continuous fun Y : Matrix A C k => setCols P Y T := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]; exact continuous_const
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_id.matrix_elem i j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × ((Σ _ : A, P) → k) =>
      setCols P q.1 (Matrix.of fun i j => q.2 ⟨i, j⟩) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨i, ⟨j, h⟩⟩ : (Σ _ : A, P))).comp continuous_snd
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_fst.matrix_elem i j

omit [DecidableEq C] in
theorem continuous_pairCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × Matrix A P k => pairCols P q.1 q.2 := by
  unfold pairCols
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_snd.matrix_elem i j).mul (continuous_fst.matrix_elem i (j : C))

end GlobalTheory.ColFourier

theorem GlobalTheory.ColFourier.fourierInt_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΞ
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun Y => ?_, ?_⟩
  · have hK : IsCompact (restrictCols P '' tsupport Ξ) := hΞ.2.image (continuous_restrictCols P)
    have h1 : ∀ᶠ Y' in 𝓝 Y, ∀ X, Ξ (X + setCols P (Y' - Y) 0) = Ξ X := by
      have hc : Continuous (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) :=
        (continuous_setCols_left P 0).comp (continuous_id.sub continuous_const)
      have h0 : setCols P (Y - Y) (0 : Matrix A P k) = 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have ht : Filter.Tendsto (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) (𝓝 Y) (𝓝 0) := by
        convert hc.tendsto Y using 2
        exact h0.symm
      exact ht.eventually hinv
    have h2 : ∀ᶠ Y' in 𝓝 Y, ∀ T ∈ restrictCols P '' tsupport Ξ,
        ψ (pairCols P Y' T) = ψ (pairCols P Y T) := by
      refine hK.eventually_forall_of_forall_eventually fun T _ => ?_
      have h3 : IsLocallyConstant fun q : Matrix A C k × Matrix A P k =>
          (ψ (pairCols P q.1 q.2), ψ (pairCols P Y q.2)) :=
        (hψ.isLocallyConstant.comp_continuous (continuous_pairCols_pair P)).prodMk
          (hψ.isLocallyConstant.comp_continuous
            ((continuous_pairCols_pair P).comp (continuous_const.prodMk continuous_snd)))
      filter_upwards [h3.eventually_eq (Y, T)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1, h2] with Y' hY1 hY2
    unfold fourierInt
    congr 1
    funext T
    rw [setCols_eq_add_offBlock P Y Y' T, hY1]
    by_cases hT : setCols P Y T ∈ tsupport Ξ
    · rw [hY2 T ⟨_, hT, restrictCols_setCols P Y T⟩]
    · simp [image_eq_zero_of_notMem_tsupport hT]
  · have hc : Continuous fun t : (Σ _ : A, P) → k =>
        setCols P (0 : Matrix A C k) (Matrix.of fun i j => t ⟨i, j⟩) :=
      (continuous_setCols_pair P).comp (continuous_const.prodMk continuous_id)
    have h0 : setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩) = 0 := by
      ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
    have hU : {Z : Matrix A C k | ∀ X, Ξ (X + Z) = Ξ X} ∈
        𝓝 (setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩)) := by
      rw [h0]; exact hinv
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (hc.continuousAt.preimage_mem_nhds hU)
    refine HasCompactSupport.intro ((hΞ.2.prod (FourierPi.isCompact_box (1 * s⁻¹))).image
      (continuous_setCols_pair P)) fun Y hY => ?_
    rw [fourierInt_eq_pi]
    by_cases hy : (fun p : (Σ _ : A, P) => Y p.1 p.2) ∈ FourierPi.box (Σ _ : A, P) (1 * s⁻¹)
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      have hback : setCols P (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
          (Matrix.of fun i j => (fun p : (Σ _ : A, P) => Y p.1 p.2) ⟨i, j⟩) = Y := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have hX : setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) ∉ tsupport Ξ := fun hX =>
        hY ⟨(_, fun p => Y p.1 p.2), ⟨hX, hy⟩, hback⟩
      simp [image_eq_zero_of_notMem_tsupport hX]
    · refine FourierPi.fourier_eq_zero_pi (Measure.pi fun _ : (Σ _ : A, P) => m) hψ (s := s)
        (f := fun x => Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))) (fun t ht x => ?_) hy
      show Ξ (setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩)) = Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
      rw [setCols_of_add]
      exact hs ht _
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.SmGL.ContraTrace

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype

theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]

theorem res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)

theorem isAdmissible_contra [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩

theorem smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]

theorem contra_admissible_trace : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1

end GlobalTheory.SmGL.ContraTrace
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.exists_compact_preimage_embX_mul_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  first | exact @GlobalTheory.RootEx.ProperTriple.proper_triple | exact GlobalTheory.RootEx.ProperTriple.proper_triple | (intros; apply GlobalTheory.RootEx.ProperTriple.proper_triple <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
omit [DecidableEq n] in
theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in
theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

end Local

end GlobalTheory.InertSupp
end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem zipHom_isOpenEmbedding : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  intro κ X Y _ _ _ _ _
  let e : ((κ → X) × (κ → Y)) ≃ₜ (κ → X × Y) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i =>
        ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
      continuous_invFun :=
        (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_pi fun i => continuous_snd.comp (continuous_apply i)) }
  exact e.isOpenEmbedding

end GlobalTheory.ModuLR
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem finiteIntegers_compact_secondCountable_t2 : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), CompactSpace (OPart F S) ∧ SecondCountableTopology (OPart F S) ∧ T2Space (OPart F S) := by
  intro F _ _ S
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, CompactSpace (v.1.adicCompletionIntegers F) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    fun v => secondCountable_of_proper
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, SecondCountableTopology (v.1.adicCompletionIntegers F) :=
    fun v => TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.ModuLR
end
