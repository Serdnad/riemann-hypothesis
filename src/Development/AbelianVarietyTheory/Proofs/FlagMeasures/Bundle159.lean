module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteHermitianIsometricOfSameBadPrimes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFlagPairLatticeSumDiscriminantEqNormMinor
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009

@[expose] public section

section

open Formalism.HN Matrix NumberField Finset GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

noncomputable section

namespace GlobalTheory.SizeSubToQuot

theorem norm_proj_le_infDist {ι : Type} [Fintype ι] (P Q : Submodule ℂ (EuclideanSpace ℂ ι)) (h : Q ≤ P)
    (x : EuclideanSpace ℂ ι) :
    ‖Pᗮ.starProjection x‖ ≤ Metric.infDist x (Q : Set (EuclideanSpace ℂ ι)) := by
  rw [Metric.le_infDist ⟨0, Q.zero_mem⟩]
  intro y hy
  have h0 : Pᗮ.starProjection y = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (h hy)
  rw [dist_eq_norm, ← sub_zero (Pᗮ.starProjection x), ← h0, ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)


omit [_root_.NumberField.IsTotallyComplex K] in
theorem le_of_subset_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

theorem exists_frames_subspace (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) :
    ∃ (m : ℕ) (e : Module.Basis (Fin m) K U) (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ),
      (∀ v, IsUnit (Y v).det) ∧
      ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v (U.subtype x) = Formalism.HermitianLatticesTheory.normAt e Y v x := by
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  let e := Module.finBasis K U
  let T : InfinitePlace K → ((Fin (Module.finrank K U) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := fun v =>
    Fintype.linearCombination ℂ (fun k => WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (e k : V)))
  have hT : ∀ v (x : U), (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x : V)) : EuclideanSpace ℂ ι) =
      T v (fun k => v.embedding (e.repr x k)) := by
    intro v x
    have hx : (x : V) = ∑ k, e.repr x k • (e k : V) := by
      have h := congrArg U.subtype (e.sum_repr x)

      rw [map_sum] at h
      exact h.symm
    rw [hx, PlaceDecomposition.fcoord_lincomb, WithLp.toLp_sum]
    simp only [T, Fintype.linearCombination_apply, WithLp.toLp_smul]
  have hinj : ∀ v, Function.Injective (T v) := by
    intro v
    have hle : QuotientRealization.pv b X U v ≤ LinearMap.range (T v) := by
      rw [QuotientRealization.pv, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hT v ⟨y, hy⟩).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [QuotientRealization.finrank_pv b X hX] at h1
    have h4 := LinearMap.finrank_range_add_finrank_ker (T v)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h4
    have h5 : Module.finrank ℂ (LinearMap.ker (T v)) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 h5
  have hM := fun v => QuotientRealization.exists_mat (T v) (hinj v)
  choose M hMu hMn using hM
  refine ⟨_, e, fun v => (M v)⁻¹, fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v), fun v x => ?_⟩
  rw [Formalism.HermitianLatticesTheory.normAt, PlaceOperatorNorms.cnorm_eq, Submodule.subtype_apply, hT, ← hMn v]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
  rfl

theorem ptAt_mem_spanAt (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) : ptAt b X v y ∈ spanAt b X v S := by
  have h := Submodule.mem_map_of_mem
    (f := ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι))
    (QuotientRealization.fcoord_mem_span b X S v hy)
  rw [Submodule.map_span, Set.image_image] at h
  exact h

theorem size_ineq_to_quot (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) {A B B' : Submodule (𝓞 K) V}
    (hA : A.FG) (hB : B.FG) (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) B B') (hAB : ∀ y ∈ A, φ y ∈ B)
    (hne : ∃ y ∈ A, φ y ∉ B') {lo hi : ℝ} (hlo : 0 < lo)
    (hl : ∀ N, B' < N → N ≤ B → lo ≤ sizeQ b X N B') (hh : largestSize b X A ≤ hi)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hn : ∀ v, ∀ y ∈ Submodule.span K (A : Set V),
      distAt b X v B' (φ y) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v y) :
    lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  have hQ := quotRealize K V ι b X hX B B' hB hS
  set W := Submodule.span K (B' : Set V) with hW
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  set U := Submodule.span K (A : Set V) with hU
  obtain ⟨m, e, Y, hY, hiso⟩ := exists_frames_subspace b X hX U
  set A₀ : Submodule (𝓞 K) U := A.comap (U.subtype.restrictScalars (𝓞 K)) with hA₀
  have hmapA : A₀.map (U.subtype.restrictScalars (𝓞 K)) = A := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy
    · intro y hy
      exact ⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩
  have hA₀fg : A₀.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    rw [hmapA]; exact hA
  have hre := (rerealize K U (Fin m) V ι e Y b X U.subtype hY hX U.injective_subtype hiso A₀ hA₀fg).2.2.2.2.2.2
  rw [hmapA] at hre
  set ψ : U →ₗ[K] V ⧸ W := W.mkQ ∘ₗ φ ∘ₗ U.subtype with hψ
  set Bq := B.map (W.mkQ.restrictScalars (𝓞 K)) with hBq
  have hBfg : Bq.FG := hB.map _
  have hABq : A₀.map (ψ.restrictScalars (𝓞 K)) ≤ Bq := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hAB _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀'⟩ := hne
  have h0 : A₀.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    have h1 : ψ.restrictScalars (𝓞 K) ⟨y₀, Submodule.subset_span hy₀⟩ ∈
        A₀.map (ψ.restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hy₀
    rw [h0, Submodule.mem_bot] at h1
    have h2 : φ y₀ ∈ W := (Submodule.Quotient.mk_eq_zero W).1 h1
    have h3 : B ⊓ W.restrictScalars (𝓞 K) ≤ B' :=
      le_of_subset_span b X hX hB hS inf_le_left fun z hz => hz.2
    exact hy₀' (h3 ⟨hAB _ hy₀, h2⟩)
  have hA0 : A₀ ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hB0 : Bq ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hABq))
  have hM := sizeIneq K U (Fin m) _ κ e Y b' X' hY hX' ψ A₀ Bq hA₀fg hBfg hABq h0
  have hop : ∀ v, opNormAt e Y b' X' v ψ ≤ c v := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points e Y b' X' hY _ v (c v) (hc v) fun y => ?_
    rw [← hiso]
    refine le_trans ?_ (hn v y y.2)
    rw [hψ, LinearMap.comp_apply, hnorm]
    refine norm_proj_le_infDist _ _ ?_ _
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Submodule.subset_span hz, rfl⟩
  have hP : (∏ v, opNormAt e Y b' X' v ψ) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤
      (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
    Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _)
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hop v) (by positivity)
  have hleast : lo ≤ leastSize b' X' Bq := by
    refine le_csInf ⟨_, Bq, le_rfl, hB0, rfl⟩ ?_
    rintro _ ⟨N, hNB, hN0, rfl⟩
    set N' := B ⊓ N.comap (W.mkQ.restrictScalars (𝓞 K)) with hN'
    have hS0 : ∀ s ∈ B', W.mkQ s = 0 := fun s hs =>
      (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span hs)
    have hSN : B' ≤ N' := by
      intro s hs
      refine ⟨hS.1 hs, ?_⟩
      show W.mkQ s ∈ N
      rw [hS0 s hs]; exact N.zero_mem
    have hmap : N'.map (W.mkQ.restrictScalars (𝓞 K)) = N := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hy.2
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hNB hz
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
    have hne : B' ≠ N' := by
      intro h
      apply hN0
      rw [← hmap, ← h, eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact hS0 s hs
    have hlt := hl N' (lt_of_le_of_ne hSN hne) inf_le_left
    rwa [(hq N' hSN inf_le_left).2, hmap] at hlt
  have hpos : 0 < largestSize e Y A₀ := by
    rw [(sizeMu K U (Fin m) e Y hY A₀ hA₀fg hA0).2.2.2.2.1]; exact Real.exp_pos _
  refine le_trans ?_ (hM.trans hP)
  exact div_le_div₀ (hlo.le.trans hleast) hleast hpos (hre ▸ hh)

end General

theorem size_ineq_sub_to_quot : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) → ∀ (φ : Matrix (Fin n) (Fin n) K) (A B B' : Submodule (𝓞 K) (Fin n → K)), A.FG → B.FG → IsSat (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X) B B' → (∀ y ∈ A, φ *ᵥ y ∈ B) → (∃ y ∈ A, φ *ᵥ y ∉ B') → ∀ lo hi : ℝ, 0 < lo → (∀ N, B' < N → N ≤ B → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N B') → largestSize (Pi.basisFun K (Fin n)) X A ≤ hi → ∀ c : InfinitePlace K → ℝ, (∀ v, 0 ≤ c v) → (∀ v, ∀ u ∈ spanAt (Pi.basisFun K (Fin n)) X v A, Metric.infDist (Matrix.toEuclideanLin ((X v)⁻¹ * φ.map v.embedding * X v) u) (spanAt (Pi.basisFun K (Fin n)) X v B' : Set (EuclideanSpace ℂ (Fin n))) ≤ c v * ‖u‖) → lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  intro K _ _ _ _ n X hX φ A B B' hA hB hS hAB hne lo hi hlo hl hh c hc hn
  refine size_ineq_to_quot (Pi.basisFun K (Fin n)) X hX (Matrix.toLin' φ) hA hB hS hAB hne hlo hl hh c hc
    fun v y hy => ?_
  have h := hn v _ (ptAt_mem_spanAt (Pi.basisFun K (Fin n)) X A v hy)
  rw [norm_ptAt] at h
  refine le_trans (le_of_eq ?_) h
  unfold distAt ptAt
  rw [PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rfl

end GlobalTheory.SizeSubToQuot
end
end

section

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.LowVec

variable {k r : ℕ}

abbrev flagSpan (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem mem_flagSpan {a : Fin (r + 1)} {y : Fin (2 * r + k + 1) → ℂ} :
    y ∈ flagSpan k r a ↔ ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
  constructor
  · intro hy i hi
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have := b.2
      exact Pi.single_eq_of_ne (fun e => by rw [e] at hi; simp only [eI] at hi; omega) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a.val ≤ i.val
    · rw [hy i hi, Pi.single_zero]; exact Submodule.zero_mem _
    · have ha := a.isLt
      have : (Pi.single i (y i) : Fin (2 * r + k + 1) → ℂ) = y i • bvec (eI k r ⟨i.val, by omega⟩) := by
        rw [bvec, ← Pi.single_smul, smul_eq_mul, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, by simpa using hi⟩, rfl⟩)

theorem mulVec_sub {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z)
    (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ flagSpan k r a) :
    ∃ y' ∈ flagSpan k r a, s *ᵥ (fvec k r z a - y) = fvec k r z a - y' := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hc := ((WeylGroupFacts.nset_iff m).1 hm).2
  have ha := a.isLt
  have h1 : fvec k r z a - m *ᵥ (fvec k r z a - y) ∈ flagSpan k r a := by
    refine mem_flagSpan.2 fun i hi => ?_
    have : (m *ᵥ (fvec k r z a - y)) i = ((1 : Mat k r) *ᵥ (fvec k r z a - y)) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
      · rw [hc i j hj.1 hj.2, Matrix.one_apply]
      · have e1 : y j = 0 := mem_flagSpan.1 hy j (by omega)
        have e2 : fvec k r z a j = 0 := by
          unfold fvec
          split_ifs with h'
          · exact Pi.single_eq_of_ne (fun e => by rw [e] at hj; simp only [eI] at hj; omega) _
          · exact hz j (by omega)
        simp [e1, e2]
    rw [Pi.sub_apply, this, Matrix.one_mulVec, Pi.sub_apply, mem_flagSpan.1 hy i hi]; ring
  have h2 : ∀ x ∈ flagSpan k r a, h *ᵥ x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact (hh.2.1 b.1).1
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  have h3 : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with h'
    · exact (hh.2.1 _).1
    · exact hh.2.2
  refine ⟨_, h1, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have := h2 _ h1
  rw [Matrix.mulVec_sub, h3] at this
  rw [sub_sub_cancel]
  exact sub_right_injective this

theorem lA_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z) (g : Mat k r)
    (a : Fin (r + 1)) : lA k r z (s * g) a = lA k r z g a := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hu : IsUnit s.det := by
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    rw [Matrix.det_mul]
    exact ((uHGroup _ _ hH).2.2 h hh.1).1.mul ((uHGroup _ _ hH).2.2 m hm.1).1
  unfold lA
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz ((sGroup k r z hz).2.2 s hs) a hy
    exact ⟨y', hy', by rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz hs a hy
    refine ⟨y', hy', ?_⟩
    rw [← e, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem eucl_unitary {N : ℕ} {t : Matrix (Fin N) (Fin N) ℂ} (ht : t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (v : Fin N → ℂ) : eucl (t *ᵥ v) = eucl v := by
  have e : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := fun v => by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have h1 : tᴴ * t = 1 := Matrix.mem_unitaryGroup_iff'.1 ht
  unfold eucl
  congr 1
  apply Complex.ofReal_injective
  rw [e, e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

theorem lA_right (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) {t : Mat k r}
    (ht : t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lA k r z (g * t) a = lA k r z g a := by
  have h1 : t⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ht)]
    exact Unitary.star_mem ht
  unfold lA
  simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, eucl_unitary h1]

end GlobalTheory.Mom.LowVec
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.definite_hermitian_isometric_of_same_bad_primes : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → PD h' → Module.finrank K V = Module.finrank K V' → ∀ (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V'), IsMaxLat h M → IsMaxLat h' M' → badP h M = badP h' M' → ∃ e : V ≃ₗ[K] V', ∀ x y, h' (e x) (e y) = h x y := by
  first | exact @GlobalTheory.Mass.SameBad.main | exact GlobalTheory.Mass.SameBad.main | (intros; apply GlobalTheory.Mass.SameBad.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitStabilizerMass_subspace_cyclicDiscriminant_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  first | exact @GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | exact GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | (intros; apply GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLattice_carry_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Carry.carry_iff | exact GlobalTheory.St.G.Carry.carry_iff | (intros; apply GlobalTheory.St.G.Carry.carry_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dual_lattice_local_characterization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat (dualL cm.sig J L) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F), x ∈ loc v (dualL cm.sig J L) ↔ ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) z x ∈ intV E v) ∧ ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F (dualL cm.sig J L) ↔ ∀ z ∈ hat F L, hR cm.sig J (Ad F) z x ∈ OAd F E := by
  first | exact @GlobalTheory.St.G.dualL_local_adelic | exact GlobalTheory.St.G.dualL_local_adelic | (intros; apply GlobalTheory.St.G.dualL_local_adelic <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_embedded_hermData_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  first | exact @GlobalTheory.DegCnt.encard_isDat_le | exact GlobalTheory.DegCnt.encard_isDat_le | (intros; apply GlobalTheory.DegCnt.encard_isDat_le <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_sublattices_definiteQuotient_normalForm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  first | exact @GlobalTheory.DegCnt.count_sublattices_definite | exact GlobalTheory.DegCnt.count_sublattices_definite | (intros; apply GlobalTheory.DegCnt.count_sublattices_definite <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt

theorem _root_.GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  first | exact @GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | exact GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn | (intros; apply GlobalTheory.DegCnt.NF.ref_mem_of_mem_Wn <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_sublattices_index_fixed_trace_le : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  first | exact @GlobalTheory.TraceCount.main | exact GlobalTheory.TraceCount.main | (intros; apply GlobalTheory.TraceCount.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (s : V ≃ₗ[K] V), s ∈ isomGrp H → ∃ N' : NF H r, (∀ a, N'.F.e a = s (N.F.e a) ∧ N'.F'.e a = s (N.F'.e a)) ∧ N'.j = N.j ∧ N'.c = N.c ∧ N'.T = N.T ∧ N'.𝔡 = N.𝔡 ∧ (∀ l, N'.nD l = N.nD l) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), N'.om (s • Λ) = N.om Λ ∧ (N'.IsTerm g (s • Λ) ↔ N.IsTerm g Λ) ∧ N'.gI g (s • Λ) = N.gI g Λ := by
  first | exact @GlobalTheory.DegMove.exists_moved | exact GlobalTheory.DegMove.exists_moved | (intros; apply GlobalTheory.DegMove.exists_moved <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFlagPairLatticeSumDiscriminant_eq_norm_minor : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ l ≤ N.j, N.nD l ≠ 0 → normD N.F N.F' Λ l = N.nD l ∧ 1 ≤ N.nD l := by
  first | exact @GlobalTheory.DegCnt.FlagDisc.main | exact GlobalTheory.DegCnt.FlagDisc.main | (intros; apply GlobalTheory.DegCnt.FlagDisc.main <;> assumption)
end
