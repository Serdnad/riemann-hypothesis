module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_frames

open MvPolynomial Filter Topology

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X)
    {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hx' : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simp [Set.mem_preimage, (A.chart j).left_inv hj, hx]⟩
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x := by
    refine ContinuousAt.comp ?_ ((A.chart j).continuousAt hj)
    exact (hf j _ hx').continuousAt
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = mCoordIdeal z := by
  classical
  let φ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  let ψ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    simp only [φ, ψ, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hcomp : (mConeMap (fun p : Σ k, ι k => c p.1 * z p)) = (φ.restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, φ, C_mul]
    ring
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, AlgHom.coe_toRingHom, hcomp]
  constructor
  · intro h
    have h' := congrArg ψ h
    have e := AlgHom.congr_fun hψφ (mConeMap z f)
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at e
    simpa [e] using h'
  · intro h
    simp [h]

theorem X_notMem_iff (w : (Σ k, ι k) → ℂ) (q : Σ k, ι k) :
    (X q : MRing ι) ∉ mCoordIdeal w ↔ w q ≠ 0 := by
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, MvPolynomial.X_ne_zero]

theorem eventually_notMem {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) {w₀ : (Σ k, ι k) → ℂ}
    (h0 : h ∉ mCoordIdeal w₀) : ∀ᶠ w in 𝓝 w₀, h ∉ mCoordIdeal w := by
  have hiff : ∀ w : (Σ k, ι k) → ℂ, h ∈ mCoordIdeal w ↔
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) = 0 := by
    intro w
    rw [form_mem_mCoordIdeal_iff w hh, aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]
  have hc : Continuous fun w : (Σ k, ι k) → ℂ => MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have h0' : MvPolynomial.eval w₀ (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 := fun e => h0 ((hiff w₀).mpr e)
  filter_upwards [hc.continuousAt.eventually_ne h0'] with w hw
  exact fun hm => hw ((hiff w).mp hm)

theorem eventually_regAt {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {s : Ω} {w₀ : (Σ k, ι k) → ℂ}
    (hs : RegAt x (mCoordIdeal w₀) s) : ∀ᶠ w in 𝓝 w₀, RegAt x (mCoordIdeal w) s := by
  obtain ⟨d, g, h, hg, hh, hQ, e⟩ := hs
  filter_upwards [eventually_notMem hh hQ] with w hw
  exact ⟨d, g, h, hg, hh, hw, e⟩

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem eventually_goodAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {w₀ : (Σ k, baseIdx ι M.blk k) → ℂ} (hF : M.GoodAt F (mCoordIdeal w₀)) :
    ∀ᶠ w in 𝓝 w₀, M.GoodAt F (mCoordIdeal w) := by
  obtain ⟨h1, h2, h3⟩ := hF
  have e1 : ∀ᶠ w in 𝓝 w₀, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal w := by
    refine Filter.eventually_all.2 fun k => ?_
    have h := (X_notMem_iff w₀ _).1 (h1 k)
    filter_upwards [(continuous_apply (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k)).continuousAt.eventually
      (isOpen_ne.mem_nhds h)] with w hw
    exact (X_notMem_iff w _).2 hw
  have e2 : ∀ᶠ w in 𝓝 w₀, ∀ q I, RegAt M.x (mCoordIdeal w) (F.u q I) ∧ RegAt M.x (mCoordIdeal w) (F.u' I q) :=
    Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun I =>
      (eventually_regAt (h2 q I).1).and (eventually_regAt (h2 q I).2)
  have e3 : ∀ᶠ w in 𝓝 w₀, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal w) (F.υ p) ∧
      RegAt M.x (mCoordIdeal w) (F.υ p)⁻¹ := by
    refine Filter.eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := h3 p hp
      filter_upwards [eventually_regAt b, eventually_regAt c] with w hb hc
      exact fun _ => ⟨a, hb, hc⟩
    · exact Filter.Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [e1, e2, e3] with w a b c
  exact ⟨a, b, c⟩

end PositivityTheory.Xgp.c_bm_exists_frames

theorem PositivityTheory.Xgp.t_c_bm_exists_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j n M Rb
  classical
  letI := Rb.top
  haveI := Rb.compact
  haveI := Rb.t2
  have key : ∀ x : Rb.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (t : Set Rb.X), M.IsFrame F ∧ t ∈ nhds x ∧
      IsClosed t ∧ ∀ z ∈ t, M.GoodAt F (mCoordIdeal (Rb.lift z z)) := by
    intro x
    have hw := Rb.mem x x (Rb.mem_U x)
    have hrel : IsRelevant (mCoordIdeal (Rb.lift x x)) := by
      intro k
      obtain ⟨i, hi⟩ := hw.1 k
      exact ⟨i, (PositivityTheory.Xgp.c_bm_exists_frames.X_notMem_iff _ _).mpr hi⟩
    obtain ⟨F, hFr, hG⟩ := M.frames _ (ValRing.isPrime_mCoordIdeal _) hrel (CPts.mCoordIdeal_le hw)
    have hcont : ContinuousAt (Rb.lift x) x := continuousAt_pi.mpr fun p =>
      PositivityTheory.Xgp.c_bm_exists_frames.continuousAt_of_holoOn Rb.A (Rb.holo x p) (Rb.mem_U x)
    have hev : ∀ᶠ z in nhds x, M.GoodAt F (mCoordIdeal (Rb.lift x z)) :=
      hcont.tendsto.eventually (PositivityTheory.Xgp.c_bm_exists_frames.eventually_goodAt M F hG)
    have hS : {z | z ∈ Rb.U x ∧ M.GoodAt F (mCoordIdeal (Rb.lift z z))} ∈ nhds x := by
      filter_upwards [hev, (Rb.isOpen_U x).mem_nhds (Rb.mem_U x)] with z hz hU
      refine ⟨hU, ?_⟩
      obtain ⟨c, hc, hceq⟩ := Rb.compat x z z ⟨hU, Rb.mem_U z⟩
      have e := PositivityTheory.Xgp.c_bm_exists_frames.mCoordIdeal_smul c hc (Rb.lift z z)
      rw [← hceq] at e
      rw [e] at hz
      exact hz
    obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hS
    exact ⟨F, t, hFr, ht, htc, fun z hz => (hts hz).2⟩
  choose F t hFr ht htc hgood using key
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (t x))
    (fun x => isOpen_interior)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (ht x)⟩)
  let e := s.equivFin
  refine ⟨s.card, fun l => interior (t (e.symm l)), fun l => F (e.symm l), fun l => isOpen_interior, ?_,
    fun l => hFr _, ?_⟩
  · intro x
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨e ⟨i, hi⟩, by simpa using hx⟩
  · intro l x hx
    exact hgood _ x (closure_minimal interior_subset (htc _) hx)
end

section

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {N j : ℕ}

theorem exists_selector (R : Type) [CommRing R] (hj : j ≤ N) (i : Fin N) {I' : Finset (Fin N)}
    (hI : IsStepRows N j i I') : ∃ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h ∧
      ∀ I, minorIJ h I (stepCols N j i) = if I = I' then 1 else 0 := by
  refine ⟨Matrix.of fun a b => if ∃ s, a = I'.orderEmbOfFin hI.1 s ∧ b = (stepCols N j i).orderEmbOfFin rfl s
    then 1 else 0, fun a b hab => ?_, fun I => ?_⟩
  · rw [Matrix.of_apply, if_neg]
    rintro ⟨s, rfl, rfl⟩
    have h1 := hI.2 (I'.orderEmbOfFin_mem hI.1 s)
    have h2 := mem_stepCols_block hj ((stepCols N j i).orderEmbOfFin_mem rfl s)
    apply hab
    split_ifs at h1 h2 with h
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases e : I = I'
    · subst e
      rw [if_pos rfl, minorIJ, dite_eq_left hI.1]
      refine Eq.trans (congrArg Matrix.det ?_) Matrix.det_one
      ext s t
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨s, rfl, rfl⟩
    · rw [if_neg e]
      by_cases c : I.card = (stepCols N j i).card
      · have hs : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by rw [c, hI.1]))
        obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
        refine minorIJ_eq_zero_of_row _ ha fun b _ => ?_
        rw [Matrix.of_apply, if_neg]
        rintro ⟨s, rfl, -⟩
        exact has (I'.orderEmbOfFin_mem hI.1 s)
      · exact minorIJ_of_card_ne _ c

theorem minorIJ_conjTranspose (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) :
    minorIJ hᴴ J I = star (minorIJ h I J) := by
  by_cases e : I.card = J.card
  · rw [minorIJ_eq_det h I J _ e rfl, minorIJ_eq_det hᴴ J I _ rfl e, ← Matrix.det_conjTranspose]
    rfl
  · rw [minorIJ_of_card_ne h e, minorIJ_of_card_ne hᴴ (Ne.symm e), star_zero]

theorem gram_minor {G h g : Matrix (Fin N) (Fin N) ℂ} {C : Finset (Fin N)} {a l : ℂ}
    (e : ∀ I, a * minorIJ h I C = l * minorIJ g I C) :
    ‖a‖ ^ 2 * (minorIJ (hᴴ * G * h) C C).re = ‖l‖ ^ 2 * (minorIJ (gᴴ * G * g) C C).re := by
  have key : ∀ (b : ℂ) (f : Matrix (Fin N) (Fin N) ℂ), star b * b * minorIJ (fᴴ * G * f) C C =
      ∑ I', ∑ I, star (b * minorIJ f I C) * minorIJ G I I' * (b * minorIJ f I' C) := by
    intro b f
    rw [minorIJ_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [minorIJ_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [minorIJ_conjTranspose, star_mul]
    ring
  have h1 := key a h
  simp only [e] at h1
  rw [← key l g] at h1
  have n : ∀ b : ℂ, star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := fun b => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [n, n] at h1
  simpa only [Complex.re_ofReal_mul] using congrArg Complex.re h1

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (C : Finset (Fin N)) : 0 < minorIJ G C C := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (C.orderEmbOfFin rfl).injective).det_pos

theorem detFac_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (i : Fin N) : 0 < (detFac j i G).re := by
  have : 0 < detFac j i G := by
    unfold detFac
    refine mul_pos ?_ ?_ <;> split_ifs
    exacts [minor_pos hG _, one_pos, minor_pos hG _, one_pos]
  exact (Complex.pos_iff.1 this).1

theorem gram_pos {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hh : h.det ≠ 0) (C : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * G * h) C C).re := by
  have : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  exact (Complex.pos_iff.1 (minor_pos this C)).1

theorem detFac_conjTranspose (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) :
    detFac j i hᴴ = star (detFac j i h) := by
  unfold detFac
  rw [minorIJ_conjTranspose, minorIJ_conjTranspose, star_mul']
  split_ifs <;> simp

theorem log_detFac (hj : j ≤ N) (i : Fin N) {G R : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (bG : IsBlockDiag j G)
    (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    (1 / 2) * Real.log (detFac j i (Rᴴ * G * R)).re =
      (1 / 2) * Real.log (detFac j i G).re + Real.log ‖detFac j i R‖ := by
  have h0 := norm_ne_zero_iff.2 (detFac_ne_zero hj i bR hR)
  have e : detFac j i (Rᴴ * G * R) = ((‖detFac j i R‖ ^ 2 : ℝ) : ℂ) * detFac j i G := by
    rw [detFac_mul i bR, detFac_mul i bG, detFac_conjTranspose, mul_right_comm, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [e, Complex.re_ofReal_mul, Real.log_mul (pow_ne_zero _ h0) (detFac_pos hG i).ne', Real.log_pow]
  push_cast; ring

theorem pot_step (hj : j ≤ N) (i : Fin N) (hi : IsProperStep N j i) {G R h h' : Matrix (Fin N) (Fin N) ℂ}
    (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) (hh : h.det ≠ 0)
    (hh' : h'.det ≠ 0) {a a' μ : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hμ : μ ≠ 0)
    (e : ∀ I, a * minorIJ h I (stepCols N j i) = a' * detFac j i R * μ * minorIJ (R * h') I (stepCols N j i)) :
    Real.log ‖a‖ + blockPot j i G h = Real.log ‖a'‖ + Real.log ‖μ‖ + blockPot j i (Rᴴ * G * R) h' := by
  have h0 := detFac_ne_zero hj i bR hR
  have h1 := gram_minor (G := G) e
  have p1 := gram_pos hG hh (stepCols N j i)
  have p2 := gram_pos hG (h := R * h') (by rw [Matrix.det_mul]; exact mul_ne_zero hR hh') (stepCols N j i)
  have h2 := congrArg Real.log h1
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha)) p1.ne',
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (mul_ne_zero (mul_ne_zero ha' h0) hμ))) p2.ne',
    Real.log_pow, Real.log_pow, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)) (norm_ne_zero_iff.2 hμ),
    Real.log_mul (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)] at h2
  have e2 : h'ᴴ * (Rᴴ * G * R) * h' = (R * h')ᴴ * G * (R * h') := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold blockPot
  rw [if_pos hi, if_pos hi, log_detFac hj i hG bG bR hR, e2]
  push_cast at h2
  linarith

theorem pot_base (hj : j ≤ N) (i : Fin N) (hi : ¬ IsProperStep N j i) {G R : Matrix (Fin N) (Fin N) ℂ}
    (h h' : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    blockPot j i (Rᴴ * G * R) h' = blockPot j i G h + Real.log ‖detFac j i R‖ := by
  unfold blockPot
  rw [if_neg hi, if_neg hi, log_detFac hj i hG bG bR hR]
  ring

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (A : Matrix (Fin N) (Fin N) R) :
    detFac j i (A.map f) = f (detFac j i A) := by
  unfold detFac
  rw [minorIJ_map, minorIJ_map, map_mul]
  split_ifs <;> simp

theorem pot_conj (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    blockPot j i (G.map (starRingEnd ℂ)) (h.map (starRingEnd ℂ)) = blockPot j i G h := by
  have e : (h.map (starRingEnd ℂ))ᴴ * G.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) =
      (hᴴ * G * h).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold blockPot
  rw [e, detFac_map, minorIJ_map, Complex.conj_re, Complex.conj_re]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end
