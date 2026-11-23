module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.SemilocalColumn

private lemma exists_sub_iota_mem_of_sub_involution_mem (A : Type) [CommRing A] [Finite (MaximalSpectrum A)]
    (y : MaximalSpectrum A → A) : ∃ a : A, ∀ M : MaximalSpectrum A, a - y M ∈ M.asIdeal := by
  have hcop : Pairwise (Function.onFun IsCoprime fun M : MaximalSpectrum A => M.asIdeal) := by
    intro M N hMN
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (M.isMaximal.coprime_of_ne N.isMaximal fun h => hMN (MaximalSpectrum.ext h))
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcop fun M => Ideal.Quotient.mk M.asIdeal (y M)
  exact ⟨a, fun M => Ideal.Quotient.eq.mp (ha M)⟩

theorem exists_isUnit_add (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ)
    (x : Fin (m + 1) → A) (hx : ∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) :
    ∃ a : Fin m → A, IsUnit (x 0 + ∑ k, a k * x k.succ) := by
  classical
  have hnot : ∀ M : MaximalSpectrum A, x 0 ∈ M.asIdeal → ∃ k : Fin m, x k.succ ∉ M.asIdeal := by
    intro M h0
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i, x i ∈ M.asIdeal := fun i => Fin.cases h0 hall i
    apply M.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)
  choose kM hkM using hnot
  let y : Fin m → MaximalSpectrum A → A := fun k M =>
    if h : x 0 ∈ M.asIdeal then (if kM M h = k then 1 else 0) else 0
  choose a ha using fun k => exists_sub_iota_mem_of_sub_involution_mem A (y k)
  refine ⟨a, ?_⟩
  by_contra hu
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
  let M : MaximalSpectrum A := ⟨N, hN⟩
  have huM : x 0 + ∑ k, a k * x k.succ ∈ M.asIdeal := hle (Ideal.mem_span_singleton_self _)
  by_cases h0 : x 0 ∈ M.asIdeal
  · have hy : ∑ k, y k M * x k.succ = x (kM M h0).succ := by
      simp only [y, dif_pos h0, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq]
    have hin : x 0 + ∑ k, (a k - y k M) * x k.succ ∈ M.asIdeal :=
      M.asIdeal.add_mem h0 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha k M))
    have e : x (kM M h0).succ =
        (x 0 + ∑ k, a k * x k.succ) - (x 0 + ∑ k, (a k - y k M) * x k.succ) := by
      rw [← hy]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    exact hkM M h0 (e ▸ M.asIdeal.sub_mem huM hin)
  · apply h0
    have hs : ∑ k, a k * x k.succ ∈ M.asIdeal := by
      refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
      simpa [y, h0] using ha k M
    simpa using M.asIdeal.sub_mem huM hs

theorem exists_invertible_first_column :
    ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ) (x : Fin (m + 1) → A),
      (∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) A, IsUnit g.det ∧ ∀ i, g i 0 = x i := by
  intro A _ _ m x hx
  classical
  obtain ⟨a, ha⟩ := exists_isUnit_add A m x hx
  set u := x 0 + ∑ k, a k * x k.succ with hu
  let b : Fin (m + 1) → A := Fin.cons 0 a
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if i = j then 1 else if i = 0 then -b j else 0
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if j = 0 then (if i = 0 then u else x i) else if i = j then 1 else 0
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun i _ => by simp [E]
    · intro i j hij
      have hji : j < i := hij
      have hi : i ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hji
      simp [E, hji.ne', hi]
  have hD : D.det = u := by
    rw [Matrix.det_of_isLowerTriangular]
    · rw [Fin.prod_univ_succ]
      simp [D, Fin.succ_ne_zero]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [D, hj, hij'.ne]
  refine ⟨E * D, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul, hE, hD, one_mul]
    exact ha
  · rw [Matrix.mul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Fin.sum_univ_succ]
      simp [E, D, b, (Fin.succ_ne_zero _).symm, hu, Finset.sum_neg_distrib]
    · rw [Finset.sum_eq_single i]
      · simp [E, D, hi]
      · intro j _ hji
        simp [E, D, Ne.symm hji, hi]
      · simp

end GlobalTheory.CompanionTheory.SW.SemilocalColumn
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem exists_posDef_majorant_of_isSymm :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 →
      ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  intro ι _ _ B hsym hdet
  have hH : B.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℝ, U = (hH.eigenvectorUnitary : Matrix ι ι ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ι → ℝ, d = hH.eigenvalues := ⟨_, rfl⟩
  have hUs : star U * U = 1 := by subst hU; simp
  have hsU : U * star U = 1 := by subst hU; simp
  have hspec : B = U * Matrix.diagonal d * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    subst hU hdd
    simp [Unitary.conjStarAlgAut_apply]
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    rw [hdd] at hi
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have conj : ∀ a b : ι → ℝ, (U * Matrix.diagonal a * star U) * (U * Matrix.diagonal b * star U) =
      U * Matrix.diagonal (fun i => a i * b i) * star U := by
    intro a b
    calc U * Matrix.diagonal a * star U * (U * Matrix.diagonal b * star U)
        = U * Matrix.diagonal a * (star U * U) * Matrix.diagonal b * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal a * Matrix.diagonal b) * star U := by
          rw [hUs, Matrix.mul_one, Matrix.mul_assoc U]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]
  have hinv : B⁻¹ = U * Matrix.diagonal (fun i => (d i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hspec, conj]
    rw [show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) from funext fun i => mul_inv_cancel₀ (hd i),
      Matrix.diagonal_one, Matrix.mul_one, hsU]
  refine ⟨U * Matrix.diagonal (fun i => |d i|) * star U, ?_, ?_⟩
  · rw [Matrix.IsUnit.posDef_star_right_conjugate_iff ⟨⟨U, star U, hsU, hUs⟩, rfl⟩,
      Matrix.posDef_diagonal_iff]
    exact fun i => abs_pos.mpr (hd i)
  · rw [hinv, conj, conj]
    conv_rhs => rw [hspec]
    congr 3
    funext i
    show |d i| * (d i)⁻¹ * |d i| = d i
    rw [mul_right_comm, abs_mul_abs_self, mul_inv_cancel_right₀ (hd i)]

end GlobalTheory.CompanionTheory.SW
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Transv

theorem toMatrix_mulVec_apply {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι]
    (t : Matrix.TransvectionStruct ι K) (x : ι → K) (k : ι) :
    (t.toMatrix *ᵥ x) k = if k = t.i then x k + t.c * x t.j else x k := by
  have h : t.toMatrix = 1 + Matrix.single t.i t.j t.c := rfl
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  by_cases hk : k = t.i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have : ∀ l, (Matrix.single t.i t.j t.c) k l = 0 := by
      intro l
      simp [Matrix.single_apply, Ne.symm hk]
    simp [Matrix.mulVec, dotProduct, this, hk]

theorem measurePreserving_pi {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure K) [SigmaFinite ν]
    [ν.IsAddLeftInvariant] (t : Matrix.TransvectionStruct ι K) :
    MeasurePreserving (fun x : ι → K => t.toMatrix *ᵥ x)
      (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  have hj : t.j ≠ t.i := t.hij.symm
  let p : ι → Prop := fun k => k ≠ t.i
  let B : Measure ({k // p k} → K) := Measure.pi fun _ => ν
  let A : Measure ({k // ¬ p k} → K) := Measure.pi fun _ => ν
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let g : ({k // p k} → K) → ({k // ¬ p k} → K) → ({k // ¬ p k} → K) :=
    fun b a => (fun _ => t.c * b ⟨t.j, hj⟩) + a
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_pi_iff.2 fun k => ?_
    have h1 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.1 ⟨t.j, hj⟩ := (measurable_pi_apply _).comp measurable_fst
    have h2 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.2 k := (measurable_pi_apply _).comp measurable_snd
    exact (h1.const_mul t.c).add h2
  have hsk : MeasurePreserving (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2))
      (B.prod A) (B.prod A) := by
    refine (MeasurePreserving.id B).skew_product hgm (Filter.Eventually.of_forall fun b => ?_)
    exact map_add_left_eq_self A _
  have hall := hmp.symm.comp (hsk.comp hmp)
  have hfun : (fun x : ι → K => t.toMatrix *ᵥ x) =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p).symm ∘
        (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2)) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p) := by
    funext x k
    rw [toMatrix_mulVec_apply]
    by_cases hk : k = t.i
    · subst hk
      have hnp : ¬ p t.i := fun h => h rfl
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, g, hnp, add_comm]
    · have hp : p k := hk
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp, hk]
  rw [hfun]
  exact hall

theorem map_toMatrix_mulVec (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K) :
    μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  let ν : Measure K := Measure.addHaar
  let P : Measure (ι → K) := Measure.pi fun _ : ι => ν
  haveI : P.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hμ : μ = Measure.addHaarScalarFactor μ P • P := Measure.isAddLeftInvariant_eq_smul μ P
  have hP : MeasurePreserving (fun x => t.toMatrix *ᵥ x) P P := measurePreserving_pi ν t
  generalize Measure.addHaarScalarFactor μ P = c at hμ
  rw [hμ, Measure.map_smul c hP.measurable.aemeasurable, hP.map_eq]

end GlobalTheory.CompanionTheory.SW.Transv

theorem GlobalTheory.CompanionTheory.SW.transvection_map_addHaar : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  intro K _ _ _ _ _ _ _ _ ι _ _ μ _ t
  exact GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec K ι μ t
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatticeUnimod

theorem unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : ∀ g : G, μ.map (· * g) = μ := by
    intro g
    have hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ :=
      Measure.isMulLeftInvariant_eq_smul _ _
    have hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := hF.measure_eq h𝓕
    have e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) :=
      (MeasurableEquiv.mulRight g).map_apply 𝓕
    have e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
      have e3 := congrArg (fun m : Measure G => m 𝓕) hc
      simp only [Measure.smul_apply] at e3
      rw [e1, hm] at e3
      rw [one_mul]
      exact e3.symm
    have e4 := (ENNReal.mul_left_inj h0 hfin.ne).1 e2
    have e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := ENNReal.coe_eq_one.1 e4
    rw [e5, one_smul] at hc
    exact hc
  haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩
  refine ⟨h0, hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hVpos : 0 < μ V := Measure.measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  rw [hc, e3, one_smul]

end GlobalTheory.CompanionTheory.SW.LatticeUnimod
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.InvariantProduct

theorem exists_const_rect {Q Z : Type} [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] (η : Measure Q) [η.IsHaarMeasure]
    (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ]
    (hinv : ∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ)
    {A C : Set Z} (hA : MeasurableSet A) (hC : IsCompact C) (hAC : A ⊆ C) :
    ∃ c : ℝ≥0, ∀ U : Set Q, MeasurableSet U → ρ (U ×ˢ A) = c * η U := by
  let μ : Measure Q := (ρ.restrict (Set.univ ×ˢ A)).map Prod.fst
  have hμ : ∀ U : Set Q, MeasurableSet U → μ U = ρ (U ×ˢ A) := by
    intro U hU
    rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
    congr 1
    ext ⟨x, z⟩
    simp
  haveI : μ.IsMulLeftInvariant := ⟨fun q => by
    ext U hU
    have hT : Measurable (fun p : Q × Z => (q * p.1, p.2)) :=
      (measurable_fst.const_mul q).prodMk measurable_snd
    rw [Measure.map_apply (measurable_const_mul q) hU, hμ _ (measurable_const_mul q hU), hμ U hU]
    conv_rhs => rw [← hinv q]
    rw [Measure.map_apply hT (hU.prod hA)]
    rfl⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun L hL => by
    rw [hμ L hL.isClosed.measurableSet]
    exact (measure_mono (Set.prod_mono subset_rfl hAC)).trans_lt (hL.prod hC).measure_lt_top⟩
  refine ⟨Measure.haarScalarFactor μ η, fun U hU => ?_⟩
  have h := congrArg (fun ν : Measure Q => ν U) (Measure.isMulLeftInvariant_eq_smul μ η)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  rw [← hμ U hU]
  exact h

end GlobalTheory.CompanionTheory.SW.InvariantProduct

namespace GlobalTheory.CompanionTheory.SW

theorem measure_eq_haar_prod_of_left_invariant :
    ∀ (Q Z : Type) [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
      [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
      [IsTopologicalGroup Q] [TopologicalSpace Z] [LocallyCompactSpace Z]
      [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
      (η : Measure Q) [η.IsHaarMeasure] (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ],
      (∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ) →
        ∃ m : Measure Z, IsLocallyFiniteMeasure m ∧ ρ = η.prod m := by
  intro Q Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ η _ ρ _ hinv
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : Q)
  have hKpos : η K ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos η ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩)
    (measure_mono interior_subset)).ne'
  have hKfin : η K ≠ ∞ := hKc.measure_lt_top.ne
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  let m : Measure Z := (η K)⁻¹ • (ρ.restrict (K ×ˢ Set.univ)).map Prod.snd
  have hm : ∀ A : Set Z, MeasurableSet A → m A = (η K)⁻¹ * ρ (K ×ˢ A) := by
    intro A hA
    have hset : Prod.snd ⁻¹' A ∩ (K ×ˢ (Set.univ : Set Z)) = K ×ˢ A := by
      ext ⟨x, z⟩
      simp [and_comm]
    simp only [m, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA), hset]
  have hrect : ∀ (U : Set Q) (A C : Set Z), MeasurableSet U → MeasurableSet A → IsCompact C →
      A ⊆ C → ρ (U ×ˢ A) = η U * m A := by
    intro U A C hU hA hC hAC
    obtain ⟨c, hc⟩ := InvariantProduct.exists_const_rect η ρ hinv hA hC hAC
    rw [hc U hU, hm A hA, hc K hKm, ← mul_assoc (η K)⁻¹, mul_comm (η K)⁻¹,
      mul_assoc (c : ℝ≥0∞), ENNReal.inv_mul_cancel hKpos hKfin, mul_one, mul_comm]
  have hmC : ∀ C : Set Z, IsCompact C → m C < ∞ := by
    intro C hC
    rw [hm C hC.isClosed.measurableSet]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hKpos))
      (hKc.prod hC).measure_lt_top
  haveI hmfc : IsFiniteMeasureOnCompacts m := ⟨fun C hC => hmC C hC⟩
  refine ⟨m, inferInstance, ?_⟩
  symm
  have genAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X],
      MeasurableSpace.generateFrom {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} =
        ‹MeasurableSpace X› := by
    intro X _ _ _ M _
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1
    · intro B hB
      have : B = ⋃ n, B ∩ compactCovering X n := by
        rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
      rw [this]
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨hB.inter (isCompact_compactCovering X n).isClosed.measurableSet,
          _, isCompact_compactCovering X n, Set.inter_subset_right⟩
  have piAux : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X],
      IsPiSystem {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ U hU V hV _
    obtain ⟨hUm, L, hL, hUL⟩ := hU
    exact ⟨hUm.inter hV.1, L, hL, Set.inter_subset_left.trans hUL⟩
  have spanAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ],
      μ.FiniteSpanningSetsIn {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ _ _ _ μ _
    exact ⟨compactCovering X,
      fun n => ⟨(isCompact_compactCovering X n).isClosed.measurableSet, _,
        isCompact_compactCovering X n, subset_rfl⟩,
      fun n => (isCompact_compactCovering X n).measure_lt_top,
      iUnion_compactCovering X⟩
  refine Measure.prod_eq_generateFrom (genAux Q) (genAux Z) (piAux Q) (piAux Z)
    (spanAux Q η) (spanAux Z m) ?_
  rintro U ⟨hU, -⟩ A ⟨hA, L, hL, hAL⟩
  exact (hrect U A L hU hA hL hAL)

end GlobalTheory.CompanionTheory.SW
end
