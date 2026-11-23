module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle001
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle048
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle062
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FinQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨-, htc, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  have hcx : w.IsComplex := htc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.mpr hcx
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  have := hτ w.embedding x
  rw [hc x] at this
  simpa using this.symm

theorem fixed_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ t : F, e = algebraMap F E t := by
  apply GlobalTheory.CompanionTheory.SW.HermOne.exists_eq_algebraMap <;> assumption

theorem hE_self_fixed (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by

  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma σ h (x j)
  have h2 : σ (J j i) = J i j := hJ.1 i j
  have h3 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, h2, h3]
  ring

end Field

theorem gram_rational_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X : Fin 1 → Fin M → E, ∃ t : F, gramE σ J X = fun _ _ => algebraMap F E t) ∧
    (∀ (n : ℕ) (X : Fin n → Fin M → E),
      gramR (AF F) σ J (ratTup (AF F) X) = (gramE σ J X).map (inclR (AF F))) ∧
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      {t : F | ∃ Y ∈ Ω, gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)}.Finite := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  refine ⟨?_, ?_, ?_⟩
  · intro X
    obtain ⟨t, ht⟩ := fixed_mem σ hcm _ (hE_self_fixed σ hcm J hJ (X 0))
    refine ⟨t, ?_⟩
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact ht
  · intro n X
    ext a b
    have hs : ∀ e : E, sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := fun e => by
      simp [sigR, inclR]

    simp only [gramR, hR, hform, ratTup, JR, Matrix.map_apply, gramE, hE, map_sum, map_mul, hs]
    rfl
  · intro Ω hΩ
    obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
    let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
      fun Y _ _ => gramR (AF F) σ J Y 0 0
    have hφ : Continuous φ :=
      continuous_pi fun _ => continuous_pi fun _ => hcont.matrix_elem 0 0
    have hfin := (GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 1).2.1 _ (hΩ.image hφ)
    let ι : F → Fin 1 → Fin 1 → E := fun t _ _ => algebraMap F E t
    refine Set.Finite.of_injOn (f := ι) ?_ ?_ hfin
    · rintro t ⟨Y, hY, hYt⟩
      refine ⟨Y, hY, ?_⟩
      funext a b
      exact congrFun (congrFun hYt 0) 0
    · intro s _ t _ hst
      exact (algebraMap F E).injective (congrFun (congrFun hst 0) 0)

end GlobalTheory.CompanionTheory.SW.FinQ
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatCount

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def ratHom (M : ℕ) : (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun := ratTup (AF F)
  map_zero' := by
    funext a i
    simp [ratTup]
  map_add' X Y := by
    funext a i
    simp [ratTup]

lemma box_mono {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

lemma sizeInf_nonneg {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma repr_projInf_ratTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf (ratTup (AF F) X) a i) k =
      algebraMap F (Ainf F) (b.repr (X a i) k) := by
  have : projInf (ratTup (AF F) X) a i = (1 : Ainf F) ⊗ₜ[F] X a i := by
    simp [projInf, ratTup, inclR]
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma sizeTup_ratTup_pos {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (hX : X ≠ 0) : 0 < sizeTup b (projInf (ratTup (AF F) X)) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨k, hk⟩ : ∃ k, b.repr (X a i) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  set Y := projInf (ratTup (AF F) X : Fin n → Fin M → AF F ⊗[F] E) with hY
  have h1 : 0 < ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ := by
    rw [hY, repr_projInf_ratTup, norm_pos_iff]
    change algebraMap F v.Completion (b.repr (X a i) k) ≠ 0
    exact (map_ne_zero _).mpr hk
  have h2 : ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ ≤ sizeInf b (Y a i) :=
    (Finset.single_le_sum
      (f := fun v => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum
      (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have h3 : sizeInf b (Y a i) ≤ sizeTup b Y :=
    (Finset.single_le_sum (f := fun i => sizeInf b (Y a i))
      (fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (Y a i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ a))
  linarith

end SlopeTestRemainingChoices

lemma exists_pos_lt {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ S, r < f x :=
  _root_.Bl.FirstLemmaK.goal1 hS f hf

theorem count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M Ω hΩ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨hcpt, hexh, hflow⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ b 1 M
  obtain ⟨-, hfin, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hCM 1 M
  obtain ⟨N, r, hN, hr, hsub⟩ := hexh Ω hΩ

  obtain ⟨r₀, h0, h1, hsmall⟩ := exists_pos_lt
    (((hfin _ (hcpt N 1 hN)).subset (Set.inter_subset_left
      (t := {X : Fin 1 → Fin M → E | X ≠ 0}))))
    (fun X => sizeTup b (projInf (ratTup (AF F) X)))
    (fun X hX => sizeTup_ratTup_pos b X hX.2)
  have hnone : ∀ X : Fin 1 → Fin M → E, X ≠ 0 → ratTup (AF F) X ∉ box b N r₀ := by
    intro X hX hmem
    have := hsmall X ⟨box_mono b N h1 hmem, hX⟩
    exact absurd hmem.2 (not_le.mpr this)
  have hscale : ∀ (x : ℝ) (Y : Fin 1 → Fin M → AF F ⊗[F] E),
      ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ Ω →
        Y ∈ box b N (Real.exp x * r) := by
    intro x Y hY
    refine (hflow τ hτ N (Real.exp x * r) (-x) Y).mp ?_
    have : Real.exp (-x) * (Real.exp x * r) = r := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact hsub hY
  refine ⟨Real.log (r₀ / r), (5 * r / r₀) ^ (2 * Module.finrank ℚ F * M), fun x => ?_⟩
  split_ifs with hx
  ·
    have hlt : Real.exp x * r < r₀ := by
      have := (Real.lt_log_iff_exp_lt (div_pos h0 hr)).mp hx
      exact (lt_div_iff₀ hr).mp this
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun X => Set.indicator_of_notMem ?_ _)
    intro hmem
    exact hnone X.1 X.2 (box_mono b N hlt.le (hscale x _ hmem))
  · have hge : r₀ ≤ Real.exp x * r := by
      have := (Real.log_le_iff_le_exp (div_pos h0 hr)).mp (not_lt.mp hx)
      exact (div_le_iff₀ hr).mp this
    set e := ratHom (F := F) (E := E) M with he
    have hone : ∑' l : Fin 1 → Fin M → E,
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ 1 := by
      rw [tsum_eq_single 0]
      · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by simp)
      · intro X hX
        exact Set.indicator_of_notMem (hnone X hX) _
    have hpack := GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hCM _ b M (Fin 1 → Fin M → E) e N r₀ (Real.exp x * r) h0 hge
    calc ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞)))
            (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1)
        ≤ ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0},
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e X.1) := by
          refine ENNReal.tsum_le_tsum fun X => ?_
          by_cases hm : ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
              ratTup (AF F) X.1 ∈ Ω
          · have hm' : e X.1 ∈ box b N (Real.exp x * r) := hscale x _ hm
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
          · rw [Set.indicator_of_notMem hm]
            exact bot_le
      _ ≤ ∑' l : Fin 1 → Fin M → E,
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun l => (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l))
      _ ≤ ENNReal.ofReal ((5 * (Real.exp x * r) / r₀) ^ (2 * Module.finrank ℚ F * M)) * 1 :=
          hpack.trans (mul_le_mul_right hone _)
      _ = ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M) *
            Real.exp (2 * Module.finrank ℚ F * M * x)) := by
          rw [mul_one]
          congr 1
          have : (2 * (Module.finrank ℚ F : ℝ) * M * x) =
              ((2 * Module.finrank ℚ F * M : ℕ) : ℝ) * x := by push_cast; ring
          rw [this, Real.exp_nat_mul, ← mul_pow]
          congr 1
          ring

end GlobalTheory.CompanionTheory.SW.LatCount
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodMass

theorem continuous_act_consTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (hring : IsTopologicalRing (R ⊗[F] E)) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA R σ J) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J h (consTup X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actW, actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · refine Fin.cases ?_ (fun j' => ?_) j <;> simpa [consTup] using continuous_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [consTup] using continuous_const
    · have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E => X a' j' :=
        (continuous_apply j').comp (continuous_apply a')
      simpa [consTup] using hc

theorem good_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdetT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [StageGood.stage_good F E σ hCM M J hJ t ht n T hT hdetT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdetT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

end GlobalTheory.CompanionTheory.SW.GoodMass
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_quadratic_density_near_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 1 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  first | exact @GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | exact GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | (intros; apply GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive <;> assumption)
end
