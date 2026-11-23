module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
open Topology Filter

namespace GlobalTheory.FundExists

theorem exists_strict_domain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ C : Set G, IsCompact C → (C ∩ Γ).Finite) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = 1 := by
  first
  | exact @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | (apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain ..)

theorem exists_isFundDom : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    ∃ fund, I.IsFundDom (I.muA μf) fund := by
  intro I μf _ _
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, hfin, -⟩ := GlobalTheory.RatDiscrete.rational_points I
  rw [← hΓ] at hfin
  obtain ⟨D, hD, hcov, hinj⟩ := exists_strict_domain Γ hfin
  refine ⟨D, hD, ?_, ?_⟩
  · rw [← hΓ]
    exact hcov
  · rw [← hΓ]
    intro γ hγ hne
    have : (fun y => γ * y) '' D ∩ D = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hγy⟩
      exact hne (hinj γ hγ y hy hγy)
    rw [this, measure_empty]

end GlobalTheory.FundExists
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CompactDense

theorem dense_of_sigmaCompact {X : Type} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) :
    Dense {y : Lp ℂ 2 μ | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0} := by
  intro y
  have hm : ∀ n, MeasurableSet (compactCovering X n) := fun n => (isCompact_compactCovering X n).isClosed.measurableSet
  have hy : MemLp (y : X → ℂ) 2 μ := Lp.memLp y
  let u : ℕ → Lp ℂ 2 μ := fun n => (hy.indicator (hm n).nullMeasurableSet).toLp _
  have hu : ∀ n, (u n : X → ℂ) =ᵐ[μ] (compactCovering X n).indicator y := fun n => MemLp.coeFn_toLp _
  refine mem_closure_of_tendsto (f := u) (b := Filter.atTop) ?_ (Filter.Eventually.of_forall fun n => ?_)
  · have hi : Integrable (fun z => ‖(y : X → ℂ) z‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).1 hy
    have e : ∀ n, ‖u n - y‖ ^ 2 = ∫ z, (compactCovering X n)ᶜ.indicator (fun z => ‖(y : X → ℂ) z‖ ^ 2) z ∂μ := by
      intro n
      rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
      refine integral_congr_ae ?_
      filter_upwards [hu n, Lp.coeFn_sub (u n) y] with z h1 h2
      rw [inner_self_eq_norm_sq, h2, Pi.sub_apply, h1]
      by_cases hz : z ∈ compactCovering X n <;> simp [hz]
    have h0 : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2) Filter.atTop (nhds (∫ _z, (0 : ℝ) ∂μ)) := by
      simp only [e]
      refine tendsto_integral_of_dominated_convergence _ (fun n => hi.1.indicator (hm n).compl) hi
        (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
      · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
        simp
      · obtain ⟨N, hN⟩ := exists_mem_compactCovering z
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have : z ∈ compactCovering X n := compactCovering_subset X hn hN
        simp [this]
    rw [integral_zero] at h0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 := h0.sqrt
    simpa using h1
  · refine ⟨_, isCompact_compactCovering X n, ?_⟩
    filter_upwards [hu n] with z h hz
    simp [h, hz]

theorem dense_compact_support : ∀ B : RowsAut, Dense {y : B.I.L2 B.μf B.fund | ∃ C : Set B.I.GA, IsCompact C ∧ ∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0} := by
  intro B
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  exact dense_of_sigmaCompact _

end GlobalTheory.CompactDense
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_integral_over {E : Type} [Field E] [NumberField E]
    (g : ℕ) (hg : g ≠ 0) (m : E)
    (hm : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * m = o) :
    ∃ ξ c : 𝓞 E, m - (ξ : E) = (g : E) * (c : E) * m := by
  let D : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E m) 1
  have hD : ∀ s : 𝓞 E, s ∈ D ↔ ∃ o : 𝓞 E, (s : E) * m = o := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [Algebra.smul_def] at hy; exact hy.symm⟩
    · rintro ⟨o, ho⟩; exact ⟨o, by rw [Algebra.smul_def]; exact ho.symm⟩
  have htop : D ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hgQ : (g : 𝓞 E) ∈ Q := hQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast hg
    have hQbot : Q ≠ ⊥ := fun h => hg0 (by rw [h] at hgQ; simpa using hgQ)
    obtain ⟨s, hs, o, ho⟩ := hm ⟨Q, hQmax.isPrime, hQbot⟩ hgQ
    exact hs (hQ (Ideal.mem_sup_left ((hD s).2 ⟨o, ho⟩)))
  have h1 : (1 : 𝓞 E) ∈ D ⊔ Ideal.span {(g : 𝓞 E)} := by rw [htop]; trivial
  obtain ⟨d, hd, y, hy, hdy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨o, ho⟩ := (hD d).1 hd
  refine ⟨o, c, ?_⟩
  have e := congrArg (fun x : 𝓞 E => (x : E)) hdy
  push_cast at e
  rw [← ho]
  linear_combination (-m) * e

theorem admissible_of_congr_unitriangular {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hlow : ∀ a b, b < a → M a b = 0) (hdiag : ∀ a, M a a = 1)
    (hint : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b,
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o)
    (hloc : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hmod : ∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) :
    IsAdmissible Λ g F F' := by
  classical
  have key : ∀ a b, ∃ ξ c : 𝓞 E, M a b - (ξ : E) = (g : E) * (c : E) * M a b :=
    fun a b => exists_int_sub_eq_mul_of_integral_over g hg (M a b) (fun P hP => hint P hP a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else (key a b).choose
  have hξ : ∀ a b, ∃ c : 𝓞 E, M a b - ((ξ a b : 𝓞 E) : E) = (g : E) * (c : E) * M a b := by
    intro a b
    by_cases h1 : b < a
    · exact ⟨0, by simp [ξ, h1, hlow a b h1]⟩
    · by_cases h2 : a = b
      · subst h2; exact ⟨0, by simp [ξ, hdiag]⟩
      · obtain ⟨c, hc⟩ := (key a b).choose_spec
        exact ⟨c, by simpa [ξ, h1, h2] using hc⟩
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], ?_⟩
  intro b P hP
  haveI := P.isPrime
  have hsplit : frame F' b - frameAct (frame F) ξ b =
      (frame F' b - ∑ a, M a b • frame F a) + ∑ a, (M a b - (ξ a b : E)) • frame F a := by
    simp only [frameAct, sub_smul, Finset.sum_sub_distrib]; abel
  rw [hsplit]
  refine Submodule.add_mem _ (hmod b P hP) (Submodule.sum_mem _ fun a _ => ?_)
  obtain ⟨c, hc⟩ := hξ a b
  obtain ⟨t, ht, htf⟩ := hloc P hP a
  obtain ⟨s, hs, o, ho⟩ := hint P hP a b
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  rw [hc]
  have e : (s * t) • (((g : E) * (c : E) * M a b) • frame F a) =
      ((g : 𝓞 E) * (c * o)) • (t • frame F a) := by
    rw [← algebraMap_smul E (s * t), ← algebraMap_smul E ((g : 𝓞 E) * (c * o)),
      ← algebraMap_smul E t, smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_natCast]
    change (s : E) * (t : E) * ((g : E) * (c : E) * M a b) = (g : E) * ((c : E) * (o : E)) * (t : E)
    rw [← ho]; ring
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) htf

end GlobalTheory
end

section

noncomputable section

open NumberField

namespace GlobalTheory.RowLatAssembly

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

lemma Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

lemma X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

lemma e_mem (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

private lemma coefX_linearCombination_eq (F : FlagG S r T) (l : Fin r →₀ E) (a : Fin r) :
    F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
  have hmem : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ l
  unfold FlagG.coefX
  rw [dite_eq_left hmem, F.e_indep.repr_eq (l := l) rfl]

private lemma exists_linearCombination_eq_of_mem_flagX (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) :
    ∃ l : Fin r →₀ E, Finsupp.linearCombination E F.e l = y := by
  unfold FlagG.X at hy
  rw [← Finsupp.range_linearCombination] at hy
  exact LinearMap.mem_range.mp hy

lemma coefX_add (F : FlagG S r T) (a : Fin r) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  obtain ⟨m, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hy
  rw [← map_add (f := _), coefX_linearCombination_eq, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.add_apply]

lemma coefX_smul (F : FlagG S r T) (a : Fin r) (c : E) {x : S.V} (hx : x ∈ F.X) :
    F.coefX (c • x) a = c * F.coefX x a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  rw [← map_smul, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.smul_apply, smul_eq_mul]

lemma coefX_e (F : FlagG S r T) (i a : Fin r) :
    F.coefX (F.e i) a = if i = a then 1 else 0 := by
  have h : F.e i = Finsupp.linearCombination E F.e (Finsupp.single i 1) := by simp
  rw [h, coefX_linearCombination_eq, Finsupp.single_apply]

lemma mem_Xa_of_coefX_eq_zero (F : FlagG S r T) (a : Fin r) {y : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (h0 : F.coefX y a = 0) : y ∈ F.Xa a.val := by
  unfold FlagG.Xa at hy ⊢
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).mp hy
  rw [coefX_linearCombination_eq] at h0
  refine (Finsupp.mem_span_image_iff_linearCombination (R := E)).mpr ⟨l, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hl ⊢
  intro i hi
  simp only [Set.mem_ofPred_eq, not_lt] at hi
  rcases lt_or_eq_of_le hi with h | h
  · exact hl i (by simp only [Set.mem_ofPred_eq]; omega)
  · have hia : i = a := Fin.ext h.symm
    rw [hia]
    exact h0

lemma sub_smul_mem (F : FlagG S r T) (a : Fin r) {y w : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (hw : w ∈ F.Xa (a.val + 1)) (hw1 : F.coefX w a = 1) :
    y - F.coefX y a • w ∈ F.Xa a.val := by
  have hyX := Xa_le_X F _ hy
  have hwX := Xa_le_X F _ hw
  apply mem_Xa_of_coefX_eq_zero F a (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hw))
  rw [sub_eq_add_neg, ← neg_smul, coefX_add F a hyX (Submodule.smul_mem _ _ hwX),
    coefX_smul F a _ hwX, hw1]
  ring

lemma exists_section (F : FlagG S r T) (Λ : Submodule (𝓞 E) S.V)
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (a : Fin r)
    (h3 : ∀ t : E, t ∈ J → ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t) :
    ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = 1 ∧ ∀ t ∈ J, t • w ∈ Λ := by

  have key : ∀ s ∈ J * J⁻¹, ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = s ∧ ∀ t ∈ J, t • w ∈ Λ := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro i hi j hj
      obtain ⟨x, hxΛ, hxX, hxc⟩ := h3 i hi
      refine ⟨j • x, Submodule.smul_mem _ j hxX, ?_, ?_⟩
      · rw [coefX_smul F a j (Xa_le_X F _ hxX), hxc, mul_comm]
      · intro t ht
        have htj : t * j ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul ht hj
        rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff] at htj
        obtain ⟨o, ho⟩ := htj
        rw [smul_smul, ← ho, algebraMap_smul]
        exact Λ.smul_mem o hxΛ
    · rintro s₁ s₂ ⟨w₁, hw₁, hc₁, hΛ₁⟩ ⟨w₂, hw₂, hc₂, hΛ₂⟩
      refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_, ?_⟩
      · rw [coefX_add F a (Xa_le_X F _ hw₁) (Xa_le_X F _ hw₂), hc₁, hc₂]
      · intro t ht
        rw [smul_add]
        exact Λ.add_mem (hΛ₁ t ht) (hΛ₂ t ht)
  have h1 : (1 : E) ∈ J * J⁻¹ := by
    rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff]
    exact ⟨1, map_one _⟩
  exact key 1 h1

theorem xLam_eq_span : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  intro E _ _ _ S r T G Λ J hJ h2 h3
  have hsec : ∀ a : Fin r, ∃ w ∈ G.fl.Xa (a.val + 1), G.fl.coefX w a = 1 ∧ ∀ t ∈ J a, t • w ∈ Λ :=
    fun a => exists_section G.fl Λ (J a) (hJ a) a (h3 a)
  choose e' he'X he'c he'Λ using hsec
  refine ⟨e', fun a => ?_, ?_⟩
  · have hea : G.fl.coefX (G.fl.e a) a = 1 := by rw [coefX_e, if_pos rfl]
    have h := sub_smul_mem G.fl a (he'X a) (e_mem G.fl a) hea
    rwa [he'c a, one_smul] at h
  · apply le_antisymm
    ·
      have step : ∀ j : ℕ, j ≤ r → ∀ v ∈ Λ, v ∈ G.fl.Xa j →
          v ∈ Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
        intro j
        induction j with
        | zero =>
          intro _ v _ hv
          have hv0 : v = 0 := by
            unfold Formalism.MainNotions.S.FlagG.Xa at hv
            simpa using hv
          rw [hv0]
          exact Submodule.zero_mem _
        | succ j ih =>
          intro hj v hvΛ hv
          obtain ⟨a, rfl⟩ : ∃ a : Fin r, a.val = j := ⟨⟨j, hj⟩, rfl⟩
          have hc : G.fl.coefX v a ∈ J a := h2 a v hvΛ hv
          have hrest : v - G.fl.coefX v a • e' a ∈ G.fl.Xa a.val :=
            sub_smul_mem G.fl a hv (he'X a) (he'c a)
          have hrestΛ : v - G.fl.coefX v a • e' a ∈ Λ := Λ.sub_mem hvΛ (he'Λ a _ hc)
          have hlow := ih (Nat.le_of_succ_le hj) _ hrestΛ hrest
          have htop : G.fl.coefX v a • e' a ∈
              Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} :=
            Submodule.subset_span ⟨a, _, hc, rfl⟩
          have hsum := Submodule.add_mem _ hlow htop
          rwa [sub_add_cancel] at hsum
      intro v hv
      obtain ⟨hvΛ, hvX⟩ : v ∈ Λ ∧ v ∈ G.fl.X := hv
      rw [X_eq_Xa] at hvX
      exact step r le_rfl v hvΛ hvX
    · rw [Submodule.span_le]
      rintro y ⟨a, x, hx, rfl⟩
      show x • e' a ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S (Formalism.MainNotions.S.Lat.Xsp G)
      exact Submodule.mem_inf.mpr ⟨he'Λ a x hx, (G.fl.X).smul_mem x (Xa_le_X G.fl _ (he'X a))⟩

end GlobalTheory.RowLatAssembly
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagInv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem map_Xflag_le (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) ≤ Xflag F j := by
  show (F.fl.Xa j).map (a : S.V →ₗ[E] S.V) ≤ F.fl.Xa j
  rw [Submodule.map_le_iff_le_comap]
  unfold Formalism.MainNotions.S.FlagG.Xa
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq] at hi
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
  have hb := h (Fin.castSucc i)
  have hf : frame F (Fin.castSucc i) = F.fl.e i := by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  rw [hf] at hb
  have hmono : Xflag F (Fin.castSucc i).val ≤ F.fl.Xa j := by
    show F.fl.Xa i.val ≤ F.fl.Xa j
    unfold Formalism.MainNotions.S.FlagG.Xa
    apply Submodule.span_mono
    apply Set.image_mono
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    omega
  have he : F.fl.e i ∈ F.fl.Xa j := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have := Submodule.add_mem _ (hmono hb) he
  unfold Formalism.MainNotions.S.FlagG.Xa at this
  simpa using this

theorem map_Xflag_eq (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) = Xflag F j := by
  haveI : FiniteDimensional E (Xflag F j) := by
    show FiniteDimensional E (Submodule.span E (F.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite E (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq (map_Xflag_le F a h j) (LinearEquiv.finrank_map_eq a _)

theorem symm_mem_Xflag (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) {x : S.V}
    (hx : x ∈ Xflag F j) : a.symm x ∈ Xflag F j := by
  rw [← map_Xflag_eq F a h j] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem inv_moves : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  intro E _ _ _ S r T F a h b
  have hm := symm_mem_Xflag F a h b.val (h b)
  have key : a⁻¹ (frame F b) - frame F b = -(a.symm (a (frame F b) - frame F b)) := by
    show a.symm (frame F b) - frame F b = _
    simp [map_sub]
  rw [key]
  exact Submodule.neg_mem _ hm

end GlobalTheory.FlagInv
end

section

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.GenericOrder

theorem mem_locP' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem frame_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hL : IsLift Λ F) (hF : ∀ b, frame F b ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} := by
  have hb := hF b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]
  | cast i =>
    refine Submodule.mem_sup_left ⟨hb, ?_⟩
    have : frame F i.castSucc = F.fl.e i := by simp [frame, Formalism.MainNotions.S.FlagG.fvec]
    rw [this]
    exact Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩

end GlobalTheory.GenericOrder
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.MinorJet.deriv_leadMinor_exp | exact GlobalTheory.MinorJet.deriv_leadMinor_exp | (intros; apply GlobalTheory.MinorJet.deriv_leadMinor_exp <;> assumption)
end
