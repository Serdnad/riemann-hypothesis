module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.AutomorphicL2Local

theorem tsum_indicator_le {G : Type*} [Group G] (Γ : Subgroup G) (C : Set G) (x : G) (a : ℝ≥0∞) :
    ∑' γ : Γ, C.indicator (fun _ => a) (γ * x) ≤ ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) * a := by
  classical
  set T : Set Γ := {γ | (γ : G) * x ∈ C} with hT
  have h1 : (fun γ : Γ => C.indicator (fun _ => a) ((γ : G) * x)) = T.indicator (fun _ => a) := by
    ext γ
    simp [T, Set.indicator_apply]
  rw [h1, ← tsum_subtype T (fun _ => a), ENNReal.tsum_set_const]
  have hle : T.encard ≤ {γ : Γ | (γ : G) ∈ C * C⁻¹}.encard := by
    rcases T.eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
    · simp [h]
    calc T.encard = ((fun γ => γ * γ₀⁻¹) '' T).encard :=
          (Set.InjOn.encard_image (s := T) (f := fun γ : Γ => γ * γ₀⁻¹)
            (fun _ _ _ _ h => mul_right_cancel h)).symm
      _ ≤ _ := by
          refine Set.encard_le_encard ?_
          rintro _ ⟨γ, hγ, rfl⟩
          refine Set.mem_mul.mpr ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, by simpa [hT] using hγ₀, ?_⟩
          simp [mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) bot_le

theorem memLp_restrict_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F C hC
  classical
  have hmeas : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  set N : ℝ≥0∞ := (({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℕ∞) : ℝ≥0∞) with hNdef
  have hN : N ≠ ⊤ := by
    have hfin : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    simpa [N] using hfin.encard_lt_top.ne
  have hF2 : ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ∞ := by
    have := (Lp.memLp F).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)] at this
    simpa using this
  have key : ∫⁻ g, ‖lift Γ F g‖ₑ ^ (2 : ℝ) ∂μ.restrict C < ∞ := by
    rw [← lintegral_indicator hCm,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeas.enorm.pow_const (2 : ℝ)).indicator hCm)]
    calc ∫⁻ q, ∑' γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out) ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ
        ≤ ∫⁻ q, N * ‖F q‖ₑ ^ (2 : ℝ) ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
          refine lintegral_mono fun q => ?_
          have e : ∀ γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out)
              = C.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) (γ * q.out) := by
            intro γ
            simp only [Set.indicator_apply]
            split_ifs
            · simp [lift, mk_mul, Quotient.out_eq]
            · rfl
          simp_rw [e]
          exact tsum_indicator_le Γ C q.out _
      _ = N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := lintegral_const_mul' _ _ hN
      _ < ∞ := ENNReal.mul_lt_top hN.lt_top hF2
  have hLp : MemLp (lift Γ F) 2 (μ.restrict C) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas.restrict]
    simpa using key
  refine ⟨hLp, ?_⟩
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  exact hLp.integrable one_le_two

end GlobalTheory.AutomorphicL2Local
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

theorem isThB_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) →
    l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ _ hl2 hlN hN hlA n w _ b _ φ φ' h h' r
  obtain ⟨f, hfinv, hfcls, hfδ, hfdl⟩ := h
  obtain ⟨f', hf'inv, hf'cls, hf'δ, hf'dl⟩ := h'
  obtain ⟨u, hu⟩ := Tower.cls_eq_pow X l n f f' (hfcls.symm.trans hf'cls)
  have hL : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hfne : (f : X.K) ≠ 0 := f.ne_zero
  have hune : (u : X.K) ≠ 0 := u.ne_zero
  have hpow : (u : X.K) ^ (l ^ n) = (f' : X.K) * (f : X.K)⁻¹ := by
    rw [hu]; field_simp
  have hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((u : X.K) ^ (l ^ n)) := by
    intro γ hγ
    rw [hpow, map_mul, map_inv₀, hfinv γ hγ, hf'inv γ hγ]
  have hT : X.sl (ofSL ModularGroup.T) (u : X.K) = u := by
    refine TInv.sl_T_eq X N l n (Fact.out) hl2 hlN hN u hune hinv ?_
    intro δ hδ hδ'
    obtain ⟨g, hg, hfg⟩ := hfδ δ hδ hδ'
    obtain ⟨g', hg', hfg'⟩ := hf'δ δ hδ hδ'
    have hgne : g ≠ 0 := by
      rintro rfl
      rw [zero_pow hL.ne'] at hfg
      exact mul_ne_zero hfne ((map_ne_zero _).2 hfne) hfg
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · intro γ hγ
      rw [map_mul, map_inv₀, hg γ hγ, hg' γ hγ]
    · have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := (map_ne_zero _).2 hfne
      rw [mul_pow g', inv_pow, ← hfg, ← hfg', hu, map_mul, map_pow]
      field_simp
      ring
  have : Algebra.IsAlgebraic ℚ Ω := DlPow.isAlgebraic_of_tower X
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  rw [hu] at hf'dl
  exact DlPow.isDl_mul_lpow_cong X A l hlA n f u hfne hune hT φ φ' hfdl hf'dl r

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.logDerivQExpansion_mul_primePow_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits → ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 → X.sl (ofSL ModularGroup.T) u = u → ∀ φ φ' : HahnSeries ℚ Ω, IsDl X A l n 1 f φ → IsDl X A l n 1 (f * u ^ (l ^ n)) φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  exact @GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong Ω _ _ _
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.LamZero

theorem map_slP {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (Q : MvPolynomial (Fin 2) R) : MvPolynomial.map f (slP m Q) = slP m (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_coef_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (c • Q) = f c • MvPolynomial.map f Q := by
  simp [MvPolynomial.smul_eq_C_mul]

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem eq_zero_of_sum {k : ℕ} {v : Fin k → E} (hv : LinearIndependent ℤ_[l] v)
    (Q : Fin k → MvPolynomial (Fin 2) ℤ_[l])
    (h : ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) = 0) (a : Fin k) : Q a = 0 := by
  ext m
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
    smul_eq_mul] at h1
  have := Fintype.linearIndependent_iff.1 hv (fun a => AddMonoidAlgebra.coeff (Q a) m) (by
    simpa [Algebra.smul_def, mul_comm] using h1)
  simpa using this a

theorem exists_basis (hinj : Function.Injective (algebraMap ℤ_[l] E)) (S : Finset E) :
    ∃ (k : ℕ) (v : Fin k → E) (r : E → Fin k → ℤ_[l]), LinearIndependent ℤ_[l] v ∧
      ∀ x ∈ S, x = ∑ a, r x a • v a := by
  classical
  let L := Submodule.span ℤ_[l] (S : Set E)
  haveI : Module.Finite ℤ_[l] L := Module.Finite.span_finset _ _
  haveI : NoZeroSMulDivisors ℤ_[l] E := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h⟩
  haveI : Module.Free ℤ_[l] L := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] L
  refine ⟨_, fun a => (b a : E), fun x => if h : x ∈ L then b.repr ⟨x, h⟩ else 0, ?_, ?_⟩
  · exact b.linearIndependent.map' L.subtype (by simp)
  · intro x hx
    have hxL : x ∈ L := Submodule.subset_span hx
    have h2 : ((∑ i, (b.repr ⟨x, hxL⟩) i • b i : L) : E) = x := congrArg Subtype.val (b.sum_repr _)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    simp only [dif_pos hxL]
    exact h2.symm

theorem poly_decomp {k : ℕ} (v : Fin k → E) (r : E → Fin k → ℤ_[l]) (P : MvPolynomial (Fin 2) E)
    (hr : ∀ m ∈ P.support, P.coeff m = ∑ a, r (P.coeff m) a • v a) :
    ∃ Q : Fin k → MvPolynomial (Fin 2) ℤ_[l], P = ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) := by
  classical
  refine ⟨fun a => ∑ m ∈ P.support, MvPolynomial.monomial m (r (P.coeff m) a), ?_⟩
  ext n

  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial,
  smul_eq_mul, map_sum]
  by_cases hn : n ∈ P.support
  · simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_pos hn]
    refine (hr n hn).trans ?_
    simp [Algebra.smul_def, mul_comm]
  · rw [MvPolynomial.notMem_support_iff.1 hn]
    simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_neg hn, mul_zero,
      Finset.sum_const_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem sum_reorg {n k : ℕ} (f : Fin n → E) (v : Fin k → E) (c : Fin n → Fin k → ℤ_[l])
    (hf : ∀ i, f i = ∑ a, c i a • v a) (F : Fin n → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (∑ i, c i a • F i) =
      ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i) := by

  simp only [map_sum, map_coef_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Algebra.smul_def]
  exact mul_comm _ _

theorem sum_slP {k : ℕ} (v : Fin k → E) (m : Matrix (Fin 2) (Fin 2) ℤ) (A B : Fin k → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (slP m (A a) - B a) =
      slP m (∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (A a)) -
        ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (B a) := by

  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, RingHom.map_sub, map_slP, smul_sub]

theorem tmul_sum_zero {M : Type} [AddCommGroup M] [Module ℤ_[l] M] {n k : ℕ} (f : Fin n → E) (v : Fin k → E)
    (c : Fin n → Fin k → ℤ_[l]) (hf : ∀ i, f i = ∑ a, c i a • v a) (b : Fin n → M)
    (hb : ∀ a, ∑ i, c i a • b i = 0) : ∑ i, f i ⊗ₜ[ℤ_[l]] b i = 0 := by
  have : ∀ i, f i ⊗ₜ[ℤ_[l]] b i = ∑ a, v a ⊗ₜ[ℤ_[l]] (c i a • b i) := by
    intro i
    rw [hf i, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← TensorProduct.tmul_sum, hb a, TensorProduct.tmul_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem rel_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n : ℕ} (b : Fin n → X.Fn l)
    (F : Fin n → ℂ → MvPolynomial (Fin 2) ℤ_[l]) (hR : ∀ j, Rel X l (b j) (F j)) (c : Fin n → ℤ_[l]) :
    Rel X l (∑ j, c j • b j) (∑ j, c j • F j) := by
  obtain ⟨hadd, hzero, hsmul, -, -⟩ := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have : ∀ s : Finset (Fin n), Rel X l (∑ j ∈ s, c j • b j) (∑ j ∈ s, c j • F j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd _ _ _ _ (hsmul _ _ _ (hR j)) ih
  exact this Finset.univ

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3


open LamZero in
theorem lam_fst_eq_zero_of_triv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  intro Ω _ _ ε X l _ E _ _ hinj w Γ M₀ hM₀ hΓ p hp hT
  classical
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hp
  choose b F hRel hg using fun i => (g i).2
  obtain ⟨ψ, P, hψ, hP⟩ := hT
  obtain ⟨k, v, r, hv, hr⟩ := exists_basis hinj (Finset.univ.image f ∪ P.support.image (fun m => P.coeff m))
  have hf : ∀ i, f i = ∑ a, r (f i) a • v a := fun i =>
    hr _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  obtain ⟨Q, hQ⟩ := poly_decomp v r P (fun m hm =>
    hr _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)))
  let c : Fin n → Fin k → ℤ_[l] := fun i a => r (f i) a
  let G : Fin k → ℂ → MvPolynomial (Fin 2) ℤ_[l] := fun a z => ∑ i, c i a • F i z
  have hp1 : p.1 = ∑ i, f i ⊗ₜ[ℤ_[l]] b i := by
    rw [← hfg]
    simp [Prod.fst_sum, hg, TensorProduct.smul_tmul']
  have hp2 : ∀ z, p.2 z = ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i z) := by
    intro z
    rw [← hfg]
    simp [Prod.snd_sum, Finset.sum_apply, hg]
  have hkey : ∀ z, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a z) = p.2 z := fun z =>
    (sum_reorg f v c hf (fun i => F i z)).trans (hp2 z).symm
  have e1 : ∀ y, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a y - Q a) = p.2 y - P := by
    intro y
    simp only [RingHom.map_sub, smul_sub, Finset.sum_sub_distrib, hkey, ← hQ]
  have hGT : ∀ a, (fun z => G a z) ∈ Triv ℤ_[l] w Γ := by
    intro a
    refine ⟨fun z => G a z - Q a, Q a, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have hγz : mob (ofSL γ) z ∈ Hs := GlobalTheory.KZ.MobLaws.mob_mem _ hz
    have h0 := eq_zero_of_sum hv (fun a => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (G a (mob (ofSL γ) z) - Q a) -
      (G a z - Q a)) (by
        rw [sum_slP, e1, e1, hP _ hγz, hP _ hz, add_sub_cancel_right, add_sub_cancel_right, hψ γ hγ z hz, sub_self]) a
    exact sub_eq_zero.1 h0
  have hb : ∀ a, ∑ i, c i a • b i = 0 := by
    intro a
    have hR := rel_sum X l b F hRel (fun i => c i a)
    have hG : (∑ i, c i a • F i) = fun z => G a z := by
      funext z; simp [G, Finset.sum_apply]
    rw [hG] at hR
    exact GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero Ω ε X l w Γ M₀ hM₀ hΓ _ _ hR (hGT a)
  rw [hp1]
  exact tmul_sum_zero f v c hf b hb

end GlobalTheory.KZ.H3
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.H3.LamStab

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, Betti.slP_X, map_add (f := _), map_smul]
    simp [MvPolynomial.smul_eq_C_mul]

theorem opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opP S m (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opP R m F z) := by
  funext z
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, polySlash_map]

theorem sum_opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} (s : Finset ι)
    (m : ι → Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    (∑ j ∈ s, opP S (m j)) (fun z => MvPolynomial.map φ (F z)) =
      fun z => MvPolynomial.map φ ((∑ j ∈ s, opP R (m j)) F z) := by
  funext z

  simp only [LinearMap.sum_apply, Finset.sum_apply, opP_map, map_sum]

theorem opL_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N l : ℕ) (T : Letter)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opL S N l T (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opL R N l T F z) := by
  cases T with
  | T q =>
    simp only [opL, LinearMap.add_apply, sum_opP_map, opP_map]
    funext z; simp
  | U => simp only [opL, sum_opP_map]
  | D d => simp only [opL, opP_map]

end GlobalTheory.KZ.H3.LamStab


open GlobalTheory.KZ.H3 GlobalTheory.KZ.H3.LamStab in
theorem GlobalTheory.KZ.H3.lam_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)),
    p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l _ E _ _ T p hp
  let Φ : ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) →ₗ[E]
      ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
    LinearMap.prodMap (X.opV N l E T) (opL E N l T)
  have key : abelian₂ X l E ≤ (abelian₂ X l E).comap Φ := by
    unfold abelian₂
    rw [Submodule.span_le]
    rintro q ⟨b, F, hR, rfl⟩
    refine Submodule.subset_span ⟨X.op N l T b, opL ℤ_[l] N l T F,
      (GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l).2.2.2.2 N T b F hR, ?_⟩
    simp only [Φ, LinearMap.prodMap_apply, Tower.opV, LinearMap.baseChange_tmul, opL_map]
  exact key hp
end
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.exists_multiset_satakeEigenvalue_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 → ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  first | exact @GlobalTheory.LFun.exists_satEig_eq | exact GlobalTheory.LFun.exists_satEig_eq | (intros; apply GlobalTheory.LFun.exists_satEig_eq <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.vacuumTranslate_conjugate_jet_bound : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  first | exact @GlobalTheory.ConjJet.conj_jet_bound | exact GlobalTheory.ConjJet.conj_jet_bound | (intros; apply GlobalTheory.ConjJet.conj_jet_bound <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.vacuum_under_adelic_pair_modulus_one : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  first | exact @GlobalTheory.NormSum.vacuum_under_adelic_pair | exact GlobalTheory.NormSum.vacuum_under_adelic_pair | (intros; apply GlobalTheory.NormSum.vacuum_under_adelic_pair <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | exact GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | (intros; apply GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span <;> assumption)
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
end
