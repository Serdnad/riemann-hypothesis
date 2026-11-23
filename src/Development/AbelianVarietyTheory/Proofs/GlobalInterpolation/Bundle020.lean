module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.DedekindDomain.Instances
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LocalLattice

noncomputable section

namespace GlobalTheory.SemiLocalFrame

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ (𝓞 E)⁰ :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

def semiLoc : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)
    (algebraMapSubmonoid_le E v)

instance isLocalization_semiLoc :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) (semiLoc E v) :=
  Localization.subalgebra.isLocalization_ofField E _ _

instance isFractionRing_semiLoc : IsFractionRing (semiLoc E v) E :=
  Localization.subalgebra.isFractionRing_ofField E _ _

instance isPrincipalIdealRing_semiLoc : IsPrincipalIdealRing (semiLoc E v) :=
  haveI : IsDedekindDomain (semiLoc E v) :=
    IsLocalization.isDedekindDomain (𝓞 E) (algebraMapSubmonoid_le E v) _
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

variable {E}

theorem mem_span_semiLoc_iff {V : Type*} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) (x : V) :
    x ∈ Submodule.span (semiLoc E v) (N : Set V) ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ N := by
  rw [mem_span_localization_iff (semiLoc E v)
    (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)]
  exact ⟨fun ⟨_, ⟨s, hs, rfl⟩, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨_, ⟨s, hs, rfl⟩, h⟩⟩

theorem exists_of_mem_semiLoc {z : E} (hz : z ∈ semiLoc E v) :
    ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (1 : Submodule (𝓞 E) E) := by
  have h := mem_span_semiLoc_iff v (1 : Submodule (𝓞 E) E) z
  rw [Submodule.one_eq_span, Submodule.span_span_of_tower, Submodule.mem_span_singleton,
    ← Submodule.one_eq_span] at h
  exact h.1 ⟨⟨z, hz⟩, mul_one z⟩

theorem exists_common {ι : Type*} [Finite ι] {V : Type*} [AddCommGroup V] [Module (𝓞 E) V]
    (N : Submodule (𝓞 E) V) (x : ι → V)
    (h : ∀ i, ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N) :
    ∃ s ∉ v.asIdeal, ∀ i, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N := by
  classical
  haveI := Fintype.ofFinite ι
  choose s hs h using h
  refine ⟨∏ i, s i, (prod_mem (S := v.asIdeal.primeCompl) fun i _ => hs i), fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]
  exact N.smul_mem _ (h i)

theorem exists_frame {k : ℕ} (L : Submodule (𝓞 E) (Fin k → E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin k → E)) = ⊤) :
    ∃ g : GL (Fin k) E, ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ semiLoc E v := by
  haveI : Submodule.IsLattice E (Submodule.span (semiLoc E v) (L : Set (Fin k → E))) := by
    constructor
    · obtain ⟨s, rfl⟩ := h1
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) _ _).symm⟩
    · exact fun _ _ => (LinearIndependent.iff_fractionRing (semiLoc E v) E).mp
  haveI : Submodule.IsFullLattice E (Submodule.span (semiLoc E v) (L : Set (Fin k → E))) := by
    constructor
    rw [Submodule.span_span_of_tower, h2]
  obtain ⟨g, hg⟩ := exists_eq_frameLattice (Submodule.span (semiLoc E v) (L : Set (Fin k → E)))
  refine ⟨g, fun x => ?_⟩
  rw [← mem_span_semiLoc_iff, hg, mem_frameLattice_iff_inv]
  exact forall_congr' fun i =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem smul_eq (c : 𝓞 F) (z : E) :
    algebraMap (𝓞 F) (𝓞 E) c • z = algebraMap F E (c : F) * z := by
  rw [Algebra.smul_def]; rfl

theorem exists_frame_denominator (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (B : GL (Fin k) E) (c : 𝓞 F), c ∉ v.asIdeal ∧
      (∀ x ∈ Λ, ∀ i, algebraMap F E (c : F) *
        (((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
          (algebraMap (𝓞 E) E).range) ∧
      ∀ j, (fun i => algebraMap F E (c : F) * (B : Matrix (Fin k) (Fin k) E) i j) ∈ Λ := by
  have hfg : Λ.FG := Module.Finite.iff_fg.1 hfin
  obtain ⟨g, hg⟩ := exists_frame v Λ hfg hspan
  obtain ⟨S, hS⟩ := hfg
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  obtain ⟨a, ha, hA⟩ := exists_common v (ι := S × Fin k) (1 : Submodule (𝓞 E) E)
    (fun p => (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ (p.1 : Fin k → E)) p.2)
    (fun p => exists_of_mem_semiLoc v ((hg _).1 ⟨1, hone, by
      rw [map_one, one_smul, ← hS]; exact Submodule.subset_span p.1.2⟩ p.2))
  obtain ⟨b, hb, hB⟩ := exists_common v Λ
    (fun j : Fin k => fun i => (g : Matrix (Fin k) (Fin k) E) i j) (fun j => by
      refine (hg _).2 fun i => ?_
      have : (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ
          (fun k => (g : Matrix _ _ E) k j)) i = (1 : Matrix (Fin k) (Fin k) E) i j := by
        rw [← Units.inv_mul g]; rfl
      rw [this, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
  refine ⟨g, b * a, fun h => (v.isPrime.mem_or_mem h).elim hb ha, fun x hx i => ?_, fun j => ?_⟩
  · have key : algebraMap (𝓞 F) (𝓞 E) a •
        (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ (1 : Submodule (𝓞 E) E) := by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hA (⟨y, hy⟩, i)
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.mulVec_add, Pi.add_apply, smul_add]; exact add_mem hy hz
      | smul r y _ hy =>
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy
    have := Submodule.smul_mem _ (algebraMap (𝓞 F) (𝓞 E) b) key
    rw [← mul_smul, ← map_mul, smul_eq] at this
    exact Submodule.mem_one.1 this
  · have := Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) (hB j)
    rw [← mul_smul, ← map_mul, mul_comm a b] at this
    convert this using 1
    funext i
    rw [Pi.smul_apply, smul_eq]

end GlobalTheory.SemiLocalFrame
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.RayGen

variable {K : Type} [Field K] [NumberField K]

def compAt (v : HeightOneSpectrum (𝓞 K)) : Ideles K →* v.adicCompletion K where
  toFun a := (a : AdeleRing (𝓞 K) K).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def compInf (w : InfinitePlace K) : Ideles K →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 K) K).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def unifAway (𝔮 : Ideal (𝓞 K)) : Subgroup (Ideles K) :=
  Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ),
    ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}

theorem comp_of_mem_unifAway {𝔮 : Ideal (𝓞 K)} {b : Ideles K} (hb : b ∈ unifAway 𝔮) :
    (∀ w, compInf w b = 1) ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → compAt v b = 1 := by
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, π, hv, -, rfl⟩ := hx
    exact ⟨(localIdele_isSupportedAt K v π).1,
      fun v' hv' => (localIdele_isSupportedAt K v π).2 v' (by rintro rfl; exact hv hv')⟩
  | one => exact ⟨fun w => map_one _, fun v _ => map_one _⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun w => by rw [map_mul, hx.1, hy.1, one_mul], fun v hv => by rw [map_mul, hx.2 v hv, hy.2 v hv, one_mul]⟩
  | inv x _ hx => exact ⟨fun w => by rw [map_inv, hx.1, inv_one], fun v hv => by rw [map_inv, hx.2 v hv, inv_one]⟩

theorem exists_unifAway {𝔮 : Ideal (𝓞 K)} (c : Ideles K)
    (hc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → Valued.v (compAt v c) = 1) :
    ∃ b ∈ unifAway 𝔮, ∀ v, Valued.v (compAt v b) = Valued.v (compAt v c) := by
  classical
  choose π hπ using exists_isUniformiserAt K
  have hfin := Filter.eventually_cofinite.mp (valued_comp_eventually K c)
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ Valued.v (compAt v c) ≠ 1 := fun v => hfin.mem_toFinset
  refine ⟨∏ v ∈ S, localIdele K v (π v) ^ ordAt K v c, Subgroup.prod_mem _ fun v hv => Subgroup.zpow_mem _
    (Subgroup.subset_closure (by exact ⟨v, π v, fun h => (hS v).1 hv (hc v h), hπ v, rfl⟩)) _, fun w => ?_⟩
  have h1 : ∀ v, v ≠ w → compAt w (localIdele K v (π v) ^ ordAt K v c) = 1 := fun v hv => by
    rw [map_zpow, show compAt w (localIdele K v (π v)) = 1 from (localIdele_isSupportedAt K v _).2 w hv.symm,
      one_zpow]
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv => h1 v hv, map_zpow,
      show compAt w (localIdele K w (π w)) = π w from localIdele_snd_self K w _, map_zpow₀,
      valued_eq_exp_of_isUniformiserAt K w _ (hπ w), ← WithZero.exp_zsmul, ordAt]
    rw [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one]
    exact WithZero.exp_log (valued_comp_ne_zero K c w)
  · rw [Finset.prod_eq_one fun v hv => h1 v (fun e => hw (e ▸ hv)), map_one]
    exact (not_not.1 ((hS w).not.1 hw)).symm

theorem valued_lt_one_of_mem (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ∈ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have e : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_lt_one_iff_mem x).2 hx

theorem exists_approx {𝔮 : Ideal (𝓞 K)} (h𝔮 : 𝔮 ≠ ⊥) {x : 𝓞 K} (hx : x ∈ 𝔮) (hx0 : x ≠ 0) (a : Ideles K) :
    ∃ k : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (compAt v ((diagUnits K k)⁻¹ * a) - 1) ≤ Valued.v (algebraMap K (v.adicCompletion K) (x : K))) ∧
      ∀ w : InfinitePlace K, w.IsReal → IsSquare (compInf w ((diagUnits K k)⁻¹ * a)) := by
  classical
  let T := (Ideal.finite_factors h𝔮).toFinset
  let t' : InfinitePlace K → ℝ := fun w =>
    if hw : w.IsReal then InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) else 1
  have ht' : ∀ w, t' w ≠ 0 := fun w => by
    simp only [t']
    split_ifs with hw
    · exact (map_ne_zero _).2 (inf_comp_ne_zero K a w)
    · exact one_ne_zero
  let t : (K →+* ℝ) → ℝ := fun σ => t' (InfinitePlace.mk (Complex.ofRealHom.comp σ))
  let r : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v =>
    (algebraMap K (v.adicCompletion K) (x : K) * compAt v a)⁻¹
  let U : Set (((v : T) → v.1.adicCompletion K) × ((K →+* ℝ) → ℝ)) :=
    (⋂ v : T, {y | (y.1 v - compAt v.1 a) * r v.1 ∈ v.1.adicCompletionIntegers K}) ∩
      ⋂ σ : K →+* ℝ, {y | 0 < y.2 σ * t σ}
  have : Finite (K →+* ℝ) :=
    Finite.of_injective (fun σ : K →+* ℝ => Complex.ofRealHom.comp σ) (fun σ τ h => by
      ext y
      simpa using RingHom.congr_fun h y)
  have hU : IsOpen U := by
    refine (isOpen_iInter_of_finite fun v => ?_).inter (isOpen_iInter_of_finite fun σ => ?_)
    · have h : IsOpen (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K)) :=
        Valued.isOpen_valuationSubring _
      exact h.preimage ((((continuous_apply v).comp continuous_fst).sub continuous_const).mul continuous_const)
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  obtain ⟨k, hk1, hk2⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real K T).exists_mem_open hU
    ⟨(fun v => compAt v.1 a, t), Set.mem_iInter.2 fun v => by simp,
      Set.mem_iInter.2 fun σ => mul_self_pos.2 (ht' _)⟩
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx0
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k - compAt v a) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (x : K)) * Valued.v (compAt v a) := fun v hv => by
    have h : Valued.v ((algebraMap K (v.adicCompletion K) k - compAt v a) * r v) ≤ 1 :=
      Set.mem_iInter.1 hk1 ⟨v, (Ideal.finite_factors h𝔮).mem_toFinset.2 hv⟩
    have h0 : Valued.v (algebraMap K (v.adicCompletion K) (x : K) * compAt v a) ≠ 0 :=
      (map_ne_zero _).2 (mul_ne_zero ((map_ne_zero _).2 hxK) (comp_ne_zero K a v))
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul, map_mul] at h
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k) = Valued.v (compAt v a) := fun v hv => by
    refine Valuation.map_eq_of_sub_lt _ ((h1 v hv).trans_lt ?_)
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 (valued_comp_ne_zero K a v))
      (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  have h3 : ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw k *
      InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) := fun w hw => by
    have h : 0 < InfinitePlace.embedding_of_isReal hw k * t (InfinitePlace.embedding_of_isReal hw) :=
      Set.mem_iInter.1 hk2 _
    have e : InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w := by
      refine Eq.trans ?_ (InfinitePlace.mk_embedding w)
      congr 1
      ext y
      simp
    change 0 < _ * t' _ at h
    rw [e] at h
    simpa only [t', dif_pos hw] using h
  by_cases hk : k = 0
  · subst hk
    refine ⟨1, fun v hv => absurd (h2 v hv).symm ?_, fun w hw => absurd (h3 w hw) (by simp)⟩
    rw [map_zero, map_zero]
    exact valued_comp_ne_zero K a v
  refine ⟨Units.mk0 k hk, fun v hv => ?_, fun w hw => ?_⟩
  · have hk' : algebraMap K (v.adicCompletion K) k ≠ 0 := (map_ne_zero _).2 hk
    rw [map_mul, map_inv, show compAt v (diagUnits K (Units.mk0 k hk)) = algebraMap K (v.adicCompletion K) k from rfl,
      show (algebraMap K (v.adicCompletion K) k)⁻¹ * compAt v a - 1 =
        (compAt v a - algebraMap K (v.adicCompletion K) k) * (algebraMap K (v.adicCompletion K) k)⁻¹ by
          field_simp, map_mul, map_inv₀, h2 v hv, Valuation.map_sub_swap,
      mul_inv_le_iff₀ (c := Valued.v (compAt v a)) (zero_lt_iff.2 (valued_comp_ne_zero K a v))]
    exact h1 v hv
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : e (algebraMap K w.Completion k) = InfinitePlace.embedding_of_isReal hw k := by
      simp [e, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    have hp : 0 < e (compInf w ((diagUnits K (Units.mk0 k hk))⁻¹ * a)) := by
      rw [map_mul, map_inv, show compInf w (diagUnits K (Units.mk0 k hk)) = algebraMap K w.Completion k from rfl,
        map_mul, map_inv₀, he, mul_comm, ← div_eq_mul_inv, div_pos_iff, ← mul_pos_iff, mul_comm]
      exact h3 w hw
    have := (Real.isSquare_iff.2 hp.le).map e.symm
    rwa [e.symm_apply_apply] at this

theorem exists_diag_mul_ray_mul_unif : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ a : Ideles K, ∃ k : Kˣ, ∃ u ∈ rayUnits K 𝔮 {w | w.IsReal}, ∃ b ∈ Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}, a = diagUnits K k * u * b := by
  intro K _ _ 𝔮 h𝔮 a
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮
  obtain ⟨k, hk1, hk2⟩ := exists_approx h𝔮 hx hx0 a
  set c := (diagUnits K k)⁻¹ * a with hc
  obtain ⟨b, hb, hbv⟩ := exists_unifAway (𝔮 := 𝔮) c fun v hv => by
    rw [Valuation.map_eq_of_sub_lt _ (x := 1), map_one]
    rw [map_one]
    exact (hk1 v hv).trans_lt (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  obtain ⟨hb1, hb2⟩ := comp_of_mem_unifAway hb
  refine ⟨k, c * b⁻¹, ⟨fun w hw => ?_, fun v => ?_⟩, b, hb, by rw [hc]; group⟩
  · change IsSquare (compInf w (c * b⁻¹))
    rw [map_mul, map_inv, hb1, inv_one, mul_one]
    exact hk2 w hw
  · have h1 : Valued.v (compAt v (c * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv₀, hbv]
      exact mul_inv_cancel₀ (valued_comp_ne_zero K c v)
    refine ⟨h1, ?_⟩
    change ∃ x ∈ 𝔮, Valued.v (compAt v (c * b⁻¹) - 1) ≤ _
    by_cases hv : v.asIdeal ∣ 𝔮
    · rw [map_mul, map_inv, hb2 v hv, inv_one, mul_one]
      exact ⟨x, hx, hk1 v hv⟩
    · obtain ⟨y, hy, hyv⟩ := SetLike.not_le_iff_exists.mp (Ideal.dvd_iff_le.not.1 hv)
      refine ⟨y, hy, ?_⟩
      rw [valued_algebraMap_eq_one K v y hyv]
      exact Valuation.map_sub_le _ h1.le (map_one _).le

end GlobalTheory.RayGen

end
end
