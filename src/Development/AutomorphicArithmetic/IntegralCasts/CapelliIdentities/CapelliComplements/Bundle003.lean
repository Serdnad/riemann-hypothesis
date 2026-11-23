module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
public import Mathlib.RingTheory.Valuation.Integral
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Bl.KappaIntegralBound

private lemma kappaIntBound {K : Type} [Field K] [NumberField K] (p : Nat.Primes)
    (κ : K →+* PadicComplex p.val) (r : NumberField.RingOfIntegers K) :
    ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := by
  let w : Valuation K NNReal := (NormedField.valuation (K := PadicComplex p.val)).comap κ
  have hi : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
    NumberField.RingOfIntegers.isIntegral_coe r
  have hO : IsIntegral w.integer (algebraMap (NumberField.RingOfIntegers K) K r) := hi.tower_top
  have hm : algebraMap (NumberField.RingOfIntegers K) K r ∈ w.integer :=
    (Valuation.integer.integers w).mem_of_integral hO
  rw [Valuation.mem_integer_iff] at hm
  have h2 : ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖₊ ≤ 1 := hm
  exact_mod_cast h2

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [inst_1 : NumberField.{0} K] (p : Nat.Primes)
  (κ : RingHom.{0, 0} K (PadicComplex (Subtype.val.{1} p))),
  Exists.{1} fun (la : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K)) ↦
    ∀ (a : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K la) a) 1)
        (LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} κ a)) 1) := by
  intro K _ _ p κ
  have hle : ∀ r : NumberField.RingOfIntegers K,
      ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := fun r => kappaIntBound p κ r
  let I : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {r | ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        calc ‖κ (algebraMap _ K c)‖ * ‖κ (algebraMap _ K a)‖
            ≤ 1 * ‖κ (algebraMap _ K a)‖ := mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact ha }
  have hmem : ∀ r, r ∈ I ↔ ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1 :=
    fun r => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem, map_mul, map_mul, norm_mul] at hab
      rw [hmem, hmem]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      have ha := le_antisymm (hle a) h.1
      have hb := le_antisymm (hle b) h.2
      rw [ha, hb, mul_one] at hab
      exact lt_irrefl _ hab
  have hpI : ((p.val : ℕ) : NumberField.RingOfIntegers K) ∈ I := by
    rw [hmem, map_natCast, map_natCast]
    rw [show ((p.val : ℕ) : PadicComplex p.val) = (((p.val : ℕ) : Padic p.val) : PadicComplex p.val)
      from by simp]
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpI
    have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hpI
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact p.2.ne_zero h2
  let la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := ⟨I, hIprime, hne⟩
  refine ⟨la, fun a => ?_⟩
  obtain ⟨n, d, h | h⟩ := la.exists_primeCompl_mul_eq_or_mul_eq a
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv : la.valuation K a = la.valuation K (algebraMap _ K n) := by
      rw [← h, map_mul, hvd, mul_one]
    have hN : ‖κ a‖ = ‖κ (algebraMap _ K n)‖ := by
      rw [← h, map_mul, norm_mul, hNd, mul_one]
    rw [hv, hN]
    exact iff_of_true (la.valuation_le_one (K := K) n) (hle n)
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv2 : la.valuation K a * la.valuation K (algebraMap _ K n) = 1 := by
      rw [← map_mul, h, hvd]
    have hN2 : ‖κ a‖ * ‖κ (algebraMap _ K n)‖ = 1 := by
      rw [← norm_mul, ← map_mul, h, hNd]
    have key1 : la.valuation K a ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha
        have h1 : 1 ≤ la.valuation K (algebraMap _ K n) := hv2 ▸ mul_le_of_le_one_left' ha
        exact (la.valuation_eq_one_iff_notMem (K := K)).mp
          (le_antisymm (la.valuation_le_one (K := K) n) h1)
      · intro hn
        have h1 := (la.valuation_eq_one_iff_notMem (K := K)).mpr hn
        rw [h1, mul_one] at hv2
        exact hv2.le
    have key2 : ‖κ a‖ ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha hn
        have h1 : 1 ≤ ‖κ (algebraMap _ K n)‖ := by
          rw [← hN2]; exact mul_le_of_le_one_left (norm_nonneg _) ha
        exact absurd ((hmem n).mp hn) (not_lt.mpr h1)
      · intro hn
        have h1 : ‖κ (algebraMap _ K n)‖ = 1 := le_antisymm (hle n) (not_lt.mp hn)
        rw [h1, mul_one] at hN2
        exact hN2.le
    rw [key1, key2]

end Bl.KappaIntegralBound
end

section

namespace Bl.EqIdOfFixed

private lemma ne_id_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h
  obtain ⟨-, hc, -, hs⟩ := h
  by_contra hne0
  have hne : ∀ z : E, σ z = z := fun z => by_contra fun hz => hne0 ⟨z, hz⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := hc
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have := hs τ z
  rw [hne z] at this
  exact this.symm

private lemma eq_id_of_fix {F E : Type} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) {x : E} (hx : σ x = x)
    (hno : ∀ t : F, algebraMap F E t ≠ x) (y : E) : σ y = y := by
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hno (-(s / t))
      have h1 : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : x = t⁻¹ • -(s • (1 : E)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hc : Fintype.card (Fin 2) = Module.finrank F E := by simp [hd]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E) := by
    apply b.ext
    intro i
    fin_cases i
    · simp [b]
    · simp [b, hx]
  exact LinearMap.congr_fun heq y

theorem goal1 :
  ∀ {F E : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F] [inst_2 : Field.{0} E] [inst_3 : NumberField.{0} E]
  [inst_4 : Algebra.{0, 0} F E] {σ : AlgHom.{0, 0, 0} F E E},
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
    ∀ {x : E},
      Eq.{1} (DFunLike.coe.{1, 1, 1} σ x) x →
        Exists.{1} fun (t : F) ↦ Eq.{1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} F E) t) x := by
  intro F E _ _ _ _ _ σ h x hx
  by_contra hno0
  have hno : ∀ t : F, algebraMap F E t ≠ x := fun t ht => hno0 ⟨t, ht⟩
  obtain ⟨y, hy⟩ := ne_id_of_cm σ h
  have h' := h
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'
  exact hy (eq_id_of_fix h'.2.2.1 σ hx hno y)

end Bl.EqIdOfFixed
end
