module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Lemmata.GeneralBFactThirdMore.Key
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

@[expose] public section

section

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open Formalism.MainNotions.S (Af)
open scoped TensorProduct

theorem exists_den {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp

variable {F : Type} [Field F] [NumberField F]

def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F

theorem ohat_mul {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a * c ∈ Ohat F := by
  intro v
  exact mul_mem (ha v) (hc v)

theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F := by
  intro v
  exact add_mem (ha v) (hc v)

theorem ohat_neg {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) : -a ∈ Ohat F := by
  intro v
  exact neg_mem (ha v)

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).zero_mem

theorem ohat_one : (1 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).one_mem

theorem ohat_sum {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ohat_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ohat_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => rw [zero_nsmul]; exact ohat_zero
  | succ n ih => rw [succ_nsmul]; exact ohat_add ih ha

theorem ohat_zsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [natCast_zsmul]; exact ohat_nsmul ha n
  · rw [neg_zsmul, natCast_zsmul]; exact ohat_neg (ohat_nsmul ha n)

theorem intF_of_int (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := by
  unfold IntF Ohat
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_den_fin {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have key : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((c : 𝓞 F) * a i) := by
    rw [hc, Nat.cast_mul, map_mul, ← ha i, map_natCast]; ring
  rw [key]
  exact intF_of_int _

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

def IntC (x : E ⊗[F] Af F) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

theorem intC_add {x y : E ⊗[F] Af F} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := by
  intro k
  rw [map_add (f := _)]
  exact ohat_add (hx k) (hy k)

theorem intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af F} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := by
  intro k

  rw [map_sum, Finset.sum_apply]
  exact ohat_sum s fun i hi => hf i hi k

theorem smul_eq_algebraMap_mul (c : F) (a : Af F) : c • a = algebraMap F (Af F) c * a :=
  Algebra.smul_def c a

theorem exists_den_mul (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af F, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af F) * algebraMap F (Af F) (b.repr (b i * b j) k) =
      algebraMap F (Af F) ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))

end Coord

end PI.WAU
end
end

section

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af F :=
  fun i => Formalism.UG.inclE (F := F) (Af F) (w i)

theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

theorem one_tmul_mem_intAf {c : Af F} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af F,
      (∀ j k, coord b (y j) k ∈ Ohat F) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af F), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af F) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af F) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af F) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

end PI.WAU
end
end

section

noncomputable section

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def KgSubgroup : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ H : Subgroup I.Gf, (H : Set I.Gf) = I.Kg g

def KCompact : Prop := ∀ I : AutInst, IsCompact I.Kset

def KCountable : Prop :=
  ∀ I : AutInst, ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset

def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)

end PI.WAU
end
end
