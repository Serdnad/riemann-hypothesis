module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023

@[expose] public section

section

open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicMatLat

variable (E : Type) [Field E] [NumberField E]

def intAdeles : Subring (FiniteAdeleRing (𝓞 E) E) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers E)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers E)
  neg_mem' ha v := neg_mem (ha v)

theorem mem_intAdeles {a : FiniteAdeleRing (𝓞 E) E} :
    a ∈ intAdeles E ↔ ∀ v, a v ∈ v.adicCompletionIntegers E := Iff.rfl

theorem algebraMap_mem_iff (x : E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) x ∈ intAdeles E ↔ ∃ r : 𝓞 E, (r : E) = x := by
  rw [mem_intAdeles, ← GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral,
    GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal E),
    FractionalIdeal.mem_one_iff]

theorem exists_nat_denom (x : E) : ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 E, (r : E) = d * x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, c * a, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : E) =
        algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b := by
      rw [← map_mul, hc, map_natCast]
    have h2 : algebraMap (𝓞 E) E b ≠ 0 := by
      simpa using hb0
    rw [h1]
    change algebraMap (𝓞 E) E (c * a) = _
    rw [map_mul]
    field_simp

theorem exists_nat_mul_mem (a : FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 E) E) * a ∈ intAdeles E := by
  obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a
  obtain ⟨d, hd, r, hr⟩ := exists_nat_denom E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add, one_smul]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) hb)
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]
  exact ⟨r, hr⟩

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 E) E) * a i ∈ intAdeles E := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem E (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

variable {E} {n : ℕ}

def lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E}
  add_mem' {x y} hx hy j := by
    simpa only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib] using add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by
    have h : algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) ∈ intAdeles E :=
      (algebraMap_mem_iff E _).2 ⟨c, rfl⟩
    have h2 := mul_mem h (hx j)
    rw [Finset.mul_sum] at h2
    convert h2 using 2 with k
    rw [← mul_assoc, ← map_mul]
    rfl

theorem span_lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.span E (lat β : Set (Fin n → E)) = ⊤ := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β := by
    intro j
    rw [Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]
    simpa using h (i, j)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem fg_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : (lat β.1).FG := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β⁻¹.1 p.1 p.2)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hle : lat β.1 ≤ Submodule.span (𝓞 E)
      (Set.range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E)) := by
    intro x hx
    have h1 : ∀ j, ∃ r : 𝓞 E, (r : E) = d * x j := by
      intro j
      rw [← algebraMap_mem_iff]
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) (d * x j) =
          ∑ l, (∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l) *
            ((d : FiniteAdeleRing (𝓞 E) E) * β⁻¹.1 l j) := by
        have h3 : ((fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)) ᵥ* β.1) ᵥ* β⁻¹.1 =
            fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) := by
          rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
        rw [map_mul, map_natCast, ← congrFun h3 j]
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
      rw [h2]
      exact sum_mem fun l _ => mul_mem (hx l) (h (l, j))
    choose r hr using h1
    have h4 : x = ∑ i, r i • (Pi.single i (d : E)⁻¹ : Fin n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j
        (by intro k _ hk; simp [Pi.single_eq_of_ne hk.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.single_eq_same]
      change x j = (r j : E) * (d : E)⁻¹
      rw [hr]
      field_simp
    rw [h4]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := isNoetherian_span_of_finite (𝓞 E)
    (Set.finite_range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))
  exact Submodule.FG.of_le_of_isNoetherian hle

theorem isLattice_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.IsFullLattice E (lat β.1) := by
  exact { toIsLattice := Submodule.IsLattice.of_fg E (fg_lat β)
          span_eq_top := span_lat β.1 }

theorem inv_mul_mem (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_family E
    (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))
  choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂)
    (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)
  have hxl : x ∈ lat β.1 := by
    intro l
    have h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l =
        (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) *
          ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l) := by
      rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx k, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [h3, Units.inv_mul]
    refine sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨y, hy⟩ := hδ x hxl
  have h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j := by
    have h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E) := by
      rw [hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← congrFun h5 j]
    rfl
  have h6 : (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) +
        ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) *
          ((d₂ : FiniteAdeleRing (𝓞 E) E) *
            algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 k j)) := by

    rw [h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]
    ring
  rw [h6]
  exact add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ =>
    mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))

theorem exists_lattice_integral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  intro E _ _ n β
  refine ⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩
  rw [Matrix.mul_apply]
  exact h1 i j v

end GlobalTheory.AdelicMatLat
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicCocycleLift

variable {l : ℕ} [Fact l.Prime]

theorem toZModPow_eq_zero_iff (r : ℕ) (x : ℤ_[l]) :
    PadicInt.toZModPow r x = 0 ↔ (l : ℤ_[l]) ^ r ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

theorem continuous_toZModPow (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) ?_
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  refine ContinuousAt.congr (f := fun _ => (0 : ZMod (l ^ r))) continuousAt_const ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow] at hx
  exact hx.symm

theorem exists_continuous_div {X : Type*} [TopologicalSpace X] (f : X → ℤ_[l]) (hf : Continuous f)
    (a : ℤ_[l]) (ha : a ≠ 0) (hd : ∀ x, a ∣ f x) :
    ∃ c : X → ℤ_[l], Continuous c ∧ ∀ x, f x = a * c x := by
  choose c hc using hd
  refine ⟨c, ?_, hc⟩
  have ha' : (a : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 ha
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ c : X → ℚ_[l]) = fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) := by
    funext x
    rw [hc x, PadicInt.coe_mul, inv_mul_cancel_left₀ ha']
    rfl
  have h2 : Continuous fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) :=
    continuous_const.mul (continuous_subtype_val.comp hf)
  rw [← e] at h2
  exact h2

theorem exists_continuous_lift {X : Type*} [TopologicalSpace X] (r : ℕ) (f : X → ZMod (l ^ r))
    (hf : Continuous f) :
    ∃ F : X → ℤ_[l], Continuous F ∧ ∀ x, PadicInt.toZModPow r (F x) = f x := by
  have hs : Function.Surjective (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) :=
    ZMod.ringHom_surjective _
  exact ⟨fun x => Function.surjInv hs (f x),
    (continuous_of_discreteTopology (f := Function.surjInv hs)).comp hf,
    fun x => Function.surjInv_eq hs _⟩

variable {Γ : Type} [Group Γ]

noncomputable def dTwo (χ : Γ → ℤ_[l]) (u : Γ × Γ → ℤ_[l]) (p : Γ × Γ × Γ) : ℤ_[l] :=
  χ p.1 * u (p.2.1, p.2.2) - u (p.1 * p.2.1, p.2.2) + u (p.1, p.2.1 * p.2.2) - u (p.1, p.2.1)

def IsCocycleThree (χ : Γ → ℤ_[l]) (c : Γ × Γ × Γ → ℤ_[l]) : Prop :=
  ∀ g h k m, χ g * c (h, k, m) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m)
    + c (g, h, k) = 0

theorem isCocycleThree_dTwo (χ : Γ → ℤ_[l]) (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (u : Γ × Γ → ℤ_[l]) : IsCocycleThree χ (dTwo χ u) := by
  intro g h k m
  simp only [dTwo, hχ, mul_assoc]
  ring

theorem IsCocycleThree.sub {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    (hc' : IsCocycleThree χ c') : IsCocycleThree χ (fun p => c p - c' p) := by
  intro g h k m
  linear_combination hc g h k m - hc' g h k m

theorem IsCocycleThree.cancel {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    {a : ℤ_[l]} (ha : a ≠ 0) (e : ∀ p, c p = a * c' p) : IsCocycleThree χ c' := by
  intro g h k m
  have := hc g h k m
  simp only [e] at this
  apply mul_left_cancel₀ ha
  linear_combination this

variable [TopologicalSpace Γ] [ContinuousMul Γ]

theorem continuous_dTwo {χ : Γ → ℤ_[l]} (hχ : Continuous χ) {u : Γ × Γ → ℤ_[l]}
    (hu : Continuous u) : Continuous (dTwo χ u) := by
  unfold dTwo
  fun_prop


omit [ContinuousMul Γ] in
theorem exists_dTwo_eq (χ : Γ → ℤ_[l])
    (step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p)
    (c : Γ × Γ × Γ → ℤ_[l]) (hc : Continuous c) (hz : IsCocycleThree χ c) :
    ∃ u, Continuous u ∧ ∀ p, c p = dTwo χ u p := by
  choose U C hU hC hCz hE using step
  let T := {c : Γ × Γ × Γ → ℤ_[l] // Continuous c ∧ IsCocycleThree χ c}
  let nx : T → T := fun t => ⟨C t.1 t.2.1 t.2.2, hC _ _ _, hCz _ _ _⟩
  let s : ℕ → T := fun n => nx^[n] ⟨c, hc, hz⟩
  let u : ℕ → Γ × Γ → ℤ_[l] := fun n => U (s n).1 (s n).2.1 (s n).2.2
  have hu : ∀ n, Continuous (u n) := fun n => hU _ _ _
  have hs : ∀ n p, (s n).1 p = dTwo χ (u n) p + l * (s (n + 1)).1 p := by
    intro n p
    have : s (n + 1) = nx (s n) := Function.iterate_succ_apply' _ _ _
    rw [this]
    exact hE _ _ _ p
  have hn : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hb : ∀ (n : ℕ) (x : ℤ_[l]), ‖(l : ℤ_[l]) ^ n * x‖ ≤ ‖(l : ℤ_[l])‖ ^ n := by
    intro n x
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) x.norm_le_one
  have hg : Summable fun n : ℕ => ‖(l : ℤ_[l])‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hn
  have hsum : ∀ x : ℕ → ℤ_[l], Summable fun n => (l : ℤ_[l]) ^ n * x n := fun x =>
    Summable.of_norm_bounded hg fun n => hb n _
  refine ⟨fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q,
    continuous_tsum (fun n => continuous_const.mul (hu n)) hg fun n q => hb n _, fun p => ?_⟩
  have h1 : HasSum (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p)
      (dTwo χ (fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q) p) := by
    have := ((((hsum fun n => u n (p.2.1, p.2.2)).hasSum.mul_left (χ p.1)).sub
      (hsum fun n => u n (p.1 * p.2.1, p.2.2)).hasSum).add
      (hsum fun n => u n (p.1, p.2.1 * p.2.2)).hasSum).sub
      (hsum fun n => u n (p.1, p.2.1)).hasSum
    have e : (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p) = fun n =>
        χ p.1 * ((l : ℤ_[l]) ^ n * u n (p.2.1, p.2.2)) - (l : ℤ_[l]) ^ n * u n (p.1 * p.2.1, p.2.2)
          + (l : ℤ_[l]) ^ n * u n (p.1, p.2.1 * p.2.2) - (l : ℤ_[l]) ^ n * u n (p.1, p.2.1) := by
      funext n
      simp only [dTwo]
      ring
    rw [e]
    exact this
  have h2 : ∀ N, ∑ n ∈ Finset.range N, (l : ℤ_[l]) ^ n * dTwo χ (u n) p
      = c p - (l : ℤ_[l]) ^ N * (s N).1 p := by
    intro N
    induction N with
    | zero => simp [s]
    | succ N ih => rw [Finset.sum_range_succ, ih, hs N p]; ring
  have h3 := h1.tendsto_sum_nat
  simp only [h2] at h3
  have h4 := (tendsto_const_nhds (x := c p)).sub (hsum fun n => (s n).1 p).tendsto_atTop_zero
  rw [sub_zero] at h4
  exact tendsto_nhds_unique h4 h3

theorem twoCocycle_lift : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  intro l _ Γ _ _ _ ρ hρ ρ1 h1 H3 r ρr hr y hy
  set χ : Γ → ℤ_[l] := fun g => ρ g 1 with hχdef
  have hρχ : ∀ g x, ρ g x = χ g * x := by
    intro g x
    have := map_smul (ρ g) x 1
    rw [smul_eq_mul, mul_one, smul_eq_mul] at this
    rw [this, mul_comm]
  have hχm : ∀ g h, χ (g * h) = χ g * χ h := by
    intro g h
    rw [← hρχ]
    simp only [hχdef, map_mul, Module.End.mul_apply]
  have hχc : Continuous χ := hρ.comp (continuous_id.prodMk continuous_const)
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p := by
    intro c hc hz
    obtain ⟨v, hv, hvc⟩ := H3 (fun p => PadicInt.toZModPow 1 (c p))
      ((continuous_toZModPow 1).comp hc) (by
        intro g h k m
        have := congrArg (PadicInt.toZModPow 1) (hz g h k m)
        rw [← hρχ] at this
        simpa only [map_add (f := _), map_sub, h1, map_zero] using this)
    obtain ⟨u, hu, huv⟩ := exists_continuous_lift 1 v hv
    obtain ⟨c', hc', e⟩ := exists_continuous_div (fun p => c p - dTwo χ u p)
      (hc.sub (continuous_dTwo hχc hu)) l hl0 (by
        rintro ⟨g, h, k⟩
        rw [← pow_one (l : ℤ_[l]), ← toZModPow_eq_zero_iff]
        simp only [dTwo, ← hρχ, map_add (f := _), map_sub, h1, huv, hvc, sub_self])
    exact ⟨u, c', hu, hc', (hz.sub (isCocycleThree_dTwo χ hχm u)).cancel hl0 e,
      fun p => by linear_combination e p⟩
  obtain ⟨Y, hY, hYy⟩ := exists_continuous_lift r y hy.1
  obtain ⟨c, hc, e⟩ := exists_continuous_div (dTwo χ Y) (continuous_dTwo hχc hY)
    ((l : ℤ_[l]) ^ r) (pow_ne_zero _ hl0) (by
      rintro ⟨g, h, k⟩
      rw [← toZModPow_eq_zero_iff]
      simp only [dTwo, ← hρχ, map_add (f := _), map_sub, hr, hYy]
      exact hy.2 g h k)
  obtain ⟨u, hu, hcu⟩ := exists_dTwo_eq χ step c hc
    ((isCocycleThree_dTwo χ hχm Y).cancel (pow_ne_zero _ hl0) e)
  refine ⟨fun p => Y p - (l : ℤ_[l]) ^ r * u p,
    ⟨hY.sub (continuous_const.mul hu), fun g h k => ?_⟩, fun p => ?_⟩
  · have e1 := e (g, h, k)
    rw [hcu] at e1
    simp only [dTwo] at e1
    rw [hρχ]
    linear_combination e1
  · rw [map_sub, hYy, (toZModPow_eq_zero_iff r _).2 (dvd_mul_right _ _), sub_zero]

end GlobalTheory.PadicCocycleLift
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  first | exact @GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | exact GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | (intros; apply GlobalTheory.FN.exists_ringEquiv_extend_of_embedding <;> assumption)
end

section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr : ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  first | exact @GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | exact GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | (intros; apply GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace : ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (W₁ W₂ : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W₁ ↔ algebraMap F L a ∈ W₂) → ∃ σ : L ≃ₐ[F] L, ∀ x : L, σ x ∈ W₂ ↔ x ∈ W₁ := by
  first | exact @GlobalTheory.KZ.ES.exists_conj_of_same_trace | exact GlobalTheory.KZ.ES.exists_conj_of_same_trace | (intros; apply GlobalTheory.KZ.ES.exists_conj_of_same_trace <;> assumption)
end
