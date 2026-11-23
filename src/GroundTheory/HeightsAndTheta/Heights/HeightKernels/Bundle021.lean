module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle018
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain

noncomputable section

namespace CurveAffineCharts

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem exists_chart (hy : IsArithVar (mCoordIdeal y) 1) : ∃ t : T, y ⟨(), t⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := hy.2.1.2.2 ()
  refine ⟨t, fun h0 => ht ?_⟩
  simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]


omit [Fintype T] in
theorem mem_integer_of_mem_chartRingZ [NumberField K'] (v : HeightOneSpectrum (𝓞 K')) (t : T)
    (ht : ∀ u, v.valuation K' (y ⟨(), u⟩) ≤ v.valuation K' (y ⟨(), t⟩)) {b : K'}
    (hb : b ∈ chartRingZ y (fun _ => t)) : b ∈ (v.valuation K').integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation K' (y ⟨(), t⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (ht u)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem mem_integralClosure_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' b hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _))
    (mem_curveRing.mp hb (fun _ => t) (fun _ => hyt))

theorem finite [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) : Module.Finite ℤ (curveRing y) := by
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ K' :=
    { toFun := fun b => ⟨b, mem_integralClosure_of_mem_curveRing y hy b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg (fun z : integralClosure ℤ K' => (z : K')) h)

theorem mem_blockFnField_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ blockFnField y := by
  obtain ⟨t, ht⟩ := exists_chart y hy
  have hbt := mem_curveRing.mp hb (fun _ => t) (fun _ => ht)
  clear hb
  induction hbt using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_nat_mul_mem_adjoin [CharZero K'] {S : Set K'} {x : K'} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ?_⟩
    have hq : (q.den : K') * algebraMap ℚ K' q = (q.num : K') := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [hq]
    exact intCast_mem _ _
  | add x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x + z) = (m : K') * ((n : K') * x) + (n : K') * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ m) hnx) (mul_mem (natCast_mem _ n) hmz)
  | mul x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x * z) = ((n : K') * x) * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem hnx hmz


omit [Fintype T] in
theorem mem_adjoin_of_mem_blockFnField [NumberField K'] (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ blockFnField y) :
    x ∈ Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
  have hle : blockFnField y ≤
      IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, -, rfl⟩
    have hp : y p / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    rw [← div_div_div_cancel_right₀ ht]
    exact div_mem hp hq
  exact hle hx

theorem exists_nat_mul_mem_curveRing [NumberField K'] {x : K'} (hx : x ∈ blockFnField y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ curveRing y := by
  classical
  have key : ∀ t : T, ∃ n : ℕ, n ≠ 0 ∧ (y ⟨(), t⟩ ≠ 0 → (n : K') * x ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, one_ne_zero, fun h => (h ht).elim⟩
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin (mem_adjoin_of_mem_blockFnField y t ht hx)
      exact ⟨n, hn, fun _ => h⟩
  choose N hN0 hN using key
  refine ⟨∏ t, N t, Finset.prod_ne_zero_iff.mpr (fun t _ => hN0 t), ?_⟩
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := hN (c ()) (hc ())
  rw [← hc'] at h1
  have e : ((∏ t, N t : ℕ) : K') * x =
      ((∏ t ∈ Finset.univ.erase (c ()), N t : ℕ) : K') * ((N (c ()) : K') * x) := by
    rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ (c ()))]
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ _) h1

theorem finrank_eq [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) :
    Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) := by
  have := finite y hy
  let b := Module.finBasis ℤ (curveRing y)
  let ι : curveRing y →ₗ[ℤ] K' := (curveRing y).subtype.toAddMonoidHom.toIntLinearMap
  have hliZ : LinearIndependent ℤ (ι ∘ b) :=
    b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (ι ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ (Set.range (ι ∘ b)) =
      Subalgebra.toSubmodule (blockFnField y).toSubalgebra := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_blockFnField_of_mem_curveRing y hy (b i).2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_mul_mem_curveRing y hx
      have h1 : (⟨_, hnx⟩ : curveRing y) ∈ Submodule.span ℤ (Set.range b) := by
        rw [b.span_eq]; trivial
      have h2 : (n : K') * x ∈ Submodule.span ℤ (Set.range (ι ∘ b)) := by
        rw [Set.range_comp, ← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have h3 : (n : K') * x ∈ Submodule.span ℚ (Set.range (ι ∘ b)) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ h2
      have h4 : x = (n : ℚ)⁻¹ • ((n : K') * x) := by
        rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
      rw [h4]
      exact Submodule.smul_mem _ _ h3
  rw [← IntermediateField.finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule, ← hspan,
    finrank_span_eq_card hliQ, Fintype.card_fin]

end CurveAffineCharts

theorem CurveCharts.proof (hc : ClosedPointChart.Statement) : CurveCharts.Statement :=
  fun T _ K' _ _ y hy =>
    ⟨CurveAffineCharts.finite y hy, CurveAffineCharts.finrank_eq y hy, hc T K' y hy⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

instance isPrime_map_C_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).2 inferInstance

abbrev nagataRing (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R))

def VertPointNagata.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : T → curveRing y)
          (hb : ∀ u, b u ∉ curvePtIdeal y W), (∀ u, (b u : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a u) →
          ∃ Φ : Localization.AtPrime W →+* nagataRing (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing (fun _ : Unit => T)) _) ∧
            ∀ f : MRing (fun _ : Unit => T), Φ (algebraMap _ _ f) =
              algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p.2)
                  (⟨b p.2, hb p.2⟩ : (curvePtIdeal y W).primeCompl)) * Polynomial.X) f)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

def VertPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ u : T, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) ∧
        ∀ (d : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => d) →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : K') * aeval y g = a * y ⟨(), t⟩ ^ d)

def VertPointInj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def VertPointSurj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal → locLen m (sectionQuot y (aeval y s)) ≠ 0 →
        ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def VertPointMultChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def SectionQuotLocal.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (t : T), m.IsPrime →
        (∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          locLen m (sectionQuot y (aeval y s)) = locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace TelescopingSum

theorem comp_swap {α : Type*} (D k : ℕ) (hk : k < D + 1) (X Y : α) (m : ℕ) (hm : m = k ∨ m = k + 1) :
    (fun j : Fin (D + 1) => if (j : ℕ) < m then X else Y) ∘ Equiv.swap ⟨k, hk⟩ (Fin.last D) =
      Fin.snoc (fun j : Fin D => if (j : ℕ) < k then X else Y) (if k < m then X else Y) := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Equiv.swap_apply_right]
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    by_cases h : (j' : ℕ) = k
    · have hj : Fin.castSucc j' = ⟨k, hk⟩ := Fin.ext (by simp [h])
      rw [hj, Equiv.swap_apply_left]
      have := j'.isLt
      simp only [Fin.val_last]
      rw [if_neg (by omega), if_neg (by omega)]
    · have h1 : Fin.castSucc j' ≠ ⟨k, hk⟩ := fun e => h (by simpa using congrArg Fin.val e)
      have h2 : Fin.castSucc j' ≠ Fin.last D := Fin.castSucc_ne_last j'
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [Fin.val_castSucc]
      rcases hm with rfl | rfl
      · rfl
      · by_cases h3 : (j' : ℕ) < k
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]

end TelescopingSum

theorem Telescope.proof : TelescopeStatement := by
  intro K _ ι _ I hI P D A u hu hP hA hus
  set W := HermLine.ofWeight u hu with hWdef
  have hW : IsSmoothHerm W := by
    have : W.h = fun z => Real.exp (-u z) := rfl
    unfold IsSmoothHerm
    rw [this]
    exact Real.contDiff_exp.comp_contDiffOn hus.neg
  have hA' : IsSmoothHerm (A.tensor W) := by
    unfold IsSmoothHerm at hA hW ⊢
    exact hA.mul hW
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ m, T m =
      I P (D + 1) (fun j : Fin (D + 1) => if (j : ℕ) < m then A.tensor W else A) := ⟨_, fun _ => rfl⟩
  have hsm : ∀ (m : ℕ) (j : Fin (D + 1)), IsSmoothHerm (if (j : ℕ) < m then A.tensor W else A) :=
    fun m j => by split_ifs <;> assumption
  have hstep : ∀ k ∈ Finset.range (D + 1), T (k + 1) - T k =
      -ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) u := by
    intro k hk
    have hk' : k < D + 1 := Finset.mem_range.mp hk
    have hL : ∀ j : Fin D, IsSmoothHerm (if (j : ℕ) < k then A.tensor W else A) :=
      fun j => by split_ifs <;> assumption
    have e1 : T (k + 1) = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) (A.tensor W)) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm (k + 1)),
        TelescopingSum.comp_swap D k hk' _ _ (k + 1) (Or.inr rfl), if_pos (Nat.lt_succ_self k)]
    have e0 : T k = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) A) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm k),
        TelescopingSum.comp_swap D k hk' _ _ k (Or.inl rfl), if_neg (lt_irrefl k)]
    have hmc := metricChange K ι I hI P D (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A)
      A u hu hP hL hA hus
    rw [e1, e0, hmc]
    ring
  have h0 : T 0 = I P (D + 1) (fun _ => A) := by
    rw [hT]
    simp
  have hD : T (D + 1) = I P (D + 1) (fun _ => A.tensor W) := by
    rw [hT]
    congr 1
    funext j
    rw [if_pos j.isLt]
  rw [← h0, ← hD, ← Finset.sum_range_sub, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hstep

end GroundTheory.Heights₂.Heights
end
end
