module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.DiagonalDivisors.InhabitBaseStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalDivisor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]


open Classical in
theorem divCycle_eq_ite {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dite_eq_left hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1

end DiagonalDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem mCoordIdeal_eq_ker_multiConeMap {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) : mCoordIdeal c = RingHom.ker (T.multiConeMap c) := by
  have h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap])
      (fun p => by simp [T.multiConeMap, mConeMap])
  rw [mCoordIdeal, ← h]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def ChartRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k),
    (∀ k, z ⟨k, j k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) →
      ptDeg (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def LineFibreBlocks.Statement : Prop :=
  ∀ (F : Type) [Field F] (K₀ : Type) [Fintype K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)] (k₀ : K₀)
    (Q : Ideal (MRingOver F ι₀)) (J : IFamily F ι₀),
    (∀ k, k = k₀) → IsProjVarF Q 1 →
    (∃ S : Set (MRingOver F ι₀), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ Q = Ideal.span S) →
    IsFieldIntersection J → ∀ m : K₀ → ℤ, J Q 1 ![m] = m k₀

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def FnDegAdjoin.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (x' : (Σ k', ι' k') → Ω) (i' : ∀ k', ι' k'),
    (∀ k', x' ⟨k', i' k'⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) →
      letI := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
      fnDeg v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
        Module.finrank (Algebra.adjoin F (Set.range ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v)))
          (Algebra.adjoin F (Set.range fun q => x' q / x' ⟨q.1, i' q.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z

theorem logNorm_eq_log_secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := rfl

theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl

def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])

variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem regLine_a : (regLine E t ht ε).a = 0 := rfl

theorem regLine_h (z : (Σ k, ι k) → ℂ) :
    (regLine E t ht ε).h z = Real.exp (Real.log (secNorm E t z ^ 2 + ε) / 2) := by
  simp [regLine, HermLine.ofWeight]

theorem log_regLine_h (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]

theorem contDiff_eval_map (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ (fun _ => ℂ) v)

theorem isSmoothHerm_regLine (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by
  unfold IsSmoothHerm
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_eval_map t)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2 / E.h z ^ 2 + ε)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hn.contDiffOn.div (hE.pow 2) fun z hz => pow_ne_zero _ (E.pos z hz).ne').add contDiffOn_const
  have hl := (hq.log fun z hz => (add_pos_of_nonneg_of_pos
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) hε).ne').div_const 2
  refine (Real.contDiff_exp.comp_contDiffOn hl).congr fun z _ => ?_
  rw [regLine_h, secNorm, div_pow]
  rfl

theorem logNorm_le_log_regLine_h (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

end Objects

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrder

section Orders

variable {K : Type} {ι : K → Type}

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem multAt_sup_span_eq {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW, ← hlen (s := g) hu, heq, hlen hv]

end Orders

section Diagonal

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]



end Diagonal

end DiagonalOrder


end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsAddFirst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (M N E : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm E → IsSectionOn Q E t →
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (logNorm E t) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (logNorm E t) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (logNorm E t)

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

end GroundTheory.Heights₂.Heights.Inter
end
end
