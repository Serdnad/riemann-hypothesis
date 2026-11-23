module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.norm_charpoly_separable_of_elliptic : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  first | exact @GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | exact GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | (intros; apply GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.section_meets_above_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | exact GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | (intros; apply GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistOrbit

theorem finite_of_subset_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj' (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL' (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper' (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL' hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := GlobalTheory.NormOneProper.main E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj' hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem continuous_thPair (hU : Unr E) (a b : ℕ) (w : Pl E) :
    Continuous ((thL a w).prodMap (thL b w)) := by
  have h1 := (GlobalTheory.BCT.thL_continuous_involutive E hU a w).1
  have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU b w).1
  exact (h1.comp continuous_fst).prodMk (h2.comp continuous_snd)

theorem isOpen_isCompact_pair_integral_points (a b : ℕ) (w : Pl E) :
    IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  obtain ⟨o₁, c₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨o₂, c₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [K2, Subgroup.coe_prod]
  exact ⟨o₁.prod o₂, c₁.prod c₂⟩

theorem proper_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ x : GLw a w × GLw b w,
      x⁻¹ * y * ((thL a w).prodMap (thL b w)) x ∈ C →
        ∃ t ∈ twCent ((thL a w).prodMap (thL b w)) y, ∃ d ∈ D, x = t * d := by
  obtain ⟨D₁, hD₁, p₁⟩ := proper' hU a w y.1 h₁ _ (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, p₂⟩ := proper' hU b w y.2 h₂ _ (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, e₁⟩ := p₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, e₂⟩ := p₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext ht₁ ht₂

theorem finite_doubleCosets (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (K2 a b w : Set (GLw a w × GLw b w)) |
      ∃ k ∈ K2 a b w, (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite := by
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  obtain ⟨D, hD, hp⟩ := proper_pair hU a b w y h₁ h₂ C hC
  have hD' : IsCompact ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) ''
      (D ×ˢ (K2 a b w : Set (GLw a w × GLw b w)))) :=
    (hD.prod hKc).image (continuous_fst.mul continuous_snd.inv)
  refine finite_of_subset_mul' _ (K2 a b w) hKo _ hD'
    (fun x => ∃ k ∈ K2 a b w, (x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k) ∈ C) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, d, hd, e⟩ := hp _ hx
  refine ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

theorem rStab_index_ne_zero (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ) (ho : IsOpen (K' : Set (GLw a w × GLw b w)))
    (hf : IsHecke K' f) (x : K2 a b w) :
    (rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      ((thL a w).prodMap (thL b w)) ((x : GLw a w × GLw b w) * k))).index ≠ 0 := by
  obtain ⟨-, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  have hθ := continuous_thPair hU a b w
  set θ := (thL a w).prodMap (thL b w) with hθdef
  set W : Subgroup (GLw a w × GLw b w) := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set (GLw a w × GLw b w)) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf (K2 a b w)).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf (K2 a b w) ≤ rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      θ ((x : GLw a w × GLw b w) * k)) := by
    intro k' hk' k
    have hk'W : (k' : GLw a w × GLw b w) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : GLw a w × GLw b w)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : GLw a w × GLw b w) ∈ K' := hk'W.2
    have e : (((x * (k * k') : K2 a b w) : GLw a w × GLw b w)⁻¹ * y * θ ((x : GLw a w × GLw b w) * (k * k' : K2 a b w))) =
        (k' : GLw a w × GLw b w)⁻¹ * ((((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
          θ ((x : GLw a w × GLw b w) * k)) * θ (k' : GLw a w × GLw b w)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf.2 _ hl _).1, (hf.2 _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem locSupp : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact ⟨fun C hC => finite_doubleCosets hU a b w y h₁ h₂ C hC,
    fun K' f ho _ hf x => rStab_index_ne_zero hU a b w y K' f ho hf x⟩

end GlobalTheory.CompanionTheory.TwistOrbit

end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.EllLoc

theorem map_csr_left {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    (C (c (P.coeff 0)) * P).map φ = C (c' ((P.map φ).coeff 0)) * P.map φ := by
  rw [Polynomial.map_mul, Polynomial.map_C, h, Polynomial.coeff_map]

theorem map_csr_right {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    ((P.map c).reverse).map φ = ((P.map φ).map c').reverse := by
  have hcomp : φ.comp c = c'.comp φ := RingHom.ext h
  have hd : (P.map c).natDegree = ((P.map φ).map c').natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, Polynomial.natDegree_map]
  rw [Polynomial.reverse, Polynomial.reverse, ← hd, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map]

theorem csr_linear (a : ℂ) (ha : ‖a‖ = 1) :
    C (starRingEnd ℂ ((X - C a : ℂ[X]).coeff 0)) * (X - C a) = ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse := by
  have hmul : starRingEnd ℂ a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.reverse, Polynomial.natDegree_X_sub_C,
    Polynomial.reflect_sub, Polynomial.reflect_C]
  have hX : reflect 1 (X : ℂ[X]) = 1 := by
    simpa [revAt] using Polynomial.reflect_monomial (R := ℂ) 1 1
  rw [hX]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, C_neg, pow_one]
  have : (C (starRingEnd ℂ a) * C a : ℂ[X]) = 1 := by rw [← C_mul, hmul, C_1]
  linear_combination this

theorem csr_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    C (starRingEnd ℂ ((s.map fun a => (X - C a : ℂ[X])).prod.coeff 0)) * (s.map fun a => (X - C a : ℂ[X])).prod =
      ((s.map fun a => (X - C a : ℂ[X])).prod.map (starRingEnd ℂ)).reverse := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
    have h1 := csr_linear a (hs a (Multiset.mem_cons_self a s))
    have h2 := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h1, ← h2,
      Polynomial.mul_coeff_zero, map_mul, C_mul]
    ring

theorem csr_global {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  have hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQ : (P.map τ).Monic := hP.1.map τ
  have hroots : (P.map τ) = ((P.map τ).roots.map fun a => (X - C a : ℂ[X])).prod :=
    (IsAlgClosed.splits (P.map τ)).eq_prod_roots_of_monic hQ
  have key := csr_prod (P.map τ).roots (hP.2.2.2 τ)
  rw [← hroots] at key
  apply Polynomial.map_injective τ τ.injective
  have e1 := map_csr_left τ σ (starRingEnd ℂ) hτ P
  have e2 := map_csr_right τ σ (starRingEnd ℂ) hτ P
  rw [e2, ← key, ← e1]
  rfl

theorem csr_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) :
    IsCsr w (atPl w P) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hc : ∀ x, algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) =
      cj w (algebraMap E (w.adicCompletion E) x) := fun x => (GlobalTheory.BCT.LocVal.cj_algebraMap w hs x).symm
  have e1 := map_csr_left (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  have e2 := map_csr_right (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  rw [atPl, ← e1, ← e2, ← csr_global hP]
  rfl

theorem ellLocal : EllLocal := by
  intro E _ _ _ a b p₁ p₂ h₁ h₂ hc w
  have hm₁ : (atPl w p₁).Monic := h₁.1.map _
  have hm₂ : (atPl w p₂).Monic := h₂.1.map _
  refine ⟨hm₁, hm₂, ?_, ?_, ?_, csr_at h₁ w, csr_at h₂ w⟩
  · rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  · rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  · have hs : (p₁ * p₂).Separable := h₁.2.2.1.mul h₂.2.2.1 hc
    have := hs.map (f := algebraMap E (w.adicCompletion E))
    rwa [Polynomial.map_mul] at this

end GlobalTheory.CompanionTheory.EllLoc

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm


theorem _root_.GlobalTheory.T.hasDerivAt_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | exact GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | (intros; apply GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

namespace GlobalTheory.CompanionTheory.AdjointPoly

theorem cT_aeval_mul_eq :
    ∀ (K : Type) [Field K] (s : K →+* K) (n : ℕ) (A H₀ : Matrix (Fin n) (Fin n) K) (a : K[X]),
      cT s A * H₀ * A = H₀ → aeval A a * A = 1 →
      ∀ f : K[X], cT s (aeval A f) * H₀ = H₀ * aeval A ((f.map s).comp a) := by
  intro K _ s n A H₀ a hA ha f
  have hcomm : A * aeval A a = aeval A a * A := by
    have h : aeval A (X * a) = aeval A (a * X) := by rw [mul_comm]
    simpa only [map_mul, aeval_X] using h
  have hAB : A * aeval A a = 1 := hcomm.trans ha
  have hstep : cT s A * H₀ = H₀ * aeval A a := by
    calc cT s A * H₀ = cT s A * H₀ * (A * aeval A a) := by rw [hAB, mul_one]
      _ = (cT s A * H₀ * A) * aeval A a := by simp only [mul_assoc]
      _ = H₀ * aeval A a := by rw [hA]
  have cT_mul : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P * Q) = cT s Q * cT s P := by
    intro P Q
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_add : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P + Q) = cT s P + cT s Q := by
    intro P Q
    ext i j
    simp [cT]
  have cT_C : ∀ c : K, cT s (algebraMap K (Matrix (Fin n) (Fin n) K) c)
      = algebraMap K (Matrix (Fin n) (Fin n) K) (s c) := by
    intro c
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  induction f using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Polynomial.map_C, Polynomial.C_comp]
    rw [cT_C, Algebra.commutes]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), Polynomial.add_comp, cT_add, add_mul, mul_add, hp, hq]
  | monomial k c ih =>
    have e1 : aeval A (C c * X ^ (k + 1)) = A * aeval A (C c * X ^ k) := by
      have h : aeval A (C c * X ^ (k + 1)) = aeval A (X * (C c * X ^ k)) := by
        congr 1; ring
      rw [h, map_mul, aeval_X]
    have e2 : ((C c * X ^ (k + 1) : K[X]).map s).comp a
        = ((C c * X ^ k : K[X]).map s).comp a * a := by
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, pow_succ]
      ring
    rw [e1, e2, cT_mul, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc,
      map_mul (aeval A) (((C c * X ^ k : K[X]).map s).comp a) a]

end GlobalTheory.CompanionTheory.AdjointPoly
end
