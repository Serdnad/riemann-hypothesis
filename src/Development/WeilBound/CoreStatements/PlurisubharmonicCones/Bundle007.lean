module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

section

noncomputable section

namespace LevelTowerAlt.Comparison₂

open MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot

theorem one_coord₂ (hBr : ResBridgeStatement) (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hIso : IsLineIso P A.a B.a f g) (hw : IsDefectOn P (mcPts P) f g A B w) :
    I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) =
      -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  obtain ⟨⟨α, γ, hfα, hgγ, hdeg⟩, hU⟩ := hIso
  have hfP : f ∉ P := hU.1
  have hgP : g ∉ P := hU.2.1
  set M' : HermLine ι := fsOfDeg γ with hM'def
  set M : HermLine ι := twist M' A B with hMdef
  have hM' : IsSmoothHerm M' := isSmoothHerm_fsOfDeg γ
  have hM : IsSmoothHerm M := isSmoothHerm_twist hM' hA hB
  have hMa : ∀ k, M.a k = α k := by
    intro k
    have h := hdeg k
    have e1 : M.a k = (γ k : ℤ) + A.a k + -B.a k := rfl
    rw [e1]
    linarith
  have hM'a : ∀ k, M'.a k = γ k := fun _ => rfl

  have a1 := hI.2.1 P e L M B hP hL hM hB
  have a2 := hI.2.1 P e L M' A hP hL hM' hA
  have ht : M.tensor B = M'.tensor A := twist_tensor (fun z hz => fsOfDeg_h_of_notMem γ hz) A B
  rw [ht] at a1

  have r1 := hI.2.2 P e L M f α hP hL hM hMa hfα hfP
  have r2 := hI.2.2 P e L M' g γ hP hL hM' hM'a hgγ hgP
  rw [recR_eq] at r1 r2

  have hc := GlobalTheory.T.unit_ratio_same_divisor_multiplicities K ι P f g hU
  have hcyc : cycR I P L f = cycR I P L g := by
    unfold cycR
    refine finsum_mem_congr hc.1 fun W hW => ?_
    rw [hc.2 W (hc.1 ▸ hW)]

  have hsf : IsSectionOn P M f := ⟨α, hMa, hfα, hfP⟩
  have hsg : IsSectionOn P M' g := ⟨γ, hM'a, hgγ, hgP⟩
  rw [arInt_eq_mInt hBr hG R hP hL hM hsf] at r1
  rw [arInt_eq_mInt hBr hG R hP hL hM' hsg] at r2
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => potOf_isPotential R (L i) (hL i)
  have hlin := mIntLinear R.A (fun j => potOf R (L j)) hpot (-1)
    (fun x => logNorm M' g (R.lift x x)) (fun x => logNorm M f (R.lift x x))
    (brIntegrable R L M' g hP hL hM' hsg) (brIntegrable R L M f hP hL hM hsf)
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  have hw' : mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) =
      mInt R.A (fun j => potOf R (L j))
        (fun x => -1 * logNorm M' g (R.lift x x) + logNorm M f (R.lift x x)) := by
    refine mInt_congr_null _ _ fun j => ?_
    refine measure_mono_null ?_ (measure_union_null (zeros_null R Ψ hP hΨ hfα hfP j)
      (zeros_null R Ψ hP hΨ hgγ hgP j))
    rintro y ⟨hyt, hy⟩
    by_contra hcon
    have hnf : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) f ≠ 0 :=
      fun h => hcon (Or.inl ⟨hyt, h⟩)
    have hng : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) g ≠ 0 :=
      fun h => hcon (Or.inr ⟨hyt, h⟩)
    have hmem := R.mem ((R.A.chart j).symm y) _ (R.mem_U ((R.A.chart j).symm y))
    apply hy
    have hd := hw _ hmem g f (by rw [mul_comm, sub_self]; exact P.zero_mem) hng
    have := logNorm_sub_eq (M := M') (A := A) (B := B) (show _ ∈ blockSet ι from hmem.1) hnf hng
    show w _ = -1 * logNorm M' g _ + logNorm M f _
    rw [hd, ← this]
    ring
  rw [hw', hlin]
  linarith

end LevelTowerAlt.Comparison₂
end
end

section

open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mat_unique {b₀ : Fin r → V} (h₀ : LinearIndependent Ω b₀) {T T' : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ k', T k' k • b₀ k' = ∑ k', T' k' k • b₀ k') : T = T' := by
  ext k' k
  exact (Fintype.linearIndependent_iffₛ.1 h₀) (fun a => T a k) (fun a => T' a k) (h k) k'

theorem mat_comp {b₀ b b' : Fin r → V} {T A : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (h' : ∀ k, b' k = ∑ k', A k' k • b k') (k : Fin r) :
    b' k = ∑ k', (T * A) k' k • b₀ k' := by
  rw [h' k]
  simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem exists_mat (R : Subring Ω) {b b' : Fin r → V} (h : ∀ k, b' k ∈ Submodule.span R (Set.range b)) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ k, b' k = ∑ k', A k' k • b k') ∧ A.det ∈ R := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h k)
  refine ⟨R.subtype.mapMatrix (Matrix.of fun k' k => c k k'), fun k => ?_, ?_⟩
  · rw [← hc k]; rfl
  · rw [← RingHom.map_det]; exact SetLike.coe_mem _

theorem det_ne_zero {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') : T.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hT⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hv (funext (Fintype.linearIndependent_iff.1 hb v ?_))
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [← Finset.sum_smul]
  have := congrFun hT k'
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
  rw [show ∑ i, v i * T k' i = 0 from by rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _, zero_smul]

end

end N1

open N1

theorem determinant_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  intro X Ω _ ξ V _ _ L r b₀ b T p h₀ hb hT
  refine ⟨det_ne_zero hb.1 hT, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b', T', hb', hT', rfl⟩
    obtain ⟨A, hA, hd⟩ := exists_mat (regAt ξ p) (b := b) (b' := b') fun k => by
      rw [← hb.2, hb'.2]; exact Submodule.subset_span ⟨k, rfl⟩
    have e : T' = T * A := mat_unique h₀ fun k => by rw [← hT' k, ← mat_comp hT hA k]
    rw [e, Matrix.det_mul, mul_comm]
    exact Submodule.mem_span_singleton.2 ⟨⟨A.det, hd⟩, rfl⟩
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (SncPiece.det_mem_detLat hb hT))

end LevelTowerAlt
end
