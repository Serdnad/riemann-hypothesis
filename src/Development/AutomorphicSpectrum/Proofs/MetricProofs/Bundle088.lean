module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle001
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.exists_family_in_ideal_of_isOFamily : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (r : ℕ) (v : Fin r → Fin g → ℂ), I ≤ W → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) → IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) v → ∃ y : Fin r → W, (∀ a, (y a : Λ) ∈ I) ∧ (∀ a, per (y a) = v a) ∧ LinearIndependent (𝓞 E) (fun a => (y a : Λ)) ∧ (oSpan ρ v).relIndex (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) = (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep

theorem eq_zero_of_sum_mem_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V),
    IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) →
    LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) →
    ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  intro E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl
  obtain ⟨c, hc⟩ := EigCoef.eigComp_eq_combination E s₀
  obtain ⟨h1, h2, h3⟩ := hc V ρ
  let π : V →ₗ[ℂ] V := ∑ a ∈ c.support, c a • ρ a
  have hπ : ∀ x, π x = eigComp ρ s₀ x := by
    intro x
    rw [h1 x]
    simp [π, LinearMap.sum_apply]
  have hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x := by
    intro b x
    have e : π (ρ b x) = ρ b (π x) := by

      simp only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      exact LinearMap.congr_fun this x
    rw [e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))
  have hO : ∀ y ∈ oSpan ρ v, π y ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, i, rfl⟩ := hy
      rw [hact, hπ]
      exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact W.neg_mem hx
  have hI : ∀ x ∈ I₀, π x ∈ W := by
    intro x hx
    obtain ⟨_, _, hN⟩ := hF
    have hm := hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at hm
    have hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (W.smul_mem_iff hN').1 hm
  have hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π := Submodule.span_le.2 hI
  have hxe : ∑ c, l c • q c ∈ eigSp ρ s₀ := Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)
  have hW : ∑ c, l c • q c ∈ W := by
    have h := hS hl
    rw [Submodule.mem_comap, hπ, h3 _ hxe] at h
    exact h
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hW
  have hz := Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hm]
    simp)
  funext j
  have := hz (Fin.natAdd r j)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.generic_flag_elementary_twist : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω) (A : Subring Ω) (val : A →+* ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (τ : Ψ) (ca cb : Fin N), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → (∀ τ, IsBlockDiag j (h τ)) → ∃ (L R : Type) (_ : Field L) (_ : CommRing R) (φ : Φ →+* L) (θ : RatFunc Φ →+* L) (U : Ψ → Matrix (Fin N) (Fin N) L) (s : L) (i : R →+* L) (ρ : R →+* ℂ) (cA : A →+* R) (B : Ψ → Matrix (Fin N) (Fin N) R) (sR : R), Function.Injective i ∧ (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = φ a) ∧ (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) ∧ U τ ca ca + s * U τ ca cb ≠ 0 ∧ θ RatFunc.X * (U τ ca ca + s * U τ ca cb) = s * U τ cb cb ∧ (∀ a : A, i (cA a) = φ (algebraMap Ω Φ a)) ∧ (∀ a, ρ (cA a) = val a) ∧ (∀ τ', IsBlockDiag j (B τ')) ∧ (∀ τ', (B τ').map i = ((T τ')⁻¹.map (φ.comp (algebraMap Ω Φ))) * ((g τ').map φ * U τ')) ∧ (∀ τ', (B τ').map ρ = h τ') ∧ i sR = s ∧ ρ sR = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data | exact GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.gram_det_im_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (R.gram u).det.im = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.gram_det_mul_normSq_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.nz_eq_nzOf_and_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | exact GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseForm

variable {K : Type} {ι : K → Type}

def incl (S : K → Prop) : (Σ k : {k // S k}, ι k.1) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩

theorem incl_injective (S : K → Prop) : Function.Injective (incl (ι := ι) S) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [incl, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl

theorem isMultiHomog_rename_incl [Fintype K] [∀ k, Fintype (ι k)] (S : K → Prop)
    {D : MRing (fun k : {k // S k} => ι k.1)} {a : {k // S k} → ℕ} (hD : IsMultiHomog D a) :
    IsMultiHomog (rename (incl (ι := ι) S) D : MRing ι) (Function.extend Subtype.val a 0) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_rename_of_injective (incl_injective S), Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  by_cases hk : S k
  · have he : Function.extend Subtype.val a 0 k = a ⟨k, hk⟩ := Subtype.val_injective.extend_apply a 0 ⟨k, hk⟩
    rw [he, ← hD m₀ hm₀ ⟨k, hk⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (incl_injective S) m₀ ⟨⟨k, hk⟩, i⟩
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨c, rfl⟩; exact hk c.2), Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact hk ((Sigma.mk.inj_iff.mp hq).1 ▸ q.1.2)

theorem mConeMap_rename_incl {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) (D : MRing (fun k : {k // S k} => ι k.1)) :
    mConeMap y (rename (incl (ι := ι) S) D) =
      map (algebraMap Ω Φ) (rename Subtype.val (mConeMap x D)) := by
  induction D using MvPolynomial.induction_on with
  | C r => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, map_C, map_X, hy] <;> rfl

theorem rename_incl_notMem {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) {D : MRing (fun k : {k // S k} => ι k.1)}
    (hD : D ∉ mCoordIdeal x) : (rename (incl (ι := ι) S) D : MRing ι) ∉ mCoordIdeal y := by
  intro hmem
  apply hD
  have e : mConeMap y (rename (incl (ι := ι) S) D) = 0 := hmem
  rw [mConeMap_rename_incl S x y hy D] at e
  have e2 : rename Subtype.val (mConeMap x D) = 0 :=
    MvPolynomial.map_injective _ (algebraMap Ω Φ).injective (e.trans (map_zero _).symm)
  show mConeMap x D = 0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (e2.trans (map_zero _).symm)

theorem exists_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a → D ∉ mCoordIdeal M.x → ∃ (G : MRing ι) (a' : K → ℕ), IsMultiHomog G a' ∧ G ∉ mCoordIdeal y ∧ ∀ w : (Σ k, ι k) → ℂ, eval w (map (Int.castRingHom ℂ) G) = eval (basePart M.blk w) (map (Int.castRingHom ℂ) D) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ D a hD hDx
  refine ⟨rename (incl (ι := ι) fun k => ∀ p, M.blk p ≠ some k) D, Function.extend Subtype.val a 0,
    isMultiHomog_rename_incl _ hD, rename_incl_notMem _ M.x y (fun q => M.y_base q) hDx, fun w => ?_⟩
  rw [map_rename, eval_rename]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.BaseForm
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (q : Σ k, ι k) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I, valAt M.x (F.u q I) b * minorIJ h I (stepCols N j i)

def stepCoord {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    (p : Ψ × Fin N) (k' : K') (q : Σ k, ι k) : ℂ :=
  ∑ I, valAt M.x (F.u q I) (basePart M'.blk z ∘ Cv.v) *
    ∑ I', if IsStepRows N j p.2 I' then minorIJ (Cv.trans F' F (basePart M'.blk z) p.1) I I' *
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ else 0

def img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then basePart M'.blk z (Cv.v ⟨⟨q.1, hk⟩, q.2⟩)
  else
    have hp : ∃ p, M.blk p = some q.1 := by simpa using hk
    match M'.blk hp.choose with
    | none => 0
    | some k' => stepCoord Cv F' F z hp.choose k' q

theorem img_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    basePart M.blk (img Cv F' F z) = basePart M'.blk z ∘ Cv.v := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  simp only [basePart, img, Function.comp]
  rw [dite_eq_left hk]

theorem img_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    {p : Ψ × Fin N} {k : K} {k' : K'} (hp : M.blk p = some k) (hp' : M'.blk p = some k') (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = stepCoord Cv F' F z p k' ⟨k, m⟩ := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h => h p hp
  have hex : ∃ p', M.blk p' = some k := ⟨p, hp⟩
  have hch : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
  simp only [img, dif_neg hk]
  split
  · next h =>
    rw [hch, hp'] at h
    exact absurd h (by simp)
  · next k'' h =>
    rw [hch, hp'] at h
    cases h
    rw [hch]

theorem exists_blk_cover {M : FlagModel y Ψ N j} (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : ∃ k', M'.blk p = some k' := by
  have h1 : ¬ (M.blk p = none) := by
    rw [hp]
    simp
  rw [M.blk_none] at h1
  have h2 : M'.blk p ≠ none := by
    rw [Ne, M'.blk_none]
    exact h1
  exact Option.ne_none_iff_exists'.mp h2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem trans_blockDiag_det : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal b) → M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ τ, IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F' F hb hF' hF hG' hG τ
  have hT := hF.1 τ
  have hT' := hF'.1 τ
  have hdet : ((F.T τ).map Cv.φ).det ≠ 0 := by
    have e : ((F.T τ).map Cv.φ).det = Cv.φ (F.T τ).det := by
      rw [RingHom.map_det]; rfl
    rw [e]
    exact (map_ne_zero Cv.φ).2 hT.2
  have hu : IsUnit ((F.T τ).map Cv.φ).det := isUnit_iff_ne_zero.2 hdet
  have hu' : IsUnit (F'.T τ).det := isUnit_iff_ne_zero.2 hT'.2
  have hA : IsBlockDiag j (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) :=
    ((hT.1.map Cv.φ).inv hu).mul hT'.1
  have hreg := Cv.agree b hb F' F hF' hF hG' hG τ
  have hz : valMat M'.x b (1 : Matrix (Fin N) (Fin N) M'.Ω) = 1 := by
    have hring := ValRing.regAt_valAt_ring _ _ _ M'.x b hb
    ext a c
    by_cases e : a = c
    · subst e
      show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a a) b = _
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact hring.2.2.2.1
    · show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a c) b = _
      rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e]
      exact hring.2.2.1
  have hAB : (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) * ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]
  have hmul := (regMat_mul hb (fun a c => (hreg a c).1) (fun a c => (hreg a c).2)).2
  rw [hAB, hz] at hmul
  have htr : Cv.trans F' F b τ = valMat M'.x b (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) := rfl
  refine ⟨fun a c h => ?_, ?_⟩
  · show valAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a c) b = 0
    rw [hA a c h]
    exact (ValRing.regAt_valAt_ring _ _ _ M'.x b hb).2.2.1
  · rw [htr]
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end
