module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle053
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle055
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_zero_comp_smul_of_periodic :
    ∀ (n : Type) [Fintype n] (L : AddSubgroup (n → ℝ)) [Countable L] (D : Set (n → ℝ)) (k : (n → ℝ) → ℂ) (q : ℝ), 0 < q → MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → 0 < MeasureTheory.volume D → MeasureTheory.volume D < ⊤ → Continuous k → (∃ C : ℝ, ∀ s, ‖k s‖ ≤ C) → (∀ p ∈ L, ∀ s, k (s + p) = k s) → ∫ s in D, k s = 0 → ∀ (L₁ : AddSubgroup (n → ℝ)) [Countable L₁] (D₁ : Set (n → ℝ)), MeasureTheory.IsAddFundamentalDomain L₁ D₁ MeasureTheory.volume → MeasureTheory.volume D₁ < ⊤ → (∀ p ∈ L₁, ∀ s, k (q • (s + p)) = k (q • s)) → ∫ s in D₁, k (q • s) = 0 := by
  intro n _ L _ D k q hq hD hDpos hDfin hk hb hper h0 L₁ _ D₁ hD₁ hD₁fin hper₁
  have hq0 : q ≠ 0 := hq.ne'
  have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq0
  let φ : (n → ℝ) →+ (n → ℝ) := DistribSMul.toAddMonoidHom (n → ℝ) q⁻¹
  have hφ : Function.Injective φ := fun x y h => by
    simpa [φ, smul_right_inj hqi] using h
  let L' : AddSubgroup (n → ℝ) := L.map φ
  let eL : L ≃+ L' := AddSubgroup.equivMapOfInjective L φ hφ
  haveI : Countable L' := Countable.of_equiv L eL.toEquiv
  let f : (n → ℝ) ≃ (n → ℝ) := (Homeomorph.smulOfNeZero q⁻¹ hqi).toEquiv
  have hf : ∀ x, f x = q⁻¹ • x := fun x => rfl
  have hfs : ∀ x, f.symm x = q • x := fun x => by
    apply f.injective
    rw [Equiv.apply_symm_apply, hf, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hD' : IsAddFundamentalDomain L' (f '' D) volume := by
    refine hD.image_of_equiv f ?_ eL.symm.toEquiv ?_
    · have : (f.symm : (n → ℝ) → (n → ℝ)) = fun x => q • x := funext hfs
      rw [this]
      exact Measure.quasiMeasurePreserving_smul volume hq0
    · intro g x
      show f ((eL.symm g : L) +ᵥ x) = g +ᵥ f x
      have hg : ((g : L') : n → ℝ) = q⁻¹ • ((eL.symm g : L) : n → ℝ) := by
        conv_lhs => rw [← eL.apply_symm_apply g]
        rfl
      rw [AddSubgroup.vadd_def, AddSubgroup.vadd_def, vadd_eq_add, vadd_eq_add, hf, hf, smul_add, hg]
  have himg : f '' D = q⁻¹ • D := by
    ext x; simp [hf, Set.mem_smul_set]
  rw [himg] at hD'
  have hvol : volume (q⁻¹ • D) = ENNReal.ofReal |q⁻¹ ^ Module.finrank ℝ (n → ℝ)| * volume D :=
    Measure.addHaar_smul volume q⁻¹ D
  have hvne0 : volume (q⁻¹ • D) ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero ?_ hDpos.ne'
    simpa using abs_pos.2 (pow_ne_zero (Module.finrank ℝ (n → ℝ)) hqi)
  have hvfin : volume (q⁻¹ • D) < ⊤ := by
    rw [hvol]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin
  have hint0 : ∫ s in q⁻¹ • D, k (q • s) = 0 := by
    rw [Measure.setIntegral_comp_smul_of_pos volume k (q⁻¹ • D) hq, smul_smul,
      mul_inv_cancel₀ hq0, one_smul, h0, smul_zero]
  have hperL' : ∀ p ∈ L', ∀ s, k (q • (s + p)) = k (q • s) := by
    intro p hp s
    obtain ⟨p0, hp0, rfl⟩ := AddSubgroup.mem_map.1 hp
    have : q • (s + φ p0) = q • s + p0 := by
      simp [φ, smul_add, smul_smul, mul_inv_cancel₀ hq0]
    rw [this, hper p0 hp0]
  obtain ⟨C, hC⟩ := hb
  have key := mean_fundamentalDomain_eq_of_periodic n L' L₁ (q⁻¹ • D) D₁ (fun s => k (q • s))
    hD' hD₁ hvfin hD₁fin (hk.comp (continuous_const_smul q)) ⟨C, fun s => hC _⟩ hperL' hper₁
  rw [hint0, mul_zero] at key
  have hre : ((volume (q⁻¹ • D)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hvne0 hvfin.ne).ne'
  exact (mul_eq_zero.1 key).resolve_left hre

end GlobalTheory
end

section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  first | exact @GlobalTheory.cosets_main | exact GlobalTheory.cosets_main | (intros; apply GlobalTheory.cosets_main <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  first | exact @GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | exact GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | (intros; apply GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_rational_orthogonal_projection_semilinear : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  first | exact @GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | exact GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | (intros; apply GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range <;> assumption)
end

section


theorem _root_.GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  first | exact @GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | exact GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | (intros; apply GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end

section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_along_curve_products_stable_alt : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  first | exact @GlobalTheory.smooth_along_curve_products_stable | exact GlobalTheory.smooth_along_curve_products_stable | (intros; apply GlobalTheory.smooth_along_curve_products_stable <;> assumption)
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | exact GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | (intros; apply GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.unitaryGroup_secondKind_coordinates_near_one : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  first | exact @GlobalTheory.UnitaryChart.second_kind_chart | exact GlobalTheory.UnitaryChart.second_kind_chart | (intros; apply GlobalTheory.UnitaryChart.second_kind_chart <;> assumption)
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (h : ℝ → F) (m : ℕ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) → ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  first | exact @GlobalTheory.taylorTail_bound | exact GlobalTheory.taylorTail_bound | (intros; apply GlobalTheory.taylorTail_bound <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' : ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) → ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  first | exact @GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | exact GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | (intros; apply GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.upperTriangular_near_unitDiagonal_of_twistedGram_near : ∀ (r : ℕ) (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), (∀ a, ε a = 1 ∨ ε a = -1) → 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  first | exact @GlobalTheory.upperTriangular_near_diag_of_gram_near | exact GlobalTheory.upperTriangular_near_diag_of_gram_near | (intros; apply GlobalTheory.upperTriangular_near_diag_of_gram_near <;> assumption)
end
