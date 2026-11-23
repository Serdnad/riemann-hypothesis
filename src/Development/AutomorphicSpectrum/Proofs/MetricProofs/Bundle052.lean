module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.domCell_logNorm_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.volume_nonsimple_fibres_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | exact GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem emb_mul_bigZ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (a : 𝓞 E) (i k : Ix Ψ j j') :
    emb σ i a * bigZ q t i k = bigZ q t i k * star (emb σ k a) := by
  obtain ⟨i1, τ⟩ := i
  obtain ⟨k1, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases i1 with i1 | i1 <;> rcases k1 with k1 | k1 <;>
      simp [bigZ, emb, blockDiagonal_apply, mul_comm]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem tz_bigZe_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  intro E _ _ _ Ψ _ _ j j' n g σ e q t B _ hB a x
  funext i
  have hsub : B a (tz (bigZe e q t) x) i
      = B a x i - B a (bigZe e q t *ᵥ star x) i := by
    simp only [tz, map_sub, Pi.sub_apply]
  rw [hsub]
  simp only [tz, Pi.sub_apply]
  congr 1
  rw [hB a (bigZe e q t *ᵥ star x) i]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := emb_mul_bigZ σ q t a (e.symm i) (e.symm k)
  have hx : star (B a x) k = star (emb σ (e.symm k) a) * star (x k) := by
    simp [hB, mul_comm]
  rw [hx, ← mul_assoc, ← mul_assoc]
  simp only [bigZe, submatrix_apply, Pi.star_apply]
  rw [hk]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj

theorem not_eq_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) (h : ∀ a : 𝓞 E, σ τ a = star (σ τ' a)) : False := by
  have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := RingHom.ext h
  exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩

theorem emb_eq_star_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (i k : Ix Ψ j j') :
    (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  obtain ⟨s, τ⟩ := i
  obtain ⟨t, τ'⟩ := k
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.isLeft_inl, ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ τ' h
    | inr t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, star_star, ne_eq, Bool.true_eq_false, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext h)
      · rintro rfl a
        rfl
  | inr s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, ne_eq, Bool.false_eq_true, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext fun a => star_injective (h a))
      · rintro rfl a
        rfl
    | inr t =>
      simp only [emb, Sum.elim_inr, Sum.isLeft_inr, RingHom.comp_apply, starRingEnd_apply, star_star,
        ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ' τ fun a => (h a).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem exists_bigZe_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ) (hs : Zᵀ = Z)
    (hZ : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) :
    ∃ t, bigZe e q t = Z := by
  have hz : ∀ i k, ¬ ((e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → Z i k = 0 :=
    fun i k h => by_contra fun h0 => h (hZ i k h0)
  have hsym : ∀ i k, Z i k = Z k i := fun i k => by
    have := congrFun (congrFun hs k) i
    simpa [Matrix.transpose_apply] using this
  let t : Fin n → ℂ := fun m => Z (e (Sum.inr (q.symm m).2.1, (q.symm m).1)) (e (Sum.inl (q.symm m).2.2, (q.symm m).1))
  have hb : ∀ τ a b, ballMat q t τ a b = Z (e (Sum.inr a, τ)) (e (Sum.inl b, τ)) := by
    intro τ a b
    simp [ballMat, t]
  refine ⟨t, ?_⟩
  ext i k
  obtain ⟨⟨x, τ⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨y, τ'⟩, rfl⟩ := e.surjective k
  simp only [bigZe, bigZ, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hτ : τ = τ'
  · subst hτ
    rw [Matrix.blockDiagonal_apply_eq]
    rcases x with a | a <;> rcases y with b | b
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply, hb, hsym]
    · rw [Matrix.fromBlocks_apply₂₁, hb]
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hτ]
    exact (hz _ _ (by simp [hτ])).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem star_dotProduct_mulVec_eq {I : Type} [Fintype I] (M : Matrix I I ℂ) (a b : I → ℂ) :
    star (a ⬝ᵥ M *ᵥ b) = star a ⬝ᵥ (Mᴴ)ᵀ *ᵥ star b := by
  simp only [dotProduct, mulVec, Finset.sum_apply, star_sum, star_mul', Pi.star_apply, transpose_apply,
    conjTranspose_apply, Finset.mul_sum, RCLike.star_def]

theorem im_tz_form {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) (hZ : Zᵀ = Z)
    (hP : (1 - Zᴴ * Z).PosDef) (z w : I → ℂ) :
    (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = Zᴴ := ⟨_, rfl⟩
  rw [← hBdef] at hP ⊢
  have hBt : Bᵀ = B := by
    rw [hBdef]; ext i j
    simp only [transpose_apply, conjTranspose_apply]
    rw [← transpose_apply Z i j, hZ]
  have hBh : Bᴴ = Z := by rw [hBdef, conjTranspose_conjTranspose]
  have hdet : IsUnit (1 - B * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
  obtain ⟨H, hHdef⟩ : ∃ H, H = (1 - B * Z)⁻¹ := ⟨_, rfl⟩
  rw [← hHdef]
  have h1 : H * (1 - B * Z) = 1 := by rw [hHdef]; exact Matrix.nonsing_inv_mul _ hdet
  have h2 : (1 - B * Z) * H = 1 := by rw [hHdef]; exact Matrix.mul_nonsing_inv _ hdet
  have hHh : Hᴴ = H := by rw [hHdef]; exact hP.inv.isHermitian.eq
  have hT : (1 - B * Z)ᵀ = 1 - Z * B := by
    rw [transpose_sub, transpose_one, transpose_mul, hZ, hBt]
  have h3 : Hᵀ * (1 - Z * B) = 1 := by
    have := congrArg transpose h2
    rwa [transpose_mul, hT, transpose_one] at this
  have h4 : (1 - Z * B) * Hᵀ = 1 := by
    have := congrArg transpose h1
    rwa [transpose_mul, hT, transpose_one] at this
  have c1 : B * (1 - Z * B) = (1 - B * Z) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have c2 : Z * (1 - B * Z) = (1 - Z * B) * Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have K : H * B = B * Hᵀ := by
    calc H * B = H * B * ((1 - Z * B) * Hᵀ) := by rw [h4, Matrix.mul_one]
      _ = H * (B * (1 - Z * B)) * Hᵀ := by simp only [Matrix.mul_assoc]
      _ = H * (1 - B * Z) * (B * Hᵀ) := by rw [c1]; simp only [Matrix.mul_assoc]
      _ = B * Hᵀ := by rw [h1, Matrix.one_mul]
  have K2 : Z * H = Hᵀ * Z := by
    calc Z * H = Hᵀ * (1 - Z * B) * (Z * H) := by rw [h3, Matrix.one_mul]
      _ = Hᵀ * ((1 - Z * B) * Z) * H := by simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z * ((1 - B * Z) * H) := by rw [← c2]; simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z := by rw [h2, Matrix.mul_one]
  have hHB : H = 1 + H * B * Z := by
    have : H * (1 - B * Z) = H - H * B * Z := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this] at h1
    rw [← h1]; abel
  have hs : star (tz Z w) = star w - B *ᵥ w := by
    unfold tz
    rw [star_sub, star_mulVec, star_star, ← hBdef, ← mulVec_transpose, hBt]
  have dz : ∀ y : I → ℂ, (Z *ᵥ star z) ⬝ᵥ y = star z ⬝ᵥ Z *ᵥ y := by
    intro y
    rw [dotProduct_mulVec (star z), ← mulVec_transpose, hZ]
  have e1 : z ⬝ᵥ H *ᵥ star w = z ⬝ᵥ star w + z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    conv_lhs => rw [hHB]
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have e2 : z ⬝ᵥ H *ᵥ B *ᵥ w = z ⬝ᵥ (H * B) *ᵥ w := by rw [mulVec_mulVec]
  have e3 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ star w = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [dz, mulVec_mulVec]
  have e4 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ B *ᵥ w = star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [dz, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have s3 : star (z ⬝ᵥ (H * B) *ᵥ w) = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, conjTranspose_mul, hBh, hHh, transpose_mul, hZ, ← K2]
  have s4 : star (star z ⬝ᵥ (Z * H * B) *ᵥ w) = z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, star_star, conjTranspose_mul, conjTranspose_mul, hBh, hHh, ← hBdef,
      transpose_mul, transpose_mul, hZ, hBt, ← K]
  have main : tz Z z ⬝ᵥ H *ᵥ star (tz Z w) = z ⬝ᵥ star w + star (star z ⬝ᵥ (Z * H * B) *ᵥ w)
      - z ⬝ᵥ (H * B) *ᵥ w - star (z ⬝ᵥ (H * B) *ᵥ w) + star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [hs, s3, s4]
    unfold tz
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e1, e2, e3, e4]
    ring
  rw [main]
  simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

theorem im_tz_form' : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im :=
  fun Z hZ hP z w => im_tz_form Z hZ hP z w

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

variable {j j' : ℕ}

theorem sg_fb {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks a b c d)) :
    aᴴ * a - cᴴ * c = 1 ∧ aᴴ * b - cᴴ * d = 0 ∧ bᴴ * b - dᴴ * d = -1 := by
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 h
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h2
  · simpa [sub_eq_add_neg] using h4

theorem unit_of_rel {a : Matrix (Fin j) (Fin j) ℂ} {c : Matrix (Fin j') (Fin j) ℂ}
    (h : aᴴ * a - cᴴ * c = 1) : IsUnit a.det := by
  have e : aᴴ * a = 1 + cᴴ * c := by rw [← h]; abel
  have pd : (aᴴ * a).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)
  have hu : IsUnit (aᴴ * a).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  unfold sgI
  rw [fromBlocks_multiply]
  simp

theorem IsSgU.mul {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) : IsSgU (u * v) := by
  unfold IsSgU at *
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * sgI j j' * (u * v) = vᴴ * (uᴴ * sgI j j' * u) * v := by
        simp only [Matrix.mul_assoc]
    _ = sgI j j' := by rw [hu, hv]

theorem IsSgU.det_unit {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) : IsUnit u.det := by
  have : (sgI j j' * uᴴ * sgI j j') * u = 1 := by
    have e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u) := by
      simp only [Matrix.mul_assoc]
    rw [e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]
  exact Matrix.isUnit_det_of_left_inverse this

theorem unitary_iff_fb {p : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {r : Matrix (Fin j') (Fin j) ℂ} {s : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks p b r s)) :
    (fromBlocks p b r s)ᴴ * fromBlocks p b r s = 1 ↔ r = 0 := by
  obtain ⟨h1, h2, h3⟩ := sg_fb h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  constructor
  · intro e
    obtain ⟨e1, -, -, -⟩ := fromBlocks_inj.1 e
    have hz : (2 : ℂ) • (rᴴ * r) = 0 := by
      have : rᴴ * r + rᴴ * r = 0 := by
        have := sub_eq_zero.2 (e1.trans h1.symm)
        rw [← this]; abel
      rw [two_smul]; exact this
    have hz' : rᴴ * r = 0 := (smul_eq_zero.1 hz).resolve_left two_ne_zero
    exact conjTranspose_mul_self_eq_zero.1 hz'
  · rintro rfl
    simp only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢
    have hp : p * pᴴ = 1 := mul_eq_one_comm.1 h1
    have hb : b = 0 := by
      have : p * (pᴴ * b) = b := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      rw [← this, h2, Matrix.mul_zero]
    subst hb
    simp only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3
    simp [h1, h3]

theorem single_fb {a p : Matrix (Fin j) (Fin j) ℂ} {b e : Matrix (Fin j) (Fin j') ℂ}
    {c r : Matrix (Fin j') (Fin j) ℂ} {d s : Matrix (Fin j') (Fin j') ℂ}
    (hu : IsSgU (fromBlocks a b c d)) (hv : IsSgU (fromBlocks p e r s)) :
    c * a⁻¹ = (c * p + d * r) * (a * p + b * r)⁻¹ ↔ r = 0 := by
  have ha : IsUnit a.det := unit_of_rel (sg_fb hu).1
  have hp : IsUnit p.det := unit_of_rel (sg_fb hv).1
  have hw : IsUnit (a * p + b * r).det := by
    have := IsSgU.mul hu hv
    rw [fromBlocks_multiply] at this
    exact unit_of_rel (sg_fb this).1
  constructor
  · intro h
    have h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r := by
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]
    have hs : (d - c * a⁻¹ * b) * r = 0 := by
      have e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]
      rw [e1] at h'
      have : c * a⁻¹ * b * r = d * r := add_left_cancel h'
      rw [Matrix.sub_mul, this, sub_self]
    have hS : IsUnit (d - c * a⁻¹ * b).det := by
      have hd := IsSgU.det_unit hu
      letI := Matrix.invertibleOfIsUnitDet a ha
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hd
      exact isUnit_of_mul_isUnit_right hd
    have : (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r :=
      Matrix.nonsing_inv_mul_cancel_left _ _ hS
    rw [← this, hs, Matrix.mul_zero]
  · rintro rfl
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]

theorem single {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) :
    u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = (u * v).toBlocks₂₁ * (u * v).toBlocks₁₁⁻¹ ↔ vᴴ * v = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  obtain ⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩
  rw [unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]

theorem ballPt_inj {Ψ : Type} {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    {W W' : Ψ → Matrix (Fin j') (Fin j) ℂ} (h : ballPt q W = ballPt q W') : W = W' := by
  funext τ
  ext i' i
  have := congrFun h (q (τ, i, i'))
  simpa [ballPt] using this

theorem moebBall_zero {Ψ : Type} [Fintype Ψ] {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) :
    moebBall q w 0 = ballPt q fun τ => (w τ).toBlocks₂₁ * (w τ).toBlocks₁₁⁻¹ := by
  have hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  unfold moebBall
  congr 1
  funext τ
  rw [hb τ]
  simp [moebW]

theorem moebBall_zero_iff : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  intro Ψ _ j j' n q u v hu hv
  rw [moebBall_zero, moebBall_zero]
  constructor
  · intro h τ
    exact (single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)
  · intro h
    congr 1
    funext τ
    exact (single (hu τ) (hv τ)).2 (h τ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.exists_goodProj_first_coordinate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (i : (k : K) → ι k),
    IsCxVar Q e → (∃ z ∈ conePts Q, segre z i ≠ 0) →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsSetGoodProj (conePts Q) Ψ ∧ ∀ w, Ψ w 0 = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | exact GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord <;> assumption)
end
