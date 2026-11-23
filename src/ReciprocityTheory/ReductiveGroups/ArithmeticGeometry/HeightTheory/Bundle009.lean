module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle010
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift

open MvPolynomial

section Clear

variable {A : Type} [CommRing A] [IsDomain A] {σ : Type}

theorem clear_denoms (P : MvPolynomial σ (FractionRing A)) :
    ∃ (b : A) (p : MvPolynomial σ A), b ≠ 0 ∧
      MvPolynomial.map (algebraMap A (FractionRing A)) p =
        MvPolynomial.C (algebraMap A (FractionRing A) b) * P := by
  induction P using MvPolynomial.induction_on
  next a =>
    obtain ⟨z, hz⟩ := IsLocalization.surj (nonZeroDivisors A) a
    refine ⟨z.2, C z.1, nonZeroDivisors.coe_ne_zero z.2, ?_⟩
    rw [MvPolynomial.map_C, ← hz, MvPolynomial.C_mul, mul_comm]
  next p q hp hq =>
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := hp
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := hq
    refine ⟨b₁ * b₂, C b₂ * p₁ + C b₁ * p₂, mul_ne_zero hb₁ hb₂, ?_⟩
    simp only [_root_.map_add (f := _), _root_.map_mul, MvPolynomial.map_C, h₁, h₂]
    ring
  next p n hp =>
    obtain ⟨b, q, hb, h⟩ := hp
    exact ⟨b, q * X n, hb, by rw [_root_.map_mul, MvPolynomial.map_X, h, mul_assoc]⟩

noncomputable def toFracY (A : Type) [CommRing A] [IsDomain A] (σ : Type) :
    MvPolynomial σ A →+* FractionRing (MvPolynomial σ (FractionRing A)) :=
  (algebraMap (MvPolynomial σ (FractionRing A)) _).comp (MvPolynomial.map (algebraMap A (FractionRing A)))

theorem toFracY_injective : Function.Injective (toFracY A σ) := by
  intro x y h
  have h' : algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) x) =
      algebraMap (MvPolynomial σ (FractionRing A)) (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) y) := h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
    (IsFractionRing.injective _ _ h')


theorem isFractionRing_toFracY :
    @IsFractionRing (MvPolynomial σ A) _ (FractionRing (MvPolynomial σ (FractionRing A))) _
      (toFracY A σ).toAlgebra := by
  letI := (toFracY A σ).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine IsUnit.mk0 _ (fun h => nonZeroDivisors.coe_ne_zero y (toFracY_injective ?_))
    rw [_root_.map_zero]
    exact h
  · intro z
    obtain ⟨uv, huv⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial σ (FractionRing A))) z
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := clear_denoms (uv.1 : MvPolynomial σ (FractionRing A))
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := clear_denoms (uv.2 : MvPolynomial σ (FractionRing A))
    have hv : (uv.2 : MvPolynomial σ (FractionRing A)) ≠ 0 := nonZeroDivisors.coe_ne_zero uv.2
    have hβ₂ : algebraMap A (FractionRing A) b₂ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb₂)
    have hp₂ne : p₂ ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at h₂
      exact mul_ne_zero (fun h => hβ₂ (MvPolynomial.C_eq_zero.mp h)) hv h₂.symm
    have hp₂ : C b₁ * p₂ ∈ nonZeroDivisors (MvPolynomial σ A) :=
      mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (fun h => hb₁ (MvPolynomial.C_eq_zero.mp h)) hp₂ne)
    refine ⟨⟨C b₂ * p₁, ⟨C b₁ * p₂, hp₂⟩⟩, ?_⟩
    show z * toFracY A σ (C b₁ * p₂) = toFracY A σ (C b₂ * p₁)
    simp only [toFracY, RingHom.coe_comp, Function.comp_apply, _root_.map_mul,
      MvPolynomial.map_C, h₁, h₂]
    linear_combination (algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₁)) *
      algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₂))) * huv
  · intro x y h
    exact ⟨1, by rw [toFracY_injective h]⟩

end Clear

section Disjoint

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

private theorem liftY_algebraMap (x : MvPolynomial σ L) :
    ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)
        (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) x) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.map (algebraMap L E) x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

private theorem linearIndependent_algebraMap_C_fractionRing
    [Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))]
    (hmap : algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY)
    {ι : Type} [Fintype ι] (e : ι → E) (he : LinearIndependent L e) :
    LinearIndependent (FractionRing (MvPolynomial σ L))
      (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (e i))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j)) = 0 := by
    simpa only [Algebra.smul_def] using hg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial σ L)) g
  have hb' : ∀ j, ∃ c : MvPolynomial σ L,
      algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) c =
        algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) * g j := by
    intro j
    obtain ⟨c, hc⟩ := RingHom.mem_rangeS.mp (hb j)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  choose a ha using hb'
  have key : ∀ j, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
      (MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY
          (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L)) *
        (algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
          algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j))) := by
    intro j
    rw [_root_.map_mul, ← liftY_algebraMap, ha j, _root_.map_mul, hmap, mul_assoc]
  have hsum : ∑ j, MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j) = 0 := by
    apply IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))

    rw [_root_.map_zero, _root_.map_sum, Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum,
    hg', mul_zero]
  have hcoeff : ∀ m j, AddMonoidAlgebra.coeff (a j) m = 0 := by
    intro m
    have hsum' : ∑ j, MvPolynomial.C (e j) * MvPolynomial.map (algebraMap L E) (a j) = 0 := by
      simpa only [mul_comm] using hsum
    have h0 := congrArg (AddMonoidAlgebra.coeff · m) hsum'
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      AddMonoidAlgebra.coeff_zero] at h0
    have h1 : ∑ j, AddMonoidAlgebra.coeff (a j) m • e j = 0 := by
      simpa [Algebra.smul_def, mul_comm] using h0
    exact Fintype.linearIndependent_iff.mp he (fun j => AddMonoidAlgebra.coeff (a j) m) h1
  have hai : a i = 0 := by
    ext m
    simpa using hcoeff m i
  have h2 := ha i
  rw [hai, _root_.map_zero] at h2
  have hβ : algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  exact (mul_eq_zero.mp h2.symm).resolve_left hβ

theorem finiteDimensional_of_liftY
    (hfin : letI := (VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
      FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))) :
    FiniteDimensional L E := by
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    (ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
  haveI : FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    hfin
  have hbound : ∀ s : Finset E, LinearIndependent L (fun x : s => (x : E)) →
      s.card ≤ Module.finrank (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := by
    intro s hs
    have hli := linearIndependent_algebraMap_C_fractionRing (σ := σ) rfl (fun x : s => (x : E)) hs
    simpa using hli.fintype_card_le_finrank
  have hr := rank_le hbound
  exact Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0))

end Disjoint

end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def tOf (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) : Fin d.D → Fin (d.N + 1) → ℂ :=
  fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j

noncomputable def evT (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (q : KTp K d.D d.N) : ℂ :=
  MvPolynomial.eval₂ sg (fun v : TVar d.D d.N => Fin.cases (t0 v.2) (fun i => t i v.2) v.1) q

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

section Proj

variable {K : Type} [Field K] {r k : ℕ}

noncomputable def hBm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l j => σ (b j l)

noncomputable def hPm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin r) ℂ :=
  1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ

noncomputable def hns {r : ℕ} (x : Fin r → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

private theorem linearIndependent_map_ringHom_complex' (σ : K →+* ℂ) {s : Type*} [Fintype s] {v : s → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  let A : Matrix (Fin r) s K := Matrix.of fun l i => v i l
  have hAv : ∀ t : s → K, A *ᵥ t = ∑ i, t i • v i := by
    intro t
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    have h1 : ∑ i, t i • v i = 0 := by rw [← hAv]; exact ht
    funext i
    exact Fintype.linearIndependent_iff.mp hv t h1 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hker
  have hLA : LinearMap.toMatrix' g * A = 1 := by
    have e : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have := congrArg LinearMap.toMatrix' hg
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
    rwa [e] at this
  have hLAσ : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hLA]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hAc : A.map σ *ᵥ c = 0 := by
    rw [← hc]
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hc0 : c = 0 := by
    calc c = ((LinearMap.toMatrix' g).map σ * A.map σ) *ᵥ c := by rw [hLAσ, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

theorem linearIndependent_map_embedding (σ : K →+* ℂ) {ι : Type*} {v : ι → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_map_ringHom_complex' σ (hv.comp (Subtype.val : s → ι) Subtype.val_injective)

theorem embeddingColumns_mulVec (σ : K →+* ℂ) (b : Fin k → Fin r → K) (z : Fin k → ℂ) :
    hBm σ b *ᵥ z = ∑ j, z j • fun l => σ (b j l) := by
  funext l
  simp [hBm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem isUnit_det_embeddingGram (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    IsUnit ((hBm σ b)ᴴ * hBm σ b).det := by
  have hli := linearIndependent_map_embedding σ hb
  have hinj : Function.Injective (hBm σ b).mulVec := by
    intro x y hxy
    have h1 : ∑ j, (x - y) j • (fun l => σ (b j l)) = 0 := by
      rw [← embeddingColumns_mulVec, Matrix.mulVec_sub, hxy, sub_self]
    have h2 := Fintype.linearIndependent_iff.mp hli (x - y) h1
    funext j
    exact sub_eq_zero.mp (h2 j)
  have hker : LinearMap.ker ((hBm σ b)ᴴ * hBm σ b).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self, LinearMap.ker_eq_bot]
    exact hinj
  have hinj2 : Function.Injective ((hBm σ b)ᴴ * hBm σ b).mulVec := LinearMap.ker_eq_bot.mp hker
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj2)

theorem conjTranspose_mul_orthogonalProjector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    (hBm σ b)ᴴ * hPm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, sub_self]

theorem orthogonalProjector_mul_embeddingColumns (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hBm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one, sub_self]

theorem orthogonalProjector_conjTranspose (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by
  simp only [hPm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem orthogonalProjector_mul_self (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hPm σ b = hPm σ b := by
  have h := conjTranspose_mul_orthogonalProjector σ hb
  calc hPm σ b * hPm σ b
      = (1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) * hPm σ b := rfl
    _ = hPm σ b - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * ((hBm σ b)ᴴ * hPm σ b) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = hPm σ b := by rw [h, Matrix.mul_zero, sub_zero]

theorem orthogonalProjector_orthogonal (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_embeddingColumns σ hb, Matrix.vecMul_zero, zero_dotProduct]

theorem normSqSum_add_of_orthogonal {r : ℕ} (a c : Fin r → ℂ) (h : star a ⬝ᵥ c = 0) :
    hns (a + c) = hns a + hns c := by
  unfold hns
  have h' : ∑ i, (a i * (starRingEnd ℂ) (c i)).re = 0 := by
    have h1 : ∑ i, a i * (starRingEnd ℂ) (c i) = (starRingEnd ℂ) (star a ⬝ᵥ c) := by

      simp only [dotProduct, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [← Complex.re_sum, h1, h, map_zero, Complex.zero_re]
  simp only [Pi.add_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, h', mul_zero, add_zero]

theorem orthogonalProjector_mulVec_ne_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∉ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) ≠ 0 := by
  intro h0
  have hli := linearIndependent_map_embedding σ ((linearIndependent_finCons).mpr ⟨hb, hq⟩)
  have hcons : (fun i l => σ ((Fin.cons q b : Fin (k + 1) → Fin r → K) i l)) =
      (Fin.cons (fun l => σ (q l)) (fun j l => σ (b j l)) : Fin (k + 1) → Fin r → ℂ) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hcons, linearIndependent_finCons] at hli
  apply hli.2
  have hv : (fun i => σ (q i)) =
      (hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) *ᵥ fun i => σ (q i) := by
    unfold hPm at h0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have hv2 : (fun i => σ (q i)) =
      hBm σ b *ᵥ (((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ fun i => σ (q i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hv
  rw [hv2, embeddingColumns_mulVec]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem orthogonalProjector_mulVec_eq_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∈ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have h1 : (fun i => σ ((∑ j, c j • b j) i)) = hBm σ b *ᵥ fun j => σ (c j) := by
    rw [embeddingColumns_mulVec]
    funext i

    simp [Finset.sum_apply, map_sum, map_mul]
  rw [h1, Matrix.mulVec_mulVec, orthogonalProjector_mul_embeddingColumns σ hb, Matrix.zero_mulVec]

end Proj

section PT

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem crossGram_eq_embeddingColumns (σ : K →+* ℂ) {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramX 1 σ b c = (hBm σ b)ᴴ * hBm σ c := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramX, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem gramMatrix_eq_embeddingColumns (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC 1 σ b = (hBm σ b)ᴴ * hBm σ b := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem quotientGram_eq_projector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) (i j : Fin m) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c i j =
      star (hPm σ b *ᵥ fun l => σ (c i l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (c j l)) := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin r) (Fin m) ℂ) (i j : Fin m),
      (Cᴴ * M * C) i j = star (fun l => C l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
    intro M C i j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hq : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
    rw [gramMatrix_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, crossGram_eq_embeddingColumns]
    unfold hPm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hq, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_self σ hb]
  rfl

end PT

end ReciprocityTheory.ChartRestriction.G.T0
end
