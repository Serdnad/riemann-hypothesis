module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorter
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwistTie

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem exists_det_hom {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R)
    {r : ℕ} (hr : 1 ≤ r) (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) :
    ∃ δ : (Q ≃ₗ[R] Q) →* (R ⧸ I)ˣ, Function.Surjective δ ∧ ∀ (k : Q ≃ₗ[R] Q) (a : Matrix (Fin r) (Fin r) R),
      (∀ j, k (e.symm (Pi.single j 1)) = ∑ i, a i j • e.symm (Pi.single i 1)) →
        (δ k : R ⧸ I) = Ideal.Quotient.mk I a.det := by
  classical
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs) (fun a b => by
      ext x i
      simp [LinearEquiv.mul_apply])
  refine ⟨LinearEquiv.det.comp cj, fun u => ?_, fun k a ha => ?_⟩
  · let i₀ : Fin r := ⟨0, hr⟩
    let δ : (R ⧸ I)ˣ → Fin r → R ⧸ I := fun w => Function.update 1 i₀ w
    have hδ : ∀ w w' : (R ⧸ I)ˣ, w * w' = 1 → Matrix.diagonal (δ w) * Matrix.diagonal (δ w') = 1 := by
      intro w w' hw
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h
        simp only [δ, Function.update_self]
        rw [← Units.val_mul, hw, Units.val_one]
      · simp [δ, h]
    let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) :=
      Matrix.toLin'OfInv (hδ u⁻¹ u (inv_mul_cancel u)) (hδ u u⁻¹ (mul_inv_cancel u))
    have hg : LinearEquiv.det g = u := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) = Matrix.toLin' (Matrix.diagonal (δ u)) := rfl
      rw [this, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
      ext x i
      simp [cj]
    exact ⟨e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm, by rw [MonoidHom.comp_apply, hk, hg]⟩
  · rw [MonoidHom.comp_apply, LinearEquiv.coe_det, RingHom.map_det, ← LinearMap.det_toMatrix']
    congr 1
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change e (k (e.symm (Pi.single j 1))) i = Ideal.Quotient.mk I (a i j)

    rw [ha, map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
    · simp

theorem det_sub_mem_of_conj {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (A : Subring R) (hf : ∀ x, f x ∈ A)
    (I : Ideal O) (J : AddSubgroup R) (hJ : ∀ x ∈ I, ∀ y ∈ A, f x * y ∈ J) {n : ℕ} (G P Y : Matrix (Fin n) (Fin n) R)
    (a : Matrix (Fin n) (Fin n) O) (t m : O) (ht : t - 1 ∈ I) (hm : m ∈ I) (hP : IsUnit P.det) (hG : G.det ∈ A)
    (hY : ∀ i j, Y i j ∈ A) (h : (f t • G) * P = P * (a.map f + f m • Y)) : G.det - f a.det ∈ J := by
  have h1 : f t ^ n * G.det = (a.map f + f m • Y).det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, mul_comm P.det] at this
    exact hP.mul_right_cancel this
  let f' : O →+* A := f.codRestrict A hf
  let Y' : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => ⟨Y i j, hY i j⟩
  have h2 : (a.map f' + f' m • Y').det - f' a.det ∈ Ideal.span {f' m} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg A.subtype hz
  rw [map_sub, map_mul, RingHom.map_det] at h3
  have h4 : A.subtype.mapMatrix (a.map f' + f' m • Y') = a.map f + f m • Y := by
    ext i j
    rfl
  rw [h4, ← h1] at h3
  have h5 : t ^ n - 1 ∈ I := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow t 1 n
    rw [one_pow] at hq
    rw [hq]
    exact I.mul_mem_right _ ht
  have h6 := sub_mem (hJ m hm z z.2) (hJ _ h5 _ hG)
  convert h6 using 1
  change (z : R) * f m = f t ^ n * G.det - f a.det at h3
  rw [map_sub, map_pow, map_one]
  linear_combination -h3

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intRing : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  mul_mem' := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩)
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem det_sub_mem_hat {n : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (ι : La →ₗ[𝓞 E] (Fin n → E)) (hsp : Submodule.span E (Set.range ι) = ⊤) (I : Ideal (𝓞 E)) (hI : I ≠ ⊤)
    (v : Fin n → La) (hv : (⊤ : Submodule (𝓞 E) La) ≤ Submodule.span (𝓞 E) (Set.range v) ⊔ I • ⊤)
    (s : La →ₗ[𝓞 E] La) (N : ℕ) (hN : (N : 𝓞 E) ∈ I) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hG : G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h : ∀ j, ∃ w ∈ hat F (Set.range ι), G *ᵥ fv F (ι (v j)) - fv F (ι (s (v j))) = N • w) :
    ∃ a : Matrix (Fin n) (Fin n) (𝓞 E), (∀ j, s (v j) - ∑ i, a i j • v i ∈ (I • ⊤ : Submodule (𝓞 E) La)) ∧
      G.det - 1 ⊗ₜ ((a.det : 𝓞 E) : E) ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  obtain ⟨t, ht1, ht⟩ : ∃ t : 𝓞 E, t - 1 ∈ I ∧ ∀ l : La, t • l ∈ Submodule.span (𝓞 E) (Set.range v) := by
    obtain ⟨t, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule (𝓞 E) (La ⧸ Submodule.span (𝓞 E) (Set.range v))) Module.Finite.fg_top (by
        intro q _
        obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hv (Submodule.mem_top : l ∈ ⊤))
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add]
        refine Submodule.smul_induction_on hv (fun a ha z _ => ?_) (fun u v hu hv => ?_)
        · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ha trivial
        · rw [Submodule.Quotient.mk_add]; exact add_mem hu hv)
    refine ⟨t, hs1, fun l => ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hs _ trivial
  have ht0 : (t : E) ≠ 0 := by
    rw [RingOfIntegers.coe_ne_zero_iff]
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using ht1
  choose co hco using fun l => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (ht l)
  let P₀ : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => ι (v j) i
  have hP₀ : ∀ l, P₀ *ᵥ (fun j => (co l j : E)) = (t : E) • ι l := fun l => by
    have := congrArg ι (hco l)

    rw [map_sum, map_smul] at this
    funext i
    have := congrFun this i
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, Algebra.smul_def] at this
    simp only [P₀, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this
  have hu : IsUnit P₀ := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 ?_
    have : LinearMap.range P₀.mulVecLin = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨(t : E)⁻¹ • fun j => (co l j : E), ?_⟩
      rw [map_smul, Matrix.mulVecLin_apply, hP₀, inv_smul_smul₀ ht0]
    exact LinearMap.range_eq_top.1 this
  let inc : E →+* RA F E := (Algebra.TensorProduct.includeRight (R := F)).toRingHom
  have hinc : ∀ x, inc x = 1 ⊗ₜ x := fun _ => rfl
  let f : 𝓞 E →+* RA F E := inc.comp (algebraMap _ _)
  have hfv : ∀ x : Fin n → E, fv F x = fun i => inc (x i) := fun _ => rfl
  have hf : ∀ x, f x ∈ intRing F := fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  have hPl : ∀ l, P₀.map inc *ᵥ (fun j => f (co l j)) = f t • fv F (ι l) := fun l => by
    funext i
    have := congrArg inc (congrFun (hP₀ l) i)
    rw [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact this
  have hw : ∀ w ∈ hat F (Set.range ι), ∃ y : Fin n → RA F E, (∀ i, y i ∈ intRing F) ∧ P₀.map inc *ᵥ y = f t • w := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨l, rfl⟩, rfl⟩ := hx
      refine ⟨(b ⊗ₜ[F] (1 : E) : RA F E) • fun j => f (co l j),
        fun i => mul_mem (tmul_mem_adelicCompletion_of_integral F hb ⟨1, map_one _⟩ : _ ∈ intRing F) (hf _), ?_⟩
      rw [Matrix.mulVec_smul, hPl, smul_comm]
      congr 1
      funext i
      simp [fv]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', fun i => add_mem (hx' i) (hy' i), by rw [Matrix.mulVec_add, ex, ey, smul_add]⟩
    | neg x _ hx =>
      obtain ⟨x', hx', ex⟩ := hx
      exact ⟨-x', fun i => neg_mem (hx' i), by rw [Matrix.mulVec_neg, ex, smul_neg]⟩
  choose w hwm hwe using h
  choose y hy hye using fun j => hw _ (hwm j)
  refine ⟨Matrix.of fun i j => co (s (v j)) i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    rw [hco, show s (v j) - t • s (v j) = -((t - 1) • s (v j)) by rw [sub_smul, one_smul, neg_sub]]
    exact neg_mem (Submodule.smul_mem_smul ht1 trivial)
  · refine det_sub_mem_of_conj f (intRing F) hf I _ (fun x hx z hz => ?_) G (P₀.map inc) (Matrix.of fun i j => y j i) _ t N
      ht1 hN ?_ hG (fun i j => hy j i) ?_
    · exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))
        (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, I.mul_mem_right _ hx, map_mul _ _ _⟩)
        (one_tmul_mem_adelicCompletionOfElementSet F ⟨x, hx, rfl⟩) hz
    · exact (Matrix.isUnit_iff_isUnit_det _).1 (hu.map inc.mapMatrix)
    · ext i j
      have e1 : ((f t • G) * P₀.map inc) i j = (f t • (G *ᵥ fv F (ι (v j)))) i := by
        rw [Matrix.smul_mul]; rfl
      have e2 : (P₀.map inc * ((Matrix.of fun i j => co (s (v j)) i).map f + f N • Matrix.of fun i j => y j i)) i j =
          (P₀.map inc *ᵥ ((fun i => f (co (s (v j)) i)) + f N • y j)) i := rfl
      rw [e1, e2, Matrix.mulVec_add, Matrix.mulVec_smul, hPl, hye, sub_eq_iff_eq_add'.1 (hwe j), smul_add, map_natCast,
        Nat.cast_smul_eq_nsmul, smul_comm]

end GlobalTheory.TwistTie
end
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  first | exact @GlobalTheory.SmoothForms.bicomm_permMat | exact GlobalTheory.SmoothForms.bicomm_permMat | (intros; apply GlobalTheory.SmoothForms.bicomm_permMat <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm : ∀ (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ π, T * permMat n d π = permMat n d π * T) → T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  first | exact @GlobalTheory.SymmTensor.mem_adjoin_polar | exact GlobalTheory.SymmTensor.mem_adjoin_polar | (intros; apply GlobalTheory.SymmTensor.mem_adjoin_polar <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  first | exact @GlobalTheory.SmoothForms.frameSmall | exact GlobalTheory.SmoothForms.frameSmall | (intros; apply GlobalTheory.SmoothForms.frameSmall <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j := by
  first | exact @GlobalTheory.SmoothForms.hasLog_of_isLieData | exact GlobalTheory.SmoothForms.hasLog_of_isLieData | (intros; apply GlobalTheory.SmoothForms.hasLog_of_isLieData <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  first | exact @GlobalTheory.SmoothForms.der_smooth_and_linear | exact GlobalTheory.SmoothForms.der_smooth_and_linear | (intros; apply GlobalTheory.SmoothForms.der_smooth_and_linear <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L, j Z = j X * j Y - j Y * j X → Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) = Der (expMap j s) Z φ := by
  first | exact @GlobalTheory.SmoothForms.Bracket.der_bracket | exact GlobalTheory.SmoothForms.Bracket.der_bracket | (intros; apply GlobalTheory.SmoothForms.Bracket.der_bracket <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, Sm (expMap j s) φ ↔ ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => expMap j s (t i • Y i)).prod) := by
  first | exact @GlobalTheory.SmoothForms.SecondKind.main | exact GlobalTheory.SmoothForms.SecondKind.main | (intros; apply GlobalTheory.SmoothForms.SecondKind.main <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

section GelfandCentral

variable {A : Type} [Ring A] {n : ℕ}

theorem sum_fin_succ_fun_cons {M : Type} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin n) → M) :
    ∑ idx, f idx = ∑ c : Fin n, ∑ idx : Fin k → Fin n, f (Fin.cons c idx) := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp f).symm

theorem pow_of_apply_eq_sum_paths (E : Fin n → Fin n → A) (k : ℕ) (c e : Fin n) :
    (Matrix.of E ^ (k + 1)) c e = ∑ idx : Fin k → Fin n, (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons c idx : Fin (k + 1) → Fin n) a) ((Fin.snoc idx e : Fin (k + 1) → Fin n) a)).prod := by
  induction k generalizing c with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_fun_cons]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [List.ofFn_succ (n := k + 1), List.prod_cons, ← Fin.cons_snoc_eq_snoc_cons]
    simp

theorem gelfA_eq_sum_pow (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA E k = ∑ c, (Matrix.of E ^ (k + 1)) c c := by
  rw [gelfA, sum_fin_succ_fun_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_of_apply_eq_sum_paths]
  refine Finset.sum_congr rfl fun idx _ => ?_
  congr 2
  funext a
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · rw [Fin.coeSucc_eq_succ]; simp

theorem comm_pow_of_apply (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ)
    (c e : Fin n) : E a b * (Matrix.of E ^ m) c e - (Matrix.of E ^ m) c e * E a b =
      (if b = c then (Matrix.of E ^ m) a e else 0) - (if e = a then (Matrix.of E ^ m) c b else 0) := by
  first
  | exact @_root_.GlobalTheory.PowEntryCommutator.target
  | exact _root_.GlobalTheory.PowEntryCommutator.target
  | (apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEntryCommutator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEntryCommutator.target ..)

end GelfandCentral

theorem commute_gelfA : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  intro A _ _ n E hE k a b
  rw [← sub_eq_zero, gelfA_eq_sum_pow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end GlobalTheory.SmoothForms
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), E a b * wordMap E d M - wordMap E d M * E a b = wordMap E d (polar n d a b * M - M * polar n d a b) := by
  first | exact @GlobalTheory.SmoothForms.commutator_wordMap | exact GlobalTheory.SmoothForms.commutator_wordMap | (intros; apply GlobalTheory.SmoothForms.commutator_wordMap <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (π : Equiv.Perm (Fin d)), ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), wordMap E d (permMat n d π) - c ∈ filt E d := by
  first | exact @GlobalTheory.SmoothForms.PermWord.permWord | exact GlobalTheory.SmoothForms.PermWord.permWord | (intros; apply GlobalTheory.SmoothForms.PermWord.permWord <;> assumption)
end

section

open Formalism.MainNotions.S Matrix MeasureTheory

theorem _root_.GlobalTheory.T.hilbert_schur_unitary_irreducible_scalar : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  first | exact @GlobalTheory.hilbert_schur | exact GlobalTheory.hilbert_schur | (intros; apply GlobalTheory.hilbert_schur <;> assumption)
end
