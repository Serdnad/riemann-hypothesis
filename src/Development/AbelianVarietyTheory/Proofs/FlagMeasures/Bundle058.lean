module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
public import Formalism.HermitianLattices.Bundle003
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalRingCardinality.Params
public import Mathlib.Algebra.Order.Archimedean.Defs

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.ReCoords

theorem comap_bij (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (h2 : Module.finrank F E = 2) :
    Function.Bijective fun w : InfinitePlace E => w.comap (algebraMap F E) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := E), ?_⟩
  have h1 := IsTotallyComplex.finrank E
  have h2' := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem re_embedding_comap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace E) (y : F) :
    ((w.comap (algebraMap F E)).embedding y).re = (w.embedding (algebraMap F E y)).re := by
  have key : ∀ φ : E →+* ℂ, (((InfinitePlace.mk φ).comap (algebraMap F E)).embedding y).re = (φ (algebraMap F E y)).re := by
    intro φ
    rw [InfinitePlace.comap_mk]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap F E)) with h | h
    · rw [h]; rfl
    · rw [h]; simp [ComplexEmbedding.conjugate_coe_eq]
  have := key w.embedding
  rwa [InfinitePlace.mk_embedding] at this

theorem mixedSpace_reCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  intro F E _ _ _ _ _ σ h
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  haveI : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  let g : InfinitePlace E ≃ {v : InfinitePlace F // InfinitePlace.IsReal v} :=
    (Equiv.ofBijective _ (comap_bij F E h.2.2.1)).trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)).symm
  have hg : ∀ w, (g w).1 = w.comap (algebraMap F E) := fun w => rfl
  let L : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun x w => x.1 (g w)
      invFun := fun f => (fun v => f (g.symm v), 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Prod.ext (funext fun v => by simp) (Subsingleton.elim _ _)
      right_inv := fun f => funext fun w => by simp }
  refine ⟨L.toContinuousLinearEquiv, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // InfinitePlace.IsComplex w} → ℂ)) := by
      rw [volume_pi, Measure.pi_of_empty]; infer_instance
    have h1 : MeasurePreserving (Prod.fst : mixedEmbedding.mixedSpace F → _) volume volume :=
      measurePreserving_fst
    have h2 := volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm
    have heq : (L.toContinuousLinearEquiv : mixedEmbedding.mixedSpace F → InfinitePlace E → ℝ) =
        (MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm) ∘ Prod.fst := by
      funext x w
      simp [L, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [heq]
    exact h2.comp h1
  · intro y
    funext w
    show (mixedEmbedding F y).1 (g w) = _
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, reV]
    rw [← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ y), InfinitePlace.embedding_of_isReal_apply, hg]
    exact re_embedding_comap w y

end GlobalTheory.SnMass.ReCoords
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  intro B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht
  obtain ⟨χ, hχ, hχc⟩ := GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf
  have hZ := GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht
  have hD := GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g
  set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS
  set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd
  set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd
  have h1 : S ⊆ Z := fun y hy => hy.2
  have h2 : Z ⊆ S ∪ D := by
    intro y hy
    by_cases hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)
    · exact Or.inl ⟨hp, hy⟩
    · right
      have hne : ¬ ∀ s : Fin (k + 1) → B,
          ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0 :=
        fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)
      push Not at hne
      obtain ⟨s, hs, hs0⟩ := hne
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      refine ⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩
      · intro h0
        apply hs0
        rw [h0, zero_smul, zero_add] at hs
        have h3 := hx.eq_zero c (fun i => s i.succ) hs
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun h3 j
      · simp only [neg_smul, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hs
  have h3 : S.ncard ≤ Z.ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h4 : Z.ncard ≤ S.ncard + 2 * q ^ n :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))
  have h3' : (S.ncard : ℝ) ≤ Z.ncard := by exact_mod_cast h3
  have h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n := by exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  rw [abs_le] at hZ ⊢
  constructor <;> linarith [hZ.1, hZ.2]

end GlobalTheory.GramCount
end

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

open NumberField Module Matrix in
open scoped ENNReal in
private lemma exists_integer_eq_star {K : Type} [Field K] [NumberField K] [StarRing K]
    (a : 𝓞 K) : ∃ b : 𝓞 K, (b : K) = star (a : K) := by
  have hint : IsIntegral ℤ (starRingEnd K (a : K)) :=
    map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)
  rw [starRingEnd_apply] at hint
  exact ⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩


open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  intro K _ _ _ h
  unfold _root_.Formalism.HermitianLatticesTheory.IsCMUnram at h
  obtain ⟨-, -, hP⟩ := h
  let S : Set (𝓞 K) := {x | ∃ θ τ : 𝓞 K,
    algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}
  let I : Ideal (𝓞 K) := Ideal.span S
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨θ, τ, hτ, hnot⟩ := hP P hPm
    exact hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))
  have key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨θ, τ, hτ, rfl⟩ := hx
      change (τ : K) = star (θ : K) at hτ
      have h2 : star (τ : K) = θ := by rw [hτ, star_star]
      refine ⟨θ * (τ - θ), ?_⟩
      push_cast
      rw [star_sub, star_mul', star_sub, h2, ← hτ]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      obtain ⟨y', hy'⟩ := exists_integer_eq_star y
      refine ⟨s + u + x * y', ?_⟩
      push_cast
      simp only [star_add, star_mul', hy', star_star]
      linear_combination hs + hu
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨c', hc'⟩ := exists_integer_eq_star c
      refine ⟨c * c' * s, ?_⟩
      rw [smul_eq_mul]
      push_cast
      simp only [star_mul', hc', star_star]
      linear_combination ((c : K) * star (c : K)) * hs
  obtain ⟨t, ht⟩ := key 1 (hI ▸ Submodule.mem_top)
  exact ⟨t, by simpa using ht.symm⟩

end GlobalTheory
end

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem exists_denominator_of_fg {V : Type} [AddCommGroup V] (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ)
    (M : Submodule ℤ V) (hM : M.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, (d : ℚ) * B x y = n := by
  obtain ⟨s, hs⟩ := Submodule.FG.map₂ B hM hM
  refine ⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩
  have key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)
      refine ⟨c * a.num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.den_mul_eq_num]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩
    | smul c a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩
  intro x hx y hy
  exact key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)

theorem isom_sub_mem_of_congr : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U X : Submodule K V) (M : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V) (g : ℕ), h.IsSymm → X ≤ U → (∀ x ∈ X, ∀ y ∈ U, h x y = 0) → (∀ x ∈ U, x ∉ X → 0 < Algebra.trace ℚ K (h x x)) → M.FG → (∀ x ∈ M, x ∈ U) → γ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ x ∈ X, γ x ∈ X) → 3 ≤ g → (∀ x ∈ M, ∃ y ∈ M, γ x - x - (g : K) • y ∈ X) → ∀ x ∈ M, γ x - x ∈ X := by
  intro K V _ _ _ _ _ _ _ _ h U X M γ g hs hXU hrad hpos hM hMU hγ hγX hg hcong
  have hiso : ∀ x y, h (γ x) (γ y) = h x y := hγ
  have hrad' : ∀ y ∈ U, ∀ x ∈ X, h y x = 0 := fun y hy x hx => by
    rw [← hs.eq x y, hrad x hx y hy, map_zero]
  let B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ := LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ K (h x y))
    (fun a b c => by simp) (fun c a b => by rw [map_zsmul h, LinearMap.smul_apply, map_zsmul])
    (fun a b c => by simp)
    (fun c a b => by rw [map_zsmul (h a), map_zsmul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y) := fun _ _ => rfl
  obtain ⟨d, hd, hden⟩ := exists_denominator_of_fg B (M.restrictScalars ℤ) (hM.restrictScalars)
  have hnn : ∀ x ∈ U, 0 ≤ B x x := fun x hx => by
    by_cases hxX : x ∈ X
    · rw [hB, hrad x hxX x hx, map_zero]
    · exact (hpos x hx hxX).le
  have main : ∀ n : ℕ, ∀ x ∈ M, (d : ℚ) * B x x < n → γ x - x ∈ X := by
    intro n
    induction n with
    | zero =>
      intro x hx hlt
      have := hnn x (hMU x hx)
      have : (0 : ℚ) ≤ d * B x x := by positivity
      simp at hlt
      linarith
    | succ n ih =>
      intro x hx hlt
      by_cases hxX : x ∈ X
      · exact X.sub_mem (hγX x hxX) hxX
      obtain ⟨y, hy, hu⟩ := hcong x hx
      set u := γ x - x - (g : K) • y with hu_def
      set z := γ x - x with hz_def
      have hz : z = (g : K) • y + u := by rw [hu_def]; abel
      have hxU := hMU x hx
      have hyU := hMU y hy
      have hzU : z ∈ U := hz ▸ U.add_mem (U.smul_mem _ hyU) (hXU hu)
      have hγx : γ x = x + z := by rw [hz_def]; abel
      have hγxU : γ x ∈ U := hγx ▸ U.add_mem hxU hzU
      have h1 : B z z = (g : ℚ) ^ 2 * B y y := by
        have e1 : B u z = 0 := by rw [hB, hrad u hu z hzU, map_zero]
        have e2 : B y u = 0 := by rw [hB, hrad' y hyU u hu, map_zero]
        have hz' : z = (g : ℤ) • y + u := by rw [hz, natCast_zsmul, Nat.cast_smul_eq_nsmul]
        calc B z z = B ((g : ℤ) • y + u) z := by rw [← hz']
          _ = (g : ℤ) • B y z := by rw [map_add (f := _), LinearMap.add_apply, e1, map_smul]; simp
          _ = (g : ℤ) • B y ((g : ℤ) • y + u) := by rw [← hz']
          _ = _ := by rw [map_add (f := _), e2, map_smul]; simp; ring
      have h2 : B z z + B (γ x + x) (γ x + x) = 4 * B x x := by
        have e : B (γ x) (γ x) = B x x := by rw [hB, hB, hiso]
        rw [hz_def]
        simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, e]
        ring
      have h3 := hnn _ (U.add_mem hγxU hxU)
      have hxp : 0 < B x x := hpos x hxU hxX
      have hyn := hnn y hyU
      have hg' : (9 : ℚ) ≤ (g : ℚ) ^ 2 := by
        have : (3 : ℚ) ≤ g := by exact_mod_cast hg
        nlinarith
      have hlt' : B y y < B x x := by nlinarith
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      obtain ⟨a, ha⟩ := hden x hx x hx
      obtain ⟨b, hb⟩ := hden y hy y hy
      have hab : b < a := by
        have : (b : ℚ) < a := by rw [← ha, ← hb]; exact mul_lt_mul_of_pos_left hlt' hd'
        exact_mod_cast this
      have han : a < n + 1 := by
        rw [ha] at hlt
        exact_mod_cast hlt
      have hyX : γ y - y ∈ X := ih y hy (by
        rw [hb]
        have : b < n := by omega
        exact_mod_cast this)
      have hw : γ z - z ∈ X := by
        have : γ z - z = (g : K) • (γ y - y) + (γ u - u) := by
          rw [hz, map_add (f := _), map_smul, smul_sub]; abel
        rw [this]
        exact X.add_mem (X.smul_mem _ hyX) (X.sub_mem (hγX u hu) hu)
      have hzz : h z z = 0 := by
        have e := hiso x z
        have e2 : h (γ x) (γ z - z) = 0 := hrad' _ hγxU _ hw
        rw [map_sub, e, hγx, map_add (f := _), LinearMap.add_apply] at e2
        linear_combination -e2
      by_contra hzX
      have := hpos z hzU hzX
      rw [hzz, map_zero] at this
      exact lt_irrefl _ this
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℚ) * B x x)
  exact main n x hx hn

end GlobalTheory
end

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem loop_count_exponent_bound : ∀ C₁ Ad : ℝ, 1 ≤ C₁ → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, ∀ (s r f : ℕ) (De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 1 ≤ De → 1 ≤ NT → 1 ≤ HH → De ≤ HH ^ Ad → NT ≤ HH → De ^ (4 + Real.logb 2 (2 * f)) * (De * NT) ^ (C₁ * s + C₁ * Real.log f) * (9 ^ (s * f) * (HH ^ (max Ad 3)) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 ≤ HH ^ (C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + Real.logb 2 (2 * f))) * (C * s * f) ^ (6 * s * f) := by
  intro C₁ Ad hC₁
  have ha3 : (3 : ℝ) ≤ max Ad 3 := le_max_right _ _
  have haA : Ad ≤ max Ad 3 := le_max_left _ _
  generalize max Ad 3 = a at ha3 haA ⊢
  have hb : (0 : ℝ) ≤ (a + 1) * C₁ := by positivity
  refine ⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩
  intro C hC s r f De NT HH hs hf hDe hNT hHH hDA hN
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hH0 : 0 < HH := by linarith
  have hlf0 : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlfL : Real.log f ≤ Real.logb 2 (2 * f) := by
    rw [Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ)) := le_trans hlf0 hlfL
  generalize Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢
  generalize Real.log (f : ℝ) = l at hlfL hlf0 ⊢
  have hDa : De ≤ HH ^ a := hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)
  have hDN : De * NT ≤ HH ^ (a + 1) := by
    rw [Real.rpow_add hH0, Real.rpow_one]
    exact mul_le_mul hDa hN (by linarith) (by positivity)
  have h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by linarith) hDa (by linarith)
  have h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by positivity) hDN (by positivity)
  have h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2
      = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
    congr 1
    push_cast
    ring
  have hC3 : (3 : ℝ) ≤ C * s * f := by
    have h0 : (3 : ℝ) ≤ C := by linarith
    have : (3 : ℝ) ≤ C * s := by nlinarith
    nlinarith
  have h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f) := by
    calc ((9 : ℝ) ^ (s * f)) ^ 2 = 3 ^ (4 * (s * f)) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          congr 1; ring
      _ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _
  have hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))
      ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L) := by
    set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP
    have hsr : (0 : ℝ) ≤ s * r := by positivity
    have hrr : (0 : ℝ) ≤ r ^ 2 := by positivity
    have e1 : (s : ℝ) ≤ P := by rw [hP]; nlinarith
    have e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P := by rw [hP]; nlinarith
    have hP0 : 0 ≤ P := by linarith
    have e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P := mul_le_mul_of_nonneg_right hC hP0
    have e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P := mul_le_mul_of_nonneg_left e1 hb
    have e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hb
    have e7 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)
    have e8 : a * (4 + L) ≤ a * (5 * (1 + L)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P := by rw [hP]; ring
    rw [e9]
    clear_value P
    linear_combination e3 + e4 + e5 + e6 + e7 + e8
  rw [mul_pow, h3]
  calc _ ≤ HH ^ (a * (4 + L)) * HH ^ ((a + 1) * (C₁ * s + C₁ * l)) *
        ((C * s * f) ^ (6 * s * f) * HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))) := by
        gcongr
    _ = HH ^ (a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) * (C * s * f) ^ (6 * s * f) := by
        rw [Real.rpow_add hH0, Real.rpow_add hH0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)

end GlobalTheory
end
