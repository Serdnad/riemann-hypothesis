module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_coords {K C V : Type} [Field K] [Ring C] [Algebra K C] [Algebra ℚ K] [Algebra ℚ C]
    [IsScalarTower ℚ K C] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [FiniteDimensional ℚ K]
    [FiniteDimensional K C] (n : ℕ)
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hinj : Function.Injective rep) (hC : Module.finrank K C = n ^ 2)
    (hdim : Module.finrank ℚ V = n * Module.finrank ℚ K) :
    ∃ (kp : V ≃+ (Fin n → K)) (σ : C ≃ₐ[K] Matrix (Fin n) (Fin n) K), ∀ c w, kp (rep c w) = σ c *ᵥ kp w := by
  let f : K →+* Module.End ℚ V := (rep : C →+* Module.End ℚ V).comp (algebraMap K C)
  letI : Module K V := Module.compHom V f
  have hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w := fun _ _ => rfl
  haveI : IsScalarTower ℚ K V := by
    refine ⟨fun q x w => ?_⟩
    rw [hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]
    rfl
  haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V
  have hfin : Module.finrank K V = n := by
    have h := Module.finrank_mul_finrank ℚ K V
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hdim, mul_comm n] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hfin
  let r : C →ₐ[K] Module.End K V := AlgHom.ofLinearMap
    { toFun := fun c =>
        { toFun := rep c
          map_add' := map_add _
          map_smul' := fun x w => by
            simp only [RingHom.id_apply, hsm]
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }
      map_add' := fun c c' => by ext w; simp
      map_smul' := fun x c => by
        ext w
        simp [hsm, Algebra.smul_def, Module.End.mul_apply] }
    (by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])
  have hr : ∀ c w, r c w = rep c w := fun _ _ => rfl
  let s : C →ₐ[K] Matrix (Fin n) (Fin n) K := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r
  have hsinj : Function.Injective s := by
    intro c c' h
    have h' : r c = r c' := (LinearMap.toMatrixAlgEquiv b).injective h
    apply hinj
    ext w
    exact congrArg (fun g => g w) h'
  have hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
    ring
  have hsurj : Function.Surjective s :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj
  refine ⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩
  have h := LinearMap.toMatrix_mulVec_repr b b (r c) w
  exact h.symm

theorem UpperTheory.Gal.W2.fMat_of :
    UpperTheory.Gal.W2.FMat := by
  intro p _ D G L hm
  haveI := D.freeLa
  haveI := D.finLa
  have hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    ((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm
  have hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F := by
    rw [Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]
  exact exists_coords G.n L.rep L.rep_inj G.rankC hdim
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma hv_sub_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) :
    hv M (x - y) z = hv M x z - hv M y z := by
  unfold hv
  rw [Matrix.mulVec_sub, dotProduct_sub]

private lemma hv_smul_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M (c • x) z = c * hv M x z := by
  unfold hv
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma hv_smul_r {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M x (c • z) = star c * hv M x z := by
  unfold hv
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private lemma hv_J {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} (h : Jᴴ * M * J = M) (x y : Fin n → ℂ) :
    hv M (J *ᵥ x) (J *ᵥ y) = hv M x y := by
  unfold hv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h]

private lemma J_plus {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hJ : J * J = -1) (x : Fin n → ℂ) :
    J *ᵥ (x - t • J *ᵥ x) = t • (x - t • J *ᵥ x) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (J *ᵥ x) i * ht

private lemma of_plus_zero {n : ℕ} {t : ℂ} (ht : t * t = -1) {x y : Fin n → ℂ}
    (h : x - t • y = 0) : y = (-t) • x := by
  have hx : x = t • y := sub_eq_zero.mp h
  rw [hx, smul_smul, neg_mul, ht, neg_neg, one_smul]

private lemma eig_pos {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) {z : Fin n → ℂ} (hz : z ≠ 0)
    (hJz : J *ᵥ z = t • z) : 0 < (hv M z z).re := by
  have h1 := hp z hz
  rw [hJz, hv_smul_l, ← _root_.mul_assoc, neg_mul, ht, neg_neg, _root_.one_mul] at h1
  exact h1

private lemma core {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (ht : t * t = -1)
    (hJ : J * J = -1) (hP : Jᴴ * M * J = M)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) :
    (∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = t • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = t • z →
      ∀ x, J *ᵥ x = t • ((2 * (hv M x z / hv M z z)) • z - x) := by
  have hpos : ∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re := fun z hz hJz => eig_pos ht hp hz hJz
  have hall : (∀ x, x - t • J *ᵥ x = 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro h0
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    apply Matrix.ext_of_mulVec_single
    intro i
    simp only [hx]
    ext k
    by_cases h : k = i
    · subst h
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, h]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro hneg
    apply hall
    intro x
    by_contra hv0
    have h1 := hpos _ hv0 (J_plus ht hJ x)
    have h2 := hneg _ hv0
    linarith
  · rintro ⟨z, hz⟩
    by_contra hno
    push_neg at hno
    have h0 : ∀ x, x - t • J *ᵥ x = 0 := by
      intro x
      by_contra hv0
      exact hno _ hv0 (J_plus ht hJ x)
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [hv] at hz
    have h1 := hp z hz0
    rw [hx, hv_smul_l, ← _root_.mul_assoc, neg_mul_neg, ht, neg_one_mul, Complex.neg_re] at h1
    linarith
  · intro z hz hperp hJz x
    have hzz : hv M z z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    set c := hv M x z / hv M z z with hc
    set w := x - c • z with hw
    have hwz : hv M w z = 0 := by
      rw [hw, hv_sub_l, hv_smul_l, hc, div_mul_cancel₀ _ hzz, sub_self]
    have hJwz : hv M (J *ᵥ w) z = 0 := by
      have e1 := hv_J hP w z
      rw [hJz, hv_smul_r, hwz] at e1
      have ht0 : star t ≠ 0 := by
        intro h0
        rw [star_eq_zero] at h0
        rw [h0, zero_mul] at ht
        norm_num at ht
      exact (mul_eq_zero.mp e1).resolve_left ht0
    have hJw : J *ᵥ w = (-t) • w := by
      apply of_plus_zero ht
      by_contra hu
      have h1 := hpos _ hu (J_plus ht hJ w)
      have h2 := hperp _ hu (by rw [hv_sub_l, hv_smul_l, hwz, hJwz, mul_zero, sub_zero])
      linarith
    have hxw : x = w + c • z := by rw [hw, sub_add_cancel]
    rw [hxw, Matrix.mulVec_add, hJw, Matrix.mulVec_smul, hJz]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

theorem UpperTheory.Gal.W2.jLine_of :
    UpperTheory.Gal.W2.JLine := by
  intro n M J s hM hs hPJ
  obtain ⟨hJ, hP, hp⟩ := hPJ
  have ht : (s * Complex.I) * (s * Complex.I) = -1 := by
    rcases hs with rfl | rfl <;> simp
  have hp' : ∀ x, x ≠ 0 → 0 < (-(s * Complex.I) * hv M (J *ᵥ x) x).re := by
    intro x hx
    have h1 := hp x hx
    rwa [neg_mul] at h1
  exact core M J (s * Complex.I) ht hJ hP hp'
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem trace_conj {F : Type} [Field F] [NumberField F] [IsCMField F] (x : F) :
    Algebra.trace ℚ F (IsCMField.complexConj F x) = Algebra.trace ℚ F x := by
  let e : F ≃ₐ[ℚ] F := AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj F).toRingEquiv) (fun r => by simp)
  exact Algebra.trace_eq_of_algEquiv e x

private theorem trace_strip {F : Type} [Field F] [NumberField F] {a b : F}
    (h : ∀ x : F, Algebra.trace ℚ F (a * x) = Algebra.trace ℚ F (b * x)) : a = b := by
  have hnd := traceForm_nondegenerate ℚ F
  have : a - b = 0 := by
    apply hnd.1
    intro x
    show Algebra.trace ℚ F ((a - b) * x) = 0
    rw [sub_mul, map_sub, h, sub_self]
  exact sub_eq_zero.1 this

private theorem exists_trace_rep {F : Type} [Field F] [NumberField F] (f : F →+ ℚ) :
    ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) = f x := by
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm f.toRatLinearMap, fun x => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) f.toRatLinearMap x

private theorem sum_single {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    u = ∑ j, u j • (Pi.single j 1 : Fin n → F) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem form_ext {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) F}
    (h : ∀ u w : Fin n → F, Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (M *ᵥ u)) =
      Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (N *ᵥ u))) : M = N := by
  ext i j
  apply trace_strip
  intro x
  have := h (x • Pi.single j 1) (Pi.single i 1)
  have e : ∀ P : Matrix (Fin n) (Fin n) F,
      (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) ⬝ᵥ (P *ᵥ (x • Pi.single j 1)) = P i j * x := by
    intro P
    have e1 : (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) = (Pi.single i 1 : Fin n → F) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [e1, Matrix.mulVec_smul, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [mul_comm]
  rwa [e M, e N] at this

private theorem form_core {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    (B : (Fin n → F) →+ (Fin n → F) →+ ℚ)
    (hadj : ∀ (x : F) u w, B (x • u) w = B u (IsCMField.complexConj F x • w))
    (hskew : ∀ u w, B u w = - B w u)
    (hnd : ∀ u, (∀ w, B u w = 0) → u = 0) :
    ∃ A : Matrix (Fin n) (Fin n) F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj F))ᵀ = -A ∧
      ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
  have hrep : ∀ i j : Fin n, ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := fun i j =>
    exists_trace_rep (((AddMonoidHom.eval (Pi.single i 1 : Fin n → F)).comp B).comp
      (AddMonoidHom.mk' (fun x : F => x • (Pi.single j 1 : Fin n → F)) (fun a b => add_smul a b _)))
  choose A₀ hA₀ using hrep
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) F, ∀ i j x, Algebra.trace ℚ F (A i j * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := ⟨A₀, hA₀⟩
  have hterm : ∀ (u w : Fin n → F) i j, B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
      Algebra.trace ℚ F (IsCMField.complexConj F (w i) * (A i j * u j)) := by
    intro u w i j
    have e1 : B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
        B (IsCMField.complexConj F (w i) • (u j • (Pi.single j 1 : Fin n → F))) (Pi.single i 1) := by
      rw [hadj (IsCMField.complexConj F (w i)) (u j • _), IsCMField.complexConj_apply_apply]
    rw [e1, smul_smul, ← hA]
    congr 1
    ring
  have hform : ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
    intro u w
    conv_lhs => rw [sum_single u, sum_single w]

    simp only [map_sum, AddMonoidHom.finsetSum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, hterm]
  refine ⟨A, ?_, ?_, hform⟩
  · intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    exact hv (hnd v fun w => by rw [hform, hAv]; simp)
  · ext i j
    show IsCMField.complexConj F (A j i) = - A i j
    apply trace_strip
    intro x
    have h1 : Algebra.trace ℚ F (IsCMField.complexConj F (A j i) * x) =
        Algebra.trace ℚ F (A j i * IsCMField.complexConj F x) := by
      rw [← trace_conj (A j i * IsCMField.complexConj F x), map_mul (IsCMField.complexConj F), IsCMField.complexConj_apply_apply]
    rw [h1, hA, hadj, IsCMField.complexConj_apply_apply, hskew, ← hA, neg_mul, map_neg]

private theorem bc_skew {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La) (halt : ∀ x, E x x = 0)
    (u w : ℚ ⊗[ℤ] La) : E.baseChange ℚ u w = - E.baseChange ℚ w u := by
  have hs : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, neg_add]
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd, neg_add]
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [hs x y]
      simp [mul_comm]

private theorem exists_pure {La : Type} [AddCommGroup La] (v : ℚ ⊗[ℤ] La) :
    ∃ (N : ℕ) (x : La), N ≠ 0 ∧ N • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add a b ha hb =>
    obtain ⟨N, x, hN, hx⟩ := ha
    obtain ⟨M, y, hM, hy⟩ := hb
    refine ⟨N * M, M • x + N • y, mul_ne_zero hN hM, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  | tmul a x =>
    refine ⟨a.den, a.num • x, a.den_ne_zero, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, Rat.den_mul_eq_num]

private theorem bc_nondeg {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La)
    (hE : Function.Injective E) (v : ℚ ⊗[ℤ] La) (h : ∀ w, E.baseChange ℚ v w = 0) : v = 0 := by
  obtain ⟨N, x, hN, hx⟩ := exists_pure v
  have hx0 : x = 0 := by
    apply hE
    ext y
    have h1 := h ((1 : ℚ) ⊗ₜ[ℤ] y)
    have h2 : E.baseChange ℚ (N • v) ((1 : ℚ) ⊗ₜ[ℤ] y) = 0 := by simp [h1]
    rw [hx, LinearMap.BilinForm.baseChange_tmul] at h2
    simpa using h2
  rw [hx0, TensorProduct.tmul_zero] at hx
  have : (N : ℚ) • v = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hx
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)

theorem UpperTheory.Gal.W2.fForm_of :
    UpperTheory.Gal.W2.FForm := by
  intro p _ D G L kp σ hF
  let E := D.EF.baseChange ℚ
  let B : (Fin G.n → G.F) →+ (Fin G.n → G.F) →+ ℚ :=
    AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun w => E (kp.symm u) (kp.symm w)) (by intro a b; simp))
      (by intro a b; ext w; simp)
  have hB : ∀ u w, B u w = E (kp.symm u) (kp.symm w) := fun _ _ => rfl
  have hsc : ∀ (x : G.F) (u : Fin G.n → G.F),
      kp.symm (x • u) = L.rep (algebraMap G.F G.C x) (kp.symm u) := by
    intro x u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply, AlgEquiv.commutes]
    ext i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
  have hsm : ∀ (c : G.C) (u : Fin G.n → G.F), kp.symm (σ c *ᵥ u) = L.rep c (kp.symm u) := by
    intro c u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply]
  obtain ⟨A, hdet, hskew, hform⟩ := form_core B
    (by
      intro x u w
      rw [hB, hB, hsc, hsc, L.adj]
      show E _ (L.rep ((G.star _).unop) _) = _
      rw [G.star_F])
    (by intro u w; exact bc_skew D.EF D.alt _ _)
    (by
      intro u hu
      have h0 : kp.symm u = 0 := bc_nondeg D.EF D.nondeg _ fun w => by
        have := hu (kp w)
        rwa [hB, AddEquiv.symm_apply_apply] at this
      simpa using congrArg kp h0)
  have hform' : ∀ u w, E u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u)) := by
    intro u w
    have := hform (kp u) (kp w)
    rwa [hB, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at this
  refine ⟨A, hdet, hskew, hform', fun c => ?_⟩
  apply form_ext
  intro u w
  have hcj : (fun i => IsCMField.complexConj G.F (w i)) ⬝ᵥ
        (((σ c).map (IsCMField.complexConj G.F))ᵀ * A) *ᵥ u =
      (fun i => IsCMField.complexConj G.F ((σ c *ᵥ w) i)) ⬝ᵥ (A *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    congr 1
    ext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hcj, ← Matrix.mulVec_mulVec]
  have h1 := hform (σ (sh G c) *ᵥ u) w
  have h2 := hform u (σ c *ᵥ w)
  rw [← h1, ← h2, hB, hB, hsm, hsm]
  have h3 : sh G (sh G c) = c := G.star_star c
  have h4 := L.adj (sh G c) (kp.symm u) (kp.symm w)
  rw [h3] at h4
  exact h4
end
