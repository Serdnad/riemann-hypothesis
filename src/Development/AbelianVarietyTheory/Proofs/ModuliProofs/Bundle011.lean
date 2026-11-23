module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Data.Sym.Card
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isOpen_posDef_of_continuous {X n : Type} [TopologicalSpace X] [Fintype n]
    (M : X → Matrix n n ℝ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : n → ℝ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2)) :=
    (continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1,
      0 < dotProduct (star v) ((M x).mulVec v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)

theorem card_sym2_fin (h : ℕ) : Fintype.card (Sym2 (Fin h)) = h * (h + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

theorem exists_siegel_coordinates :
    ∀ h : ℕ, ∃ (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ), IsOpen B ∧ Convex ℝ B ∧ (∀ i j, Differentiable ℂ (fun b => τ b i j)) ∧ (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) ∧ ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm → (t.map Complex.im).PosDef → ∃! b, b ∈ B ∧ τ b = t := by
  intro h
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (card_sym2_fin h)
  let τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ :=
    fun b => Matrix.of fun i j => b (e s(i, j))
  have hτ : ∀ b i j, τ b i j = b (e s(i, j)) := fun _ _ _ => rfl
  have hsymm : ∀ b, (τ b).IsSymm := by
    intro b
    ext i j
    rw [Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]
  refine ⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩
  · apply isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)
    · refine continuous_matrix fun i j => ?_
      exact Complex.continuous_im.comp (continuous_apply (e s(i, j)))
    · intro b
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]
      rw [Sym2.eq_swap]
  · intro x hx y hy a b ha hb hab
    have key : (τ (a • x + b • y)).map Complex.im
        = a • (τ x).map Complex.im + b • (τ y).map Complex.im := by
      ext i j
      simp [hτ]
    change ((τ (a • x + b • y)).map Complex.im).PosDef
    rw [key]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by simpa using hab
      subst this
      simpa using hy
    · exact (Matrix.PosDef.smul hx ha').add_posSemidef
        (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)
  · intro i j
    exact differentiable_apply (𝕜 := ℂ) (e s(i, j))
  · intro b hb
    exact ⟨hsymm b, hb⟩
  · intro t ht hp
    let f : Sym2 (Fin h) → ℂ := Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩
    have hf : τ (fun k => f (e.symm k)) = t := by
      ext i j
      change f (e.symm (e s(i, j))) = t i j
      rw [Equiv.symm_apply_apply]
      rfl
    refine ⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩
    · change ((τ (fun k => f (e.symm k))).map Complex.im).PosDef
      rw [hf]; exact hp
    · rintro b ⟨-, hb⟩
      funext k
      obtain ⟨z, rfl⟩ := e.surjective k
      induction z using Sym2.ind with
      | _ i j =>
        rw [Equiv.symm_apply_apply]
        exact congrFun (congrFun hb i) j

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eval₂_scale_of_isHomogeneous {o σ S : Type} [CommRing o] [CommRing S] (f : o →+* S)
    (g : σ → S) (u : S) {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ f (fun j => g j * u) F = MvPolynomial.eval₂ f g F * u ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, _root_.mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

theorem exists_ker_eq_dehomogenisation {o σ : Type} [CommRing o] (I : Ideal (MvPolynomial σ o))
    (i : σ) (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) :
    ∃ ψ : MvPolynomial σ o →+*
        Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)),
      (∀ c, ψ (MvPolynomial.C c) = algebraMap (MvPolynomial σ o ⧸ I) _
        (Ideal.Quotient.mk I (MvPolynomial.C c))) ∧
      RingHom.ker ψ = I ⊔ Ideal.span {MvPolynomial.X i - 1} := by
  classical
  let x := Ideal.Quotient.mk I (MvPolynomial.X i)
  let L := Localization.Away x
  let g : MvPolynomial σ o →+* L :=
    (algebraMap (MvPolynomial σ o ⧸ I) L).comp (Ideal.Quotient.mk I)
  let u : L := IsLocalization.Away.invSelf x
  let ψ : MvPolynomial σ o →+* L :=
    MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u)

  have hg : ∀ F : MvPolynomial σ o,
      MvPolynomial.eval₂ (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j)) F = g F := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [MvPolynomial.eval₂_add, hp, hq, map_add (f := _)]
    | mul_X p j hp => rw [MvPolynomial.eval₂_mul, hp, MvPolynomial.eval₂_X, map_mul]
  have hxu : g (MvPolynomial.X i) * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨ψ, fun c => by exact MvPolynomial.eval₂Hom_C _ _ c, le_antisymm ?_ ?_⟩
  ·
    let J := I ⊔ Ideal.span {MvPolynomial.X i - 1}
    let q : MvPolynomial σ o ⧸ I →+* MvPolynomial σ o ⧸ J :=
      Ideal.Quotient.lift I (Ideal.Quotient.mk J)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_left (a := I) ha))
    have hq1 : q x = 1 := by
      change Ideal.Quotient.mk J (MvPolynomial.X i) = 1
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_right (a := I) (Ideal.subset_span (Set.mem_singleton _))
    have hunit : IsUnit (q x) := by rw [hq1]; exact isUnit_one
    let θ : L →+* MvPolynomial σ o ⧸ J := IsLocalization.Away.lift x hunit
    have hθ : ∀ a, θ (algebraMap _ L a) = q a := IsLocalization.Away.lift_eq x hunit
    have hθu : θ u = 1 := by
      have h := congrArg θ hxu
      rw [map_mul, map_one] at h
      have h' : θ (g (MvPolynomial.X i)) = 1 := by
        change θ (algebraMap _ L x) = 1
        rw [hθ, hq1]
      rwa [h', _root_.one_mul] at h
    have hcomp : θ.comp ψ = Ideal.Quotient.mk J := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.C c)) = _
        rw [MvPolynomial.eval₂Hom_C]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.C c))) = _
        rw [hθ]
        rfl
      · intro j
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X j)) = _
        rw [MvPolynomial.eval₂Hom_X', map_mul, hθu, _root_.mul_one]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.X j))) = _
        rw [hθ]
        rfl
    intro F hF
    rw [RingHom.mem_ker] at hF
    have h0 : Ideal.Quotient.mk J F = 0 := by
      rw [← hcomp, RingHom.comp_apply, hF, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · apply sup_le
    ·
      intro F hF

      rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      have h1 := eval₂_scale_of_isHomogeneous (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j)) u (MvPolynomial.homogeneousComponent_isHomogeneous e F)
      rw [MvPolynomial.coe_eval₂Hom, h1, hg]
      have h2 : Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent e F) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hI F hF e)
      change algebraMap _ L (Ideal.Quotient.mk I _) * _ = 0
      rw [h2, map_zero, zero_mul]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      change MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X i) - 1 = 0
      rw [MvPolynomial.eval₂Hom_X', hxu, sub_self]

theorem dehomogenisation_isRadical_and_torsionFree :
    ∀ (o σ : Type) [CommRing o] (I : Ideal (MvPolynomial σ o)) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (I.IsRadical → (I ⊔ Ideal.span {MvPolynomial.X i - 1}).IsRadical) ∧ ((∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1} → F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  intro o σ _ I i hI
  obtain ⟨ψ, hC, hker⟩ := exists_ker_eq_dehomogenisation I i hI
  rw [← hker]
  refine ⟨fun hrad => ?_, fun htf c F hc hF => ?_⟩
  ·
    have : IsReduced (MvPolynomial σ o ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
    rintro F ⟨n, hn⟩
    rw [RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  ·
    rw [RingHom.mem_ker, map_mul] at hF
    rw [RingHom.mem_ker]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective
      (S := Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)))
      (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X i))) (ψ F)
    simp only at hs
    rw [← hs, hC, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hF
    obtain ⟨⟨_, k, rfl⟩, hm⟩ := hF
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hIG : MvPolynomial.C c * (MvPolynomial.X i ^ k * G) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      simp only [map_mul, map_pow]
      ring
    have hG : MvPolynomial.X i ^ k * G ∈ I := htf c _ hc hIG
    rw [← hs, IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.X i) ^ k * Ideal.Quotient.mk I G = 0
    rw [← map_pow, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SquareDensity

theorem exists_sq_add_sub_dvd {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ w : R, x ∣ w ∧ x ^ n ∣ w ^ 2 + w - x := by
  induction n with
  | zero => exact ⟨0, dvd_zero _, by simp⟩
  | succ n ih =>
    obtain ⟨w, ⟨c, hc⟩, hw⟩ := ih
    refine ⟨x - w ^ 2, ⟨1 - c * w, by rw [hc]; ring⟩, ?_⟩
    have h : (x - w ^ 2) ^ 2 + (x - w ^ 2) - x = (w ^ 2 + w - x) * (x * (c * w - c - 1)) := by
      have : x * (c * w - c - 1) = w ^ 2 - w - x := by rw [hc]; ring
      rw [this]; ring
    rw [h, pow_succ]
    exact mul_dvd_mul hw (dvd_mul_right _ _)

theorem dvd_aeval_sub_aeval {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    simp only [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p i hp =>
    have := dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem eval_aeval {K σ : Type*} [CommRing K] (Φ : MvPolynomial σ K) (a : σ → Polynomial K)
    (t : K) :
    (MvPolynomial.aeval a Φ).eval t = MvPolynomial.eval (fun i => (a i).eval t) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_zero_of_sq {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by
  set x : Polynomial (Polynomial ℤ) :=
    Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx
  obtain ⟨w, -, hw⟩ := exists_sq_add_sub_dvd x (d + 1)
  set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy
  obtain ⟨Φ, hd, hΦ⟩ := hΨ (max F.natDegree (y ^ 2).natDegree + 1)
  set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha
  set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb
  have hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) +
      Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X := by
    intro i
    have h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4 := rfl
    simp only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_one]
    split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring
  have hb0 : MvPolynomial.aeval b Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K))
      Int.cast_injective fun k => ?_
    show (MvPolynomial.aeval b Φ).eval (k : K) = 0
    rw [eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]
    · congr 2
      funext i
      simp only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      exact Polynomial.eval_intCast_map (Int.castRingHom K) _ k
    · exact lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _))
        (Nat.lt_succ_self _)
  have hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ := by
    rw [← sub_zero (MvPolynomial.aeval a Φ), ← hb0]
    apply dvd_aeval_sub_aeval
    intro i
    have h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2 := by
      have h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4) := by rw [hy]; ring
      rw [h2, map_pow]
      exact ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _
    have h3 := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i
    have h4 := Polynomial.map_dvd (Int.castRingHom K) h3
    simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub,
      Polynomial.map_sub] using h4
  have hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1 := by
    refine MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_
    rw [hai]
    compute_degree
  have ha0 : MvPolynomial.aeval a Φ = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [Polynomial.natDegree_X_pow]; omega)
  have h := eval_aeval Φ a (1 / 4)
  rw [ha0, Polynomial.eval_zero] at h
  rw [hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]
  congr 2
  funext i
  rw [hai]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coeff_sub, Int.cast_sub]
  ring

theorem eq_sum_monomial (F : Polynomial ℤ) (r : ℕ) (h : F.natDegree < r) :
    F = ∑ i : Fin r, Polynomial.monomial (i : ℕ) (F.coeff i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i)) r]
  exact F.as_sum_range' r h

theorem exists_det_polynomial {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    ∃ Φ : MvPolynomial (Fin r) K, Φ.IsHomogeneous m ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        φ (Polynomial.aeval U F).det =
          MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ := by
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K) := fun j k =>
    ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i
  have hM : ∀ j k, (M j k).IsHomogeneous 1 := fun j k =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _
  refine ⟨M.det, ?_, fun F hF => ?_⟩
  · rw [Matrix.det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
      fun i _ => hM _ _
    have h2 := h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)
    simpa using h2
  · rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext j k
    rw [Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range
      (fun i => F.coeff i • U ^ i) r]
    change φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _
      (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)

    rw [Matrix.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]

end SquareDensity

theorem sq_eq_det_aeval_of_sq : ∀ (l : ℕ) [Fact l.Prime] (m g : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (D : Polynomial ℤ → ℚ), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → (∀ G, ((D (G ^ 2) : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])) → (∀ F H, Polynomial.aeval U H = 0 → D (F + H) = D F) → ∀ F, ((D F ^ 2 : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m g U D hD hsq _ F
  refine sub_eq_zero.1 (SquareDensity.eq_zero_of_sq
    (fun F => ((D F ^ 2 : ℚ) : ℚ_[l]) - ((Polynomial.aeval U F).det : ℤ_[l]))
    (max (2 * g) m) (fun r => ?_) (fun G => ?_) F)
  · obtain ⟨Φ, hΦ, hDΦ⟩ := hD r
    obtain ⟨Θ, hΘ, hdet⟩ := SquareDensity.exists_det_polynomial (PadicInt.Coe.ringHom (p := l)) U r
    refine ⟨(MvPolynomial.map (algebraMap ℚ ℚ_[l]) Φ) ^ 2 - Θ, ?_, fun F hF => ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ?_ hΘ.totalDegree_le)
      have := ((hΦ.map (algebraMap ℚ ℚ_[l])).pow 2).totalDegree_le
      rwa [mul_comm] at this
    · rw [map_sub, map_pow, ← hdet F hF, Rat.cast_pow]
      congr 2
      have h1 := hDΦ fun i => F.coeff i
      rw [← SquareDensity.eq_sum_monomial F r hF] at h1
      rw [h1, MvPolynomial.eval_map]
      have h2 := MvPolynomial.eval₂_comp_left (algebraMap ℚ ℚ_[l]) (RingHom.id ℚ)
        (fun i : Fin r => ((F.coeff i : ℤ) : ℚ)) Φ
      simpa [Function.comp_def] using h2
  · simp only [map_pow, Matrix.det_pow, Rat.cast_pow, hsq G, PadicInt.coe_pow, sub_self]

end GlobalTheory
end
