module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace GridSeparation

theorem norm_eval_le_of_torus {e : ℕ} (G : MvPolynomial (Fin e) ℤ) (ζ : Fin e → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := by
  rw [eval_map, eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  simp [hζ]

theorem grid_finite (e m : ℕ) (hm : 0 < m) : {ζ : Fin e → ℂ | ∀ i, ζ i ^ m = 1}.Finite := by
  have h1 : {x : ℂ | x ^ m = 1}.Finite :=
    (Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hm] using hx
  convert Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1
  ext ζ
  simp [Set.mem_pi]

theorem norm_of_pow_eq_one {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ^ m = 1) : ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])

theorem proof (hNL : NormalLocusRep.Statement) (hFN : FibreNormBound.Statement)
    (hRG : RootGridLower.Statement) : GridSeparation.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hBir hA
  obtain ⟨df, f, hf, hfP, hrep⟩ := hNL K ι Ω y D hV hBir
  obtain ⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩ := hFN K ι Ω y D A df f hV hBir hA hf hfP
  set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG
  have hSG1 : 1 ≤ SG := by
    have : 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hX : 1 ≤ 2 * B * SG := by nlinarith
  refine ⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩
  set m := G.totalDegree + c * (τ + 1) + 1 with hm
  have hm0 : 0 < m := by omega
  set Z := ((grid_finite (D + 1) m hm0).toFinset.filter
    fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ
  have hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
      ∀ z ∈ Fib ζ, z ∈ Z := fun ζ hζ hG z hz =>
    Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩
  have hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 := by
    intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hζg, hGζ⟩ := Finset.mem_filter.mp hζ
    have hζg' : ∀ i, ζ i ^ m = 1 := (Set.Finite.mem_toFinset _).mp hζg
    exact hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ
  refine ⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩
  intro u hu hu0
  obtain ⟨F, hF0, hFdeg, hFb⟩ := hnorm τ u hu hu0
  by_contra hcon
  obtain ⟨ζ, hζm, hζ1⟩ := hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by
    have h1 := degreeOf_mul_le i G F
    have h2 := degreeOf_le_totalDegree G i
    have h3 := hFdeg i
    omega
  have hζn : ∀ i, ‖ζ i‖ = 1 := fun i => norm_of_pow_eq_one hm0 (hζm i)
  rw [map_mul, eval_mul, norm_mul] at hζ1
  have hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hζ1
    linarith
  set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hFle := hFb ζ hζn hGζ E hE0.le fun z hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩ :=
      hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2
    refine ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩
    by_contra hlt
    exact hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩
  have hEX : E * (2 * B * SG) ^ (τ + 1) = 1 := by
    have : -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG)) := by
      push_cast
      ring
    rw [hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow,
      inv_mul_cancel₀ (by linarith), one_pow]
  have hE1 : E ≤ 1 := by
    have : 1 ≤ (2 * B * SG) ^ (τ + 1) := one_le_pow₀ hX
    nlinarith
  have hEn : E ^ n ≤ E := pow_le_of_le_one hE0.le hE1 (by omega)
  have hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG := by
    have := norm_eval_le_of_torus G ζ hζn
    linarith
  have hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1) := by
    rw [show 2 * B * SG = (2 * SG) * B by ring, mul_pow]
    have hB0 : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
    have : 2 * SG ≤ (2 * SG) ^ (τ + 1) := le_self_pow₀ (by linarith) (by omega)
    nlinarith
  have hBp : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
  have hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E := by
    calc _ ≤ B ^ (τ + 1) * E ^ n := hFle
      _ ≤ B ^ (τ + 1) * E := mul_le_mul_of_nonneg_left hEn hBp
  have key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1 := by
    calc 2 * (SG * (B ^ (τ + 1) * E)) = (2 * SG * B ^ (τ + 1)) * E := by ring
      _ ≤ (2 * B * SG) ^ (τ + 1) * E := mul_le_mul_of_nonneg_right hpow hE0.le
      _ = 1 := by rw [mul_comm, hEX]
  have hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖ := norm_nonneg _
  have : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤
      SG * (B ^ (τ + 1) * E) :=
    mul_le_mul hGle hFn hFnn (by linarith)
  linarith

end GridSeparation

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]


omit [∀ κ, Fintype (ι κ)] in
theorem shift_mem (y : (Σ κ, ι κ) → Ω) (c : ∀ κ, ι κ) (a a' : K → ℤ) (τ τ' : ℕ) (e : K → ℕ)
    (he : ∀ κ, (τ : ℤ) * a κ + e κ = τ' * a' κ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s ∈ chartLatNm y a' τ' := by
  intro c' hc'
  have hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c' := fun κ =>
    Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩
  have hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹ := by
    intro κ
    rw [← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]
  have heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ := by
    simp only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)
  exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩

theorem proof (h₁ : NmSectionsFinite.Statement) (h₂ : SecMRankBound.Statement) :
    NmSectionsRankBound.Statement := by
  intro K _ ι _ Ω _ y D a hvar hbir
  classical

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  choose c hc using hy
  set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb
  have hb1 : ∀ κ, 1 ≤ b κ := fun κ => Nat.le_add_left 1 _
  have hab : ∀ κ, a κ ≤ (b κ : ℤ) := fun κ => by simp only [hb]; push_cast; omega
  obtain ⟨J, _, d, e, τ₁, -, hgen⟩ := h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0
  obtain ⟨hfin, C, hC0, hC⟩ := h₂ K ι Ω y D b hvar hb1

  have hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧
      (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤
        Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
    intro τ hτ
    let M : J → AddSubgroup Ω := fun j => secM y (fun κ => (τ - d j) * b κ)
    let Φ : (∀ j, M j) →ₗ[ℤ] Ω :=
      ∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))
    have hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
      exact ⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩
    let f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ :=
      LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap
        (fun x => hle x x.2)
    have hinj : Function.Injective f := fun x x' hxx => by
      have h := congrArg Subtype.val hxx
      exact Subtype.ext h
    have : ∀ j, Module.Finite ℤ (M j) := fun j => hfin (τ - d j)
    have : ∀ j, Module.IsTorsionFree ℤ (M j) := fun j =>
      Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)
    refine ⟨Module.Finite.of_injective f hinj, ?_⟩
    have h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j) :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans
        ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))
    calc (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ)
        ≤ ∑ j, (Module.finrank ℤ (M j) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _j : J, C * ((τ : ℝ) + 1) ^ D := by
          refine Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_
          gcongr
          exact_mod_cast Nat.sub_le τ (d j)
      _ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

  have hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁),
      Function.Injective f := by
    intro τ
    set τ' := max τ τ₁
    set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat
    have hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ) := by
      intro κ
      have h0 : (τ : ℤ) * a κ ≤ τ' * b κ :=
        calc (τ : ℤ) * a κ ≤ τ * b κ := mul_le_mul_of_nonneg_left (hab κ) (by positivity)
          _ ≤ τ' * b κ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left τ τ₁) (by positivity)
      simp only [ex]
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ
    have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)
    let F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ' :=
      ((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _
        (fun x => shift_mem y c a _ τ τ' ex hex x.2)
    refine ⟨F.toIntLinearMap, fun x x' hxx => ?_⟩
    have h : u * (x : Ω) = u * x' := congrArg Subtype.val hxx
    exact Subtype.ext (mul_left_cancel₀ hu h)
  refine ⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩
  · obtain ⟨f, hf⟩ := hmap τ
    have := (hbig (max τ τ₁) (le_max_right _ _)).1
    exact Module.Finite.of_injective f hf
  · obtain ⟨f, hf⟩ := hmap τ
    obtain ⟨hF, hR⟩ := hbig (max τ τ₁) (le_max_right _ _)
    have h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤
        Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁)) := by
      exact_mod_cast LinearMap.finrank_le_finrank_of_injective hf
    have h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1) := by
      rcases le_total τ τ₁ with h | h
      · rw [max_eq_right h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
      · rw [max_eq_left h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
    calc (Module.finrank ℤ (chartLatNm y a τ) : ℝ)
        ≤ Fintype.card J * C * (((max τ τ₁ : ℕ) : ℝ) + 1) ^ D := h1.trans hR
      _ ≤ Fintype.card J * C * ((((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)) ^ D) := by
          gcongr
      _ = Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D * ((τ : ℝ) + 1) ^ D := by rw [mul_pow]; ring

end NmSectionsRankBound

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PointHeightFS.Statement : Prop :=
  ∀ I : AllFam, I.IsFamily → hhOf I 0 = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KrullDimMatAct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (J : Type) [Fintype J] (x : J → Ω) (B : Matrix J J ℚ), IsInvMat B →
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ (matAct B x)) = ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def MetricTransportSmooth.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    IsInvMat B → IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) → IsSmoothMetric m'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockIdeal (x x' : Ix κ → Ω) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x x')

def blockLine (m : ConeMetric (C := ℂ) (ι := Ix κ)) (k₀ : Fin 2) :
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) where
  a := Pi.single k₀ 1
  h z := m.ρ fun p : Ix κ => z ⟨k₀, p.2⟩
  pos z hz := m.pos _ fun h0 => by
    obtain ⟨i, hi⟩ := hz k₀
    exact hi (congrFun h0 ⟨(), i⟩)
  smul c z _ := by
    have e : (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = c k₀ • fun p : Ix κ => z ⟨k₀, p.2⟩ := rfl
    show m.ρ (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = _
    rw [e, m.smul, Finset.prod_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp

def twoBlockList (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) :
    Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) :=
  fun j => if (j : ℕ) < i then blockLine m 0 else blockLine m' 1

def twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) : ℝ :=
  I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D i) -
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D (i + 1))

def twoBlockStep (x x' : Ix κ → Ω) (a b : ℕ) : ℝ :=
  Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)

theorem twoBlockList_zero (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D 0 = fun _ => blockLine m' 1 := by
  funext j
  simp [twoBlockList]

theorem twoBlockList_last (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D (D + 1) = fun _ => blockLine m 0 := by
  funext j
  simp [twoBlockList, j.2]

theorem sum_twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x x' m m' D i =
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m' 1) -
        I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m 0) := by
  unfold twoBlockCoeff
  rw [Finset.sum_range_sub', twoBlockList_zero, twoBlockList_last]

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def linPullMetric {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ)
    (hN : ∀ u : J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) : ConeMetric ℂ J where
  ρ u := (fsMetric (ι := κ)).ρ (fun i => ∑ j, (N i j : ℂ) * u j)
  pos u hu := (fsMetric (ι := κ)).pos _ fun h => hu (hN u h)
  smul c u := by
    have : (fun i => ∑ j, (N i j : ℂ) * (c • u) j) = c • fun i => ∑ j, (N i j : ℂ) * u j := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, (fsMetric (ι := κ)).smul]

def BlockImageMetrics.Statement : Prop :=
  (∀ (κ J : Type) [Fintype κ] [Fintype J] (N : Matrix κ (Ix J) ℤ)
      (hN : ∀ u : Ix J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) (P : Ideal (MRing (GlobalTheory J))),
      IsSemipositiveRel ⊥ P (HermLine.ofCone (linPullMetric N hN))) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K) (P : Ideal (MRing ι)),
      IsSemipositiveRel ⊥ P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (unitDeg k₀))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def TwoBlockFnField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B →
      blockFnField (ι := FinTwoTypeFamily κ) (pair x (matAct B x)) = blockFnField (ι := GlobalTheory κ) x ∧
        blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
