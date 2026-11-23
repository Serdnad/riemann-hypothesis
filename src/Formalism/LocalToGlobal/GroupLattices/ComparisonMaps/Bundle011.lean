module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle080
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.Bundle001
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.HRatInvOfTriv
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

section Local

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq] {k : ℕ}

theorem den_one (π : W) (hπ : Irreducible π) (x : Qq) :
    ∃ (n : ℕ) (c : W), algebraMap W Qq π ^ n * x = algebraMap W Qq c := by
  obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors W) x
  have hs0 : (s : W) ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  refine ⟨n, ((u⁻¹ : Wˣ) : W) * c, ?_⟩
  simp only at hs
  rw [hu, map_mul, map_pow] at hs
  have hu' : algebraMap W Qq (u : W) * algebraMap W Qq ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul]
  linear_combination algebraMap W Qq ((u⁻¹ : Wˣ) : W) * hs - algebraMap W Qq π ^ n * x * hu'

theorem den_mat (π : W) (hπ : Irreducible π) (h : Matrix (Fin k) (Fin k) Qq) :
    ∃ (N : ℕ) (H : Matrix (Fin k) (Fin k) W), algebraMap W Qq π ^ N • h = H.map (algebraMap W Qq) := by
  choose nn cc hnc using fun i j => den_one π hπ (h i j)
  refine ⟨∑ i, ∑ j, nn i j, Matrix.of fun i j => π ^ (∑ i, ∑ j, nn i j - nn i j) * cc i j, ?_⟩
  ext i j
  have hle : nn i j ≤ ∑ i, ∑ j, nn i j :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (nn i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, nn i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ i))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, ← hnc i j]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem colSpan_mul_le (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) :
    colSpan W (g * U.map (algebraMap W Qq)) ≤ colSpan W g := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have h : (fun i => (g * U.map (algebraMap W Qq)) i c) = ∑ b, U b c • (fun i => g i b) := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun i => (g * U.map (algebraMap W Qq)) i c) ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c)
  rw [h]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem colSpan_mul_unit (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) (hU : IsUnit U.det) :
    colSpan W (g * U.map (algebraMap W Qq)) = colSpan W g := by
  apply le_antisymm (colSpan_mul_le g U)
  have h := colSpan_mul_le (g * U.map (algebraMap W Qq)) U⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv U hU, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one] at h

theorem det_one_add_unit (π : W) (hπ : Irreducible π) (D : Matrix (Fin k) (Fin k) W) : IsUnit (1 + π • D).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hπ0 : IsLocalRing.residue W π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have h1 : (IsLocalRing.residue W).mapMatrix (1 + π • D) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hπ0, zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Matrix.det_one]
  exact one_ne_zero

theorem approx_local (π : W) (hπ : Irreducible π) (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    ∃ N : ℕ, ∀ N', N ≤ N' → ∀ (A : Matrix (Fin k) (Fin k) Qq) (C : Matrix (Fin k) (Fin k) W),
      A = g + algebraMap W Qq π ^ N' • C.map (algebraMap W Qq) → colSpan W A = colSpan W g ∧ IsUnit A.det := by
  obtain ⟨N, H, hH⟩ := den_mat π hπ g⁻¹
  refine ⟨N + 1, fun N' hN A C hA => ?_⟩
  have hU : IsUnit (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := det_one_add_unit π hπ _
  have hAU : A = g * (1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq) := by
    rw [hA, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, map_pow, ← hH,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.one_mul, smul_smul, smul_smul]
    congr 2
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  refine ⟨by rw [hAU]; exact colSpan_mul_unit g _ hU, ?_⟩
  rw [hAU, Matrix.det_mul]
  refine hg.mul ?_
  have h2 : ((1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq)).det =
      algebraMap W Qq (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact hU.map _

end Local

variable {p : ℕ} (G : GAtP p) {E : Type} [Field E] (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)

def WeakApprox : Prop :=
  ∀ (x : ∀ v, G.P.Qq v) (N : ℕ), ∃ a : E, ∀ v, ∃ c : G.P.W v,
    iw v a = x v + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c

theorem ratTup_of_weak (h : WeakApprox G iw) : RatTup G iw := by
  intro L hL
  by_cases hne : Nonempty (Fin G.P.nV)
  swap
  · exact ⟨1, fun v => (hne ⟨v⟩).elim⟩
  choose g hg hLg using hL
  have := fun v => (G.P.setting v).frac_alt
  choose N hN using fun v => approx_local (p : G.P.W v) (G.P.setting v).p_unif (g v) (hg v)
  choose a c hac using fun x y => h (fun v => g v x y) (∑ v, N v)
  have key : ∀ v, colSpan (G.P.W v) ((Matrix.of a).map (iw v)) = colSpan (G.P.W v) (g v) ∧
      IsUnit ((Matrix.of a).map (iw v)).det := fun v =>
    hN v (∑ v, N v) (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
      ((Matrix.of a).map (iw v)) (fun x y => c x y v) (by
        ext x y
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_natCast]
        exact hac x y v)
  obtain ⟨v0⟩ := hne
  have hdet : IsUnit (Matrix.of a).det := by
    have h1 := (key v0).2
    have h2 : ((Matrix.of a).map (iw v0)).det = iw v0 (Matrix.of a).det := by
      rw [RingHom.map_det]; rfl
    rw [h2] at h1
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    exact h1 (by rw [h0, map_zero])
  exact ⟨Matrix.nonsingInvUnit (Matrix.of a) hdet, fun v => by rw [hLg v]; exact (key v).1.symm⟩

end Formalism.L2.G.Cmp
end
end

section

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain WithZero

section CRT

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem exists_prime_to_le (P : HeightOneSpectrum R) (d : R) (hd : d ≠ 0) :
    ∃ s : R, s ∉ P.asIdeal ∧ ∀ v : HeightOneSpectrum R, v ≠ P → v.intValuation s ≤ v.intValuation d := by
  classical
  have hI : (Ideal.span {d} : Ideal R) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  let S : Finset (HeightOneSpectrum R) := (Ideal.finite_factors hI).toFinset ∪ {P}
  let n : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v = P then 1 else n v) (fun v _ => v.prime)
    (fun v _ v' _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then 1 else 0)
  refine ⟨y, ?_, fun v hv => ?_⟩
  · intro hyP
    have h1 := hy P (Finset.mem_union_right _ (Finset.mem_singleton_self P))
    simp only [↓reduceIte, pow_one] at h1
    have h2 : (1 : R) ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hyP h1
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · by_cases hvd : v.asIdeal ∣ Ideal.span {d}
    · have hvS : v ∈ S := Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hvd)
      have h1 := hy v hvS
      simp only [if_neg hv, sub_zero] at h1
      rw [v.intValuation_if_neg hd]
      exact (v.intValuation_le_pow_iff_mem y (n v)).2 h1
    · have h3 : v.intValuation d = 1 := by
        apply le_antisymm (v.intValuation_le_one d)
        by_contra hlt
        exact hvd ((v.intValuation_lt_one_iff_dvd d).1 (lt_of_not_ge hlt))
      rw [h3]
      exact v.intValuation_le_one y

end CRT

variable {D : D7}

theorem exists_den (u : D.what₂.Word) (x : ((D.fm u).lat 0).V) :
    ∃ d : 𝓞 D.what₂.LL, d ≠ 0 ∧ d • x ∈ ((D.fm u).lat 0).L :=
  _root_.UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den u x

theorem locWBack_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWBack T := by
  intro u w x hx
  have key : ∀ (r : 𝓞 D.what₂.LL) (v : ((D.fm u).lat 0).V), r • v = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) • v :=
    fun r v => (algebraMap_smul D.what₂.LL r v).symm
  obtain ⟨d, hd0, hdL⟩ := exists_den u x
  obtain ⟨s, hsP, hsv⟩ := exists_prime_to_le (D.plEq w) d hd0
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ Submodule.zero_mem _)
  have hsL : s • x ∈ ((D.fm u).lat 0).L := by
    refine (((T u).val0).lat (s • x)).2 ?_
    intro w' c B hB
    by_cases hw : w' = w
    · subst hw
      have hsint : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (D.plEq w').intValuation_le_one s
      obtain ⟨P, hP, hPx⟩ := hx c B hB
      refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) • P, intSpan_smul w' _ _ hsint hP, fun t => ?_⟩
      rw [key, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
    · have hne : D.plEq w' ≠ D.plEq w := fun h => hw (D.plEq.injective h)
      have hdne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        simpa using hd0
      set q : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL s / algebraMap (𝓞 D.what₂.LL) D.what₂.LL d with hq
      have hqint : q ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, hq, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        have hdv : (D.plEq w').intValuation d ≠ 0 := (D.plEq w').intValuation_ne_zero d hd0
        rw [div_le_one₀ (zero_lt_iff.2 hdv)]
        exact hsv _ hne
      have hsx : s • x = q • (d • x) := by
        rw [key, key, smul_smul, hq, div_mul_cancel₀ _ hdne]
      obtain ⟨P, hP, hPx⟩ := (((T u).val0).lat (d • x)).1 hdL w' c B hB
      refine ⟨D.what₂.embLL q • P, intSpan_smul w' _ q hqint hP, fun t => ?_⟩
      rw [hsx, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]

  have hsu : (D.plEq w).intValuation s = 1 := by
    apply le_antisymm ((D.plEq w).intValuation_le_one s)
    by_contra hlt
    exact hsP (((D.plEq w).intValuation_lt_one_iff_mem s).1 (lt_of_not_ge hlt))
  have hsne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by simpa using hs0
  have htint : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
    rw [val_nonneg_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hsu, inv_one]
  have hx' : x = (⟨_, htint⟩ : intW D.what₂.places w) • (s • x) := by
    rw [Subring.smul_def, key, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsL)

theorem locWCrit_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWCrit T :=
  locWCrit_of T (locWBack_proved T)

end Formalism.L2.G.Cmp
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems NumberField IsDedekindDomain

section Gen

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)
variable {V W T : Type} [AddCommGroup V] [Module LL V] [AddCommGroup W] [Module Kf W]
  (ev : T → W →ₗ[Kf] Kf) (φ : V →+ W)

theorem span_inv (hsep : ∀ F : W, (∀ t, ev t F = 0) → F = 0)
    (hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x) (hval : ∀ x, IsRat e ev (φ x))
    (S : Set (W →ₗ[Kf] W)) (hT : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x))
    {ξ : W} (hξ : ξ ∈ Submodule.span Kf (Set.range φ)) (hinv : ∀ Tm ∈ S, Tm ξ = ξ) :
    ξ ∈ Submodule.span Kf (φ '' {x | ∀ Tm ∈ S, Tm (φ x) = φ x}) := by
  let _ : Algebra LL Kf := e.toAlgebra
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hξ
  set C : Submodule LL Kf := Submodule.span LL (Set.range fun x : c.support => c x) with hC
  have : FiniteDimensional LL C := FiniteDimensional.span_of_finite LL (Set.finite_range _)
  let κ := Module.finBasis LL C
  have hext : ∀ j, ∃ g : Kf →ₗ[LL] LL, g.comp C.subtype = κ.coord j := fun j => LinearMap.exists_extend (κ.coord j)
  choose π hπ using hext
  have hcx : ∀ x ∈ c.support, c x = ∑ j, e (π j (c x)) * (κ j : Kf) := by
    intro x hx
    have hmem : c x ∈ C := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h1 := κ.sum_repr ⟨c x, hmem⟩
    have h2 : ∀ j, π j (c x) = κ.repr ⟨c x, hmem⟩ j := fun j => by
      have := LinearMap.congr_fun (hπ j) ⟨c x, hmem⟩
      simpa using this
    conv_lhs => rw [show c x = ((⟨c x, hmem⟩ : C) : Kf) from rfl, ← h1]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2, Submodule.coe_smul, Algebra.smul_def]
    rfl
  let ξj : Fin (Module.finrank LL C) → V := fun j => c.sum fun x a => π j a • x
  have hdec : (c.sum fun x a => a • φ x) = ∑ j, (κ j : Kf) • φ (ξj j) := by

    simp only [ξj, Finsupp.sum, map_sum, hsm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h1 : c x • φ x = ∑ j, ((κ j : Kf) * e (π j (c x))) • φ x := by
      conv_lhs => rw [hcx x hx]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    exact h1
  rw [hdec]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ξj j, ?_, rfl⟩)
  intro Tm hTm

  choose y hy using hT Tm hTm
  have hzero : ∑ j, (κ j : Kf) • φ (y (ξj j) - ξj j) = 0 := by
    simp only [map_sub, hy, smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ x, (κ x : Kf) • Tm (φ (ξj x)) = Tm (∑ x, (κ x : Kf) • φ (ξj x)) := by

      rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => (map_smul Tm _ _).symm
    rw [h2, ← hdec, hinv Tm hTm, sub_self]
  have hli : LinearIndependent LL fun j => (κ j : Kf) :=
    κ.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hφz : φ (y (ξj j) - ξj j) = 0 := by
    refine hsep _ fun t => ?_
    choose q hq using fun j' => hval (y (ξj j') - ξj j') t
    have h3 := congrArg (ev t) hzero

    rw [map_sum, map_zero] at h3
    simp only [map_smul, smul_eq_mul, ← hq] at h3
    have h4 : ∑ j', q j' • (κ j' : Kf) = 0 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl
    have h5 := Fintype.linearIndependent_iff.1 hli q h4 j
    rw [← hq, h5, map_zero]
  rw [map_sub, sub_eq_zero, hy] at hφz
  exact hφz

end Gen

section Inv

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] [NumberField LL] (e : LL →+* G.Kf)

def evX (m : (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) →₀ ℕ) :
    G.P.Xsp →ₗ[G.Kf] G.Kf := MvPolynomial.lcoeff G.Kf m

theorem evX_sep (F : G.P.Xsp) (h : ∀ m, evX G m F = 0) : F = 0 := by
  exact MvPolynomial.ext F 0 fun m => by simpa [evX] using h m

theorem map_e_smul (a : LL) (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    MvPolynomial.map e (a • Q) = e a • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_e_rat (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    IsRat e (evX G) (MvPolynomial.map e Q) := fun m => ⟨Q.coeff m, by simp [evX, MvPolynomial.coeff_map]⟩

theorem inv_span [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (hB : RatBasisAt G e L0)
    (ξ : G.P.Xsp) (hξ : ξ ∈ G.P.HtupW L0) (hI : InvAt G i L0 ξ) :
    ξ ∈ Submodule.span G.O {ξ' | ξ' ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ' ∧ RatX G e ξ'} := by
  let φ : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL →+ G.P.Xsp :=
    (MvPolynomial.map e).toAddMonoidHom
  have hφ : ∀ (a : LL) Q, φ (a • Q) = e a • φ Q := map_e_smul G e

  let Lr : Submodule (𝓞 LL) (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ G.P.HtupW L0}
      add_mem' := by
        intro Q Q' h h'
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro a Q h
        simp only [Set.mem_ofPred_eq] at h ⊢
        obtain ⟨o, ho⟩ := (hσ (algebraMap (𝓞 LL) LL a)).1 (w.valuation_le_one a)
        have : MvPolynomial.map e (a • Q) = o • MvPolynomial.map e Q := by
          rw [← algebraMap_smul G.Kf o, ho, ← map_e_smul G e, algebraMap_smul]
          rfl
        convert Submodule.smul_mem _ o h using 1
        exact this }

  let Ur : Submodule LL (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | InvAt G i L0 (MvPolynomial.map e Q)}
      add_mem' := fun {Q Q'} h h' γ hγ => by
        rw [map_add (f := _), map_add (f := _), smul_add, h γ hγ, h' γ hγ]
      zero_mem' := fun γ _ => by rw [map_zero, map_zero, smul_zero]
      smul_mem' := fun a Q h γ hγ => by
        show ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (MvPolynomial.map e (a • Q)) = MvPolynomial.map e (a • Q)
        rw [map_e_smul, map_smul, smul_comm, h γ hγ] }

  have h1 : ξ ∈ Submodule.span G.O (φ '' (Lr : Set _)) := by
    refine Submodule.span_mono ?_ (htupW_rat G e L0 hB hξ)
    rintro _ ⟨hx, Q, rfl⟩
    exact ⟨Q, hx, rfl⟩

  let S : Set (G.P.Xsp →ₗ[G.Kf] G.P.Xsp) := {Tm | ∃ γ : (G.lev i).Γ, (G.lev i).smul γ L0 = L0 ∧
    Tm = (algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ}
  have hTm : ∀ γ (X : G.P.Xsp), ((algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ) X =
      ((G.lev i).χ γ : G.O) • (G.lev i).actX γ X := fun γ X => by
    rw [LinearMap.smul_apply, algebraMap_smul]
  have h2 : ξ ∈ Submodule.span G.Kf (φ '' (Ur : Set _)) := by
    have hspan : ξ ∈ Submodule.span G.Kf (Set.range φ) := by
      have : Submodule.span G.O (φ '' (Lr : Set _)) ≤ (Submodule.span G.Kf (Set.range φ)).restrictScalars G.O := by
        rw [Submodule.span_le]
        rintro _ ⟨Q, _, rfl⟩
        exact Submodule.subset_span ⟨Q, rfl⟩
      exact this h1
    have := span_inv e (evX G) φ (evX_sep G) hφ (map_e_rat G e) S (by
        rintro Tm ⟨γ, _, rfl⟩ Q
        obtain ⟨Q', hQ'⟩ := hA i γ (MvPolynomial.map e Q) ⟨Q, rfl⟩
        exact ⟨Q', by rw [hTm]; exact hQ'⟩)
      hspan (by
        rintro Tm ⟨γ, hγ, rfl⟩
        rw [hTm]; exact hI γ hγ)
    refine Submodule.span_mono ?_ this
    rintro _ ⟨Q, hQ, rfl⟩
    refine ⟨Q, fun γ hγ => ?_, rfl⟩
    have := hQ _ ⟨γ, hγ, rfl⟩
    rw [hTm] at this
    exact this

  have hb : LinearIndependent G.Kf (φ ∘ (MvPolynomial.basisMonomials _ LL)) := by
    have e1 : φ ∘ (MvPolynomial.basisMonomials _ LL) = MvPolynomial.basisMonomials _ G.Kf := by
      funext m
      simp [φ, MvPolynomial.coe_basisMonomials]
    rw [e1]
    exact (MvPolynomial.basisMonomials _ G.Kf).linearIndependent
  have h3 := (Formalism.BasicNotions.FBC.flat_ext w e hσ φ hφ (MvPolynomial.basisMonomials _ LL) hb).2 Lr Ur
  have h4 : ξ ∈ Submodule.span G.O (φ '' ((Lr ⊓ Ur.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) _) : Set _)) := by
    rw [← h3]
    exact ⟨h1, h2⟩
  refine Submodule.span_mono ?_ h4
  rintro _ ⟨Q, ⟨hQ1, hQ2⟩, rfl⟩
  exact ⟨hQ1, hQ2, Q, rfl⟩

theorem hRatInv_of [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (hB : RatBasis G e) : HRatInv G e :=
  fun i L0 hL0 ξ hξ => inv_span G e w hσ hA i L0 (hB L0 hL0) ξ hξ.1 hξ.2

theorem mRatSpan_of_rat_inv [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (h2 : G.FinClasses) (hL : RatLev G e) (hB : RatBasis G e) :
    MRatSpan G.P G.comp e G.M :=
  mRatSpan_inv G e h2 (Formalism.L2.G.Cmp.equivSys_HtupW G) (ratActG_of G e hL) (hRatInv_of G e w hσ (ratActG_of G e hL) hB)

end Inv

end Formalism.L2.G.Cmp
end
end
