module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle010
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

def fracR {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) : FinalTheorems.reesChart g i :=
  ⟨IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)), Algebra.subset_adjoin ⟨k, rfl⟩⟩

theorem fracR_self {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) : fracR g i i = 1 := by
  apply Subtype.ext
  exact IsLocalization.mk'_self' (Localization.Away (g i))

theorem algebraMap_reesChart_eq {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) :
    algebraMap R (FinalTheorems.reesChart g i) (g k) = fracR g i k * algebraMap R (FinalTheorems.reesChart g i) (g i) := by
  apply Subtype.ext
  exact (IsLocalization.mk'_spec (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i))).symm

theorem algebraMap_reesChart_mem_nonZeroDivisors {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R)
    (i : Fin m) : algebraMap R (FinalTheorems.reesChart g i) (g i) ∈ nonZeroDivisors (FinalTheorems.reesChart g i) := by
  have hu : IsUnit (algebraMap R (Localization.Away (g i)) (g i)) :=
    IsLocalization.Away.algebraMap_isUnit (g i)
  have key : ∀ x : FinalTheorems.reesChart g i, x * algebraMap R _ (g i) = 0 → x = 0 := by
    intro x hx
    have h1 : (x : Localization.Away (g i)) * algebraMap R _ (g i) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (hu.mul_left_eq_zero.mp h1)
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem specMap_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (constSec s U.1)) = U.2.fromSpec ≫ s := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (.of ℂ))) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl

theorem adjoin_reesChart_eq_top {R : Type} [CommRing R] (c : ℂ →+* R) {σ : Type} (z : σ → R)
    (hz : ∀ r : R, ∃ f : MvPolynomial σ ℂ, r = eval₂ c z f) {m : ℕ} (g : Fin m → R) (i : Fin m)
    {n : ℕ} (y : Fin n → FinalTheorems.reesChart g i)
    (hyz : ∀ q, ∃ l, y l = algebraMap R _ (z q)) (hyt : ∀ k, ∃ l, y l = fracR g i k) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _ ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
      (Set.range y) = ⊤ := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
  have hR : ∀ r : R, algebraMap R (FinalTheorems.reesChart g i) r ∈ Algebra.adjoin ℂ (Set.range y) := by
    intro r
    obtain ⟨f, rfl⟩ := hz r
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem _ a
    | add f h hf hh => rw [eval₂_add, map_add (f := _)]; exact add_mem hf hh
    | mul_X f q hf =>
      rw [eval₂_mul, eval₂_X, map_mul]
      obtain ⟨l, hl⟩ := hyz q
      refine mul_mem hf ?_
      rw [← hl]
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hyt k
    have h2 : y l ∈ Algebra.adjoin ℂ (Set.range y) := Algebra.subset_adjoin ⟨l, rfl⟩
    rw [hl] at h2
    exact h2
  | algebraMap r => exact hR r
  | add x y hx hy ihx ihy => exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_eval₂_chartCoord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (r : Γ(projX P hP, (chartOpen hP p).1)) :
    ∃ f : MvPolynomial (Σ k, ι k) ℂ, r = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p r)
  refine ⟨f, ?_⟩
  rw [← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]

def yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) {m : ℕ}
    (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    Fin (Fintype.card (Σ k, ι k) + m) → FinalTheorems.reesChart g i :=
  fun l => Sum.elim (fun a => algebraMap _ (FinalTheorems.reesChart g i)
    (chartCoord hP p ((Fintype.equivFin _).symm a))) (fracR g i) (finSumFinEquiv.symm l)

theorem yC_yq {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (q : Σ k, ι k) :
    yC hP p g i (finSumFinEquiv (Sum.inl (Fintype.equivFin _ q))) =
      algebraMap _ (FinalTheorems.reesChart g i) (chartCoord hP p q) := by
  simp [yC]

theorem yC_yt {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (k : Fin m) :
    yC hP p g i (finSumFinEquiv (Sum.inr k)) = fracR g i k := by
  simp [yC]

theorem adjoin_yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _
      ((algebraMap _ (FinalTheorems.reesChart g i)).comp (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
      (Set.range (yC hP p g i)) = ⊤ :=
  adjoin_reesChart_eq_top _ (chartCoord hP p) (exists_eval₂_chartCoord hP p) g i (yC hP p g i)
    (fun q => ⟨_, yC_yq hP p g i q⟩) (fun k => ⟨_, yC_yt hP p g i k⟩)

end

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def eQ (x : PrimeSpectrum (MvPolynomial σ ℤ)) (h : ChZero x.asIdeal) :
    PrimeSpectrum (MvPolynomial σ ℚ) :=
  ⟨Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal, map_isPrime x.asIdeal h⟩

lemma eQ_lt {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by
  have hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal := by
    show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal
    exact Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)
  show (eQ x hx).asIdeal < (eQ y hy).asIdeal
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) =
      (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) := congrArg (Ideal.comap _) heq
  rw [comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy] at h2
  exact (show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2

lemma length_le_coheight_eQ (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by
  induction s using RelSeries.inductionOn with
  | singleton x => intros; simp
  | cons t x hx ih =>
    intro z hz h0
    rw [RelSeries.head_cons] at hz
    subst hz
    simp only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
    by_cases h1 : ChZero t.head.asIdeal
    · have h2 := ih t.head rfl h1
      have h3 := Order.coheight_add_one_le (eQ_lt h0 h1 hx)
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight (eQ t.head h1) + 1 + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h3 1
    · have h2 : (t.length : ℕ∞) ≤ Order.coheight t.head := Order.length_le_coheight_head
      have h3 := dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1
      rw [ringKrullDim_quotient_eq_coheight,
        ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)] at h3
      have h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0) := WithBot.coe_le_coe.mp h3
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight t.head + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h4 1

private lemma isJacobsonRing_int_regular_local_rings : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases hb : P = ⊥
  · subst hb
    intro m hm
    rw [Ideal.mem_jacobson_bot] at hm
    rw [Ideal.mem_bot]
    have h1 := Int.isUnit_iff.mp (hm 1)
    have h2 := Int.isUnit_iff.mp (hm 2)
    omega
  · have hmax : P.IsMaximal := by
      first
        | exact Ideal.IsPrime.isMaximal hP hb
        | exact hP.isMaximal hb
        | exact Ideal.IsPrime.to_maximal_ideal hb
        | exact Ring.DimensionLEOne.maximalOfPrime hb hP
    exact sInf_le ⟨le_rfl, hmax⟩

private lemma not_isMaximal_of_chZero (Q : Ideal (MvPolynomial σ ℤ)) (hQ : ChZero Q) :
    ¬ Q.IsMaximal := by
  intro hmax
  haveI := hmax
  haveI := isJacobsonRing_int_regular_local_rings
  letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) =
      algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q) := RingHom.ext_int _ _
  haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by
    constructor
    intro x
    have hx := hint x
    rw [hfe] at hx
    exact hx
  have hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hm
    exact hQ m hm
  have hF : IsField ℤ := isField_of_isIntegral_of_isField hinj
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega

lemma coheight_eQ_add_one_le (P : PrimeSpectrum (MvPolynomial σ ℤ)) (hP : ChZero P.asIdeal) :
    Order.coheight (eQ P hP) + 1 ≤ Order.coheight P := by
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ) :=
    fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩
  have hg : StrictMono g := by
    intro a b hab
    show a.asIdeal.comap φ < b.asIdeal.comap φ
    exact comap_strictMono (show a.asIdeal < b.asIdeal from hab)
  have hg0 : g (eQ P hP) = P := PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)
  have hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M := by
    intro L
    have hQ : ChZero (g L).asIdeal := chZero_comap L.asIdeal
    have hnm := not_isMaximal_of_chZero (g L).asIdeal hQ
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top
    refine ⟨⟨M, hM.isPrime⟩, ?_⟩
    show (g L).asIdeal < M
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnm
    rw [heq]
    exact hM
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P := by
    intro n hn
    obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight (eQ P hP) hn
    obtain ⟨M, hM⟩ := hup p.last
    have hlast : (p.map g hg).last < M := hM
    let q := (p.map g hg).snoc M hlast
    have hqh : q.head = P := by
      rw [RelSeries.head_snoc]
      show g p.head = P
      rw [hph]
      exact hg0
    have hql : q.length = n + 1 := by
      rw [← hpl]
      rfl
    rw [← hql, ← hqh]
    exact Order.length_le_coheight_head
  rcases eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h
  · have htop : Order.coheight P = ⊤ := by
      by_contra hne
      have h1 := key (Order.coheight P).toNat (by rw [h]; exact le_top)
      have h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hne]
        exact h1
      have h3 := (Nat.cast_le (α := ℕ∞)).mp h2
      omega
    rw [htop]
    exact le_top
  · have h1 := key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])
    rw [← ENat.coe_toNat h]
    exact_mod_cast h1

end ReciprocityTheory.AnForm.R.IntegerToRational
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace AffPres

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)} (P : AffPres s)

theorem secHom_surj : Function.Surjective P.secHom := by
  intro t
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).hom (P.iso.inv.appTop (P.V.topIso.inv t)))
  refine ⟨a, ?_⟩
  show P.V.topIso.hom (P.iso.hom.appTop ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk P.K a))) = t
  rw [ha, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
    ← CommRingCat.comp_apply P.iso.inv.appTop, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply, ← CommRingCat.comp_apply P.V.topIso.inv, Iso.inv_hom_id,
    CommRingCat.id_apply]

theorem isAffineOpen_V' : IsAffineOpen P.V := by
  have : IsAffine P.V.toScheme := IsAffine.of_isIso P.iso.hom
  exact this

end AffPres

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)

theorem eval_val_chartCoord (p : (k : K) → ι k) (y : projX P hP) (hy : y ∈ (chartOpen hP p).1)
    (hc : IsClosed ({y} : Set (projX P hP))) (f : MvPolynomial (Σ k, ι k) ℂ) :
    eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f =
      val (toSpecC hP) ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) y hy := by
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc
  have h := MvPolynomial.ringHom_ext
    (f := eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy))
    (g := φ.comp ((gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p)))) ?_ ?_
  · exact (RingHom.congr_fun h f).trans (hφ _)
  · intro a
    rw [eval_C, RingHom.comp_apply, RingHom.comp_apply, hφ]
    show a = val _ ((gammaChart hP p).symm (Ideal.Quotient.mk _ (C a))) y hy
    rw [gammaChart_symm_C, val_const _ _ y hy hc]
  · intro q
    rw [eval_X, RingHom.comp_apply, RingHom.comp_apply, hφ]
    rfl

end

end ReciprocityTheory.AnForm.R
end
