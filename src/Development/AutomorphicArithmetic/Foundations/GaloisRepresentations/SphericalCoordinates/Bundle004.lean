module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Dynamics.Newton
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem exists_separable_aeval_eq_zero_ringOfIntegers {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

private theorem exists_integral_bezout_of_separable {F : Type} [Field F] [NumberField F] (χ : F[X]) (hs : χ.Separable) :
    ∃ (q u v : (𝓞 F)[X]) (y : ℤ), y ≠ 0 ∧ χ ∣ q.map (algebraMap (𝓞 F) F) ∧
      u * q + v * derivative q = C ((y : 𝓞 F) ^ 2) := by
  classical
  obtain ⟨a, b, hab⟩ := (separable_def' χ).1 hs
  let s : Finset F := (χ.support.image χ.coeff ∪ a.support.image a.coeff) ∪ b.support.image b.coeff
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ s
  have hlift : ∀ P : F[X], (∀ n, P.coeff n ≠ 0 → P.coeff n ∈ s) →
      ∃ Q : (𝓞 F)[X], Q.map (algebraMap (𝓞 F) F) = C (y : F) * P := by
    intro P hP
    have hl : C (y : F) * P ∈ Polynomial.lifts (algebraMap (𝓞 F) F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_C_mul]
      by_cases h0 : P.coeff n = 0
      · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
      · have hi := hy _ (hP n h0)
        rw [zsmul_eq_mul] at hi
        obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hi
        exact ⟨z, hz⟩
    exact hl
  have hs1 : ∀ n, χ.coeff n ≠ 0 → χ.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inl ⟨n, h, rfl⟩)
  have hs2 : ∀ n, a.coeff n ≠ 0 → a.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inr ⟨n, h, rfl⟩)
  have hs3 : ∀ n, b.coeff n ≠ 0 → b.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inr ⟨n, h, rfl⟩
  obtain ⟨q, hq⟩ := hlift χ hs1
  obtain ⟨u, hu⟩ := hlift a hs2
  obtain ⟨v, hv⟩ := hlift b hs3
  refine ⟨q, u, v, y, hy0, ?_, ?_⟩
  · rw [hq]; exact dvd_mul_left _ _
  · apply Polynomial.map_injective (algebraMap (𝓞 F) F) RingOfIntegers.coe_injective
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hq, hu, hv, Polynomial.map_C, Polynomial.derivative_C_mul, map_pow, map_intCast, C_pow]
    simp only [map_intCast, C_eq_intCast]
    linear_combination ((y : F[X])) ^ 2 * hab

private theorem isSemisimple_of_commute_of_integral_bezout {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : R →+* Module.End ℂ V) (hf : ∀ c, (f c).IsSemisimple)
    (h : Module.End ℂ V) (hc : ∀ c, Commute (f c) h) (q u v : R[X]) (y : ℤ) (hy : y ≠ 0)
    (hq : q.eval₂ f h = 0) (huv : u * q + v * derivative q = C ((y : R) ^ 2)) : h.IsSemisimple := by
  classical
  let S : Set (Module.End ℂ V) := Set.range f ∪ {h}
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨c, rfl⟩ | ha) b (⟨c', rfl⟩ | hb)
    · rw [← map_mul, ← map_mul, mul_comm]
    · rw [Set.mem_singleton_iff.1 hb]; exact hc c
    · rw [Set.mem_singleton_iff.1 ha]; exact (hc c').symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  let A := Algebra.adjoin ℂ S
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hS a ha b hb)
  letI : CommRing A := { (inferInstance : Ring A) with
    mul_comm := isMulCommutative_iff.mp inferInstance }
  have hfA : ∀ c, f c ∈ A := fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩)
  have hhA : h ∈ A := Algebra.subset_adjoin (Or.inr rfl)
  let fA : R →+* A := f.codRestrict A hfA
  letI : Algebra R A := fA.toAlgebra
  obtain ⟨n, hn, s, hs, hnil, hss, hns⟩ := Module.End.exists_isNilpotent_isSemisimple (f := h)
  have hsub : Algebra.adjoin ℂ {h} ≤ A := Algebra.adjoin_mono Set.subset_union_right
  let x : A := ⟨h, hhA⟩
  let r : A := ⟨s, hsub hs⟩
  have hev : ∀ (z : A) (p : R[X]), ((aeval z p : A) : Module.End ℂ V) = p.eval₂ f (z : Module.End ℂ V) := by
    intro z p
    rw [aeval_def]
    exact Polynomial.hom_eval₂ p (algebraMap R A) (A.val : A →+* Module.End ℂ V) z
  have hx0 : aeval x q = 0 := Subtype.ext (by rw [hev]; exact hq)
  have hunit : IsUnit (aeval x (derivative q)) := by
    have e := congrArg (aeval x) huv
    rw [map_add (f := _), map_mul, map_mul, hx0, mul_zero, zero_add, aeval_C] at e
    have hu : IsUnit (algebraMap R A ((y : R) ^ 2)) := by
      rw [map_pow, map_intCast, ← map_intCast (algebraMap ℂ A)]
      exact (IsUnit.map _ (isUnit_iff_ne_zero.2 (by exact_mod_cast hy))).pow 2
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_right hu
  obtain ⟨r0, -, huniq⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero
    (by rw [hx0]; exact IsNilpotent.zero) hunit
  have hxr : IsNilpotent (x - r) := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, Subtype.ext ?_⟩
    have e1 : ((x - r : A) : Module.End ℂ V) = n := by
      show h - s = n
      rw [hns]; abel
    rw [SubmonoidClass.coe_pow, e1, hk]
    rfl
  have hsc : ∀ c, Commute (f c) s := fun c =>
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hc c)
  have hcomA : ∀ a b : A, Commute (a : Module.End ℂ V) b := fun a b =>
    congrArg Subtype.val (mul_comm a b)
  have hssq : ∀ p : R[X], (p.eval₂ f s).IsSemisimple := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
      rw [eval₂_add]
      have e1 := hev r p
      have e2 := hev r p'
      refine Module.End.IsSemisimple.add_of_commute ?_ hp hp'
      rw [← e1, ← e2]
      exact hcomA _ _
    | monomial k c =>
      rw [eval₂_monomial]
      exact Module.End.IsSemisimple.mul_of_commute ((hsc c).pow_right k) (hf c) (hss.pow k)
  have hr0 : aeval r q = 0 := by
    have hnil2 := isNilpotent_aeval_sub_of_isNilpotent_sub q hxr
    rw [hx0, zero_sub, isNilpotent_neg_iff] at hnil2
    apply Subtype.ext
    have hnilE : IsNilpotent (q.eval₂ f s) := by
      rw [← hev r q]
      exact hnil2.map (A.val : A →+* Module.End ℂ V)
    rw [hev r q, Module.End.eq_zero_of_isNilpotent_isSemisimple hnilE (hssq q)]
    rfl
  have hxr' : x = r := (huniq x ⟨by simp, hx0⟩).trans (huniq r ⟨hxr, hr0⟩).symm
  have hhs : h = s := congrArg Subtype.val hxr'
  rw [hhs]
  exact hss

theorem UpperTheory.Gal.W2.hSep_of :
    UpperTheory.Gal.W2.HSep := by
  intro F _ _ O _ bar g ρ a H hcomm χ hmon hsep hkill
  obtain ⟨q, u, v, y, hy, hdvd, huv⟩ := exists_integral_bezout_of_separable χ hsep
  let e := Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)
  let f : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (e : Matrix (Fin g) (Fin g) ℂ →+* _).comp (ρ.comp a)
  have hf : ∀ c, (f c).IsSemisimple := by
    intro c
    obtain ⟨p, hp, hpa⟩ := exists_separable_aeval_eq_zero_ringOfIntegers f c
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree hpa
  have hc : ∀ c, Commute (f c) (e H) := fun c => by
    show e (ρ (a c)) * e H = e H * e (ρ (a c))
    rw [← map_mul, ← map_mul, hcomm c]
  have hq : q.eval₂ f (e H) = 0 := by
    have hk := hkill q hdvd
    rw [eval₂_eq_sum]
    have e2 : (q.sum fun i b => f b * (e H) ^ i) = e (q.sum fun i b => ρ (a b) * H ^ i) := by

      simp only [Polynomial.sum, map_sum, map_mul, map_pow]
      rfl
    rw [e2, hk, map_zero]
  have hss := isSemisimple_of_commute_of_integral_bezout f hf (e H) hc q u v y hy hq huv
  refine ⟨minpoly ℂ H, ?_, minpoly.aeval ℂ H⟩
  rw [← minpoly.algEquiv_eq e H]
  exact PerfectField.separable_iff_squarefree.mpr hss.minpoly_squarefree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2
open scoped Classical

namespace UpperTheory.Gal.W2.RootSumScaling

open UpperTheory.Gal.Schur

variable {F : Type} [Field F] [NumberField F]

end UpperTheory.Gal.W2.RootSumScaling

private theorem sch_comp_perm {n : ℕ} (lam : Fin n → ℕ) (g : Fin n → ℂ) (e : Equiv.Perm (Fin n)) :
    UpperTheory.Gal.Schur.sch lam (g ∘ e) = UpperTheory.Gal.Schur.sch lam g := by
  unfold UpperTheory.Gal.Schur.sch GroundTheory.Heights₂.Heights.RestTerms.schur
  rw [← MvPolynomial.aeval_rename, AlgHom.map_det]
  congr 2
  ext i j
  simp [GroundTheory.Heights₂.Heights.RestTerms.Schur.rename_completeSymmetric]

private theorem exists_perm_eq_comp_of_injective_of_surj {n : ℕ} (a b : Fin n → ℂ) (ha : Function.Injective a)
    (hsub : ∀ j, ∃ k, b k = a j) : ∃ e : Equiv.Perm (Fin n), a = b ∘ e := by
  choose f hf using hsub
  have hinj : Function.Injective f := by
    intro j j' h
    apply ha
    rw [← hf j, ← hf j', h]
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext j
  simp [hf]

private theorem detOne_eq_mul_prod_erase {n : ℕ} (x : ℂ) (v : Fin n → ℂ) (i : Fin n) :
    UpperTheory.Gal.Schur.detOne x v = (1 - x * v i) * ∏ k ∈ Finset.univ.erase i, (1 - x * v k) := by
  unfold UpperTheory.Gal.Schur.detOne
  exact (Finset.mul_prod_erase _ (fun k => 1 - x * v k) (Finset.mem_univ i)).symm

private theorem prod_map_erase_eq_prod_univ_erase {n : ℕ} (a : Fin n → ℂ) (ha : Function.Injective a) (i : Fin n)
    (f : ℂ → ℂ) :
    (Multiset.map f ((Multiset.map a Finset.univ.val).erase (a i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (a k) := by
  rw [← Multiset.map_erase a ha, Multiset.map_map, ← Finset.erase_val]
  rfl

open UpperTheory.Gal.W2.RootSumScaling in
theorem UpperTheory.Gal.W2.rootSumW_of :
    UpperTheory.Gal.W2.RootSumW := by
  intro F _ _ n t₀ ε lam m hconj hlam
  obtain ⟨k₀, hk₀⟩ := UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk₀ k hk 2 two_ne_zero ∅
  refine ⟨c, fun α hα s => ⟨(hc α hα s).1, (hc α hα s).2.1⟩, ?_⟩
  intro χ r hsep hr y
  set t₁ := ComplexEmbedding.conjugate t₀ with ht₁
  have hinj : ∀ τ, Function.Injective (r τ) := by
    intro τ a b hab
    have hnd : (Multiset.map (r τ) Finset.univ.val).Nodup := by
      rw [← hr τ]
      exact Polynomial.nodup_roots hsep.map
    exact Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hmap1 : χ.map t₁ = (χ.map t₀).map (starRingEnd ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have hroot : ∀ j, ∃ k, r t₁ k = starRingEnd ℂ (r t₀ j) := by
    intro j
    have hmem : r t₀ j ∈ (χ.map t₀).roots := by
      change r t₀ j ∈ rts χ t₀
      rw [hr t₀]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    have hne : χ.map t₁ ≠ 0 := Polynomial.map_ne_zero hsep.ne_zero
    have hmem' : starRingEnd ℂ (r t₀ j) ∈ rts χ t₁ := by
      change _ ∈ (χ.map t₁).roots
      rw [Polynomial.mem_roots hne, hmap1]
      exact (Polynomial.isRoot_of_mem_roots hmem).map (starRingEnd ℂ)
    rw [hr t₁] at hmem'
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem'
    exact ⟨k, hk⟩
  obtain ⟨e, he⟩ := exists_perm_eq_comp_of_injective_of_surj (fun j => starRingEnd ℂ (r t₀ j)) (r t₁)
    (fun a b h => hinj t₀ ((starRingEnd ℂ).injective h)) hroot
  have h01 : t₀ ≠ t₁ := fun h => hconj h.symm
  set g : (F →+* ℂ) → Fin n → ℂ :=
    fun τ => if τ = t₁ then (fun j => starRingEnd ℂ (r t₀ j)) else r τ with hgdef
  have hg0 : g t₀ = r t₀ := by simp [hgdef, h01]
  have hg1 : g t₁ = fun j => starRingEnd ℂ (r t₀ j) := by simp [hgdef]
  have hgτ : ∀ τ, τ ≠ t₁ → g τ = r τ := fun τ h => by simp [hgdef, h]
  have hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₀ j - g t₀ i) := by
    intro i j hji
    rw [hg0]
    exact (sub_ne_zero.mpr (fun h => hji (hinj t₀ h))).isUnit
  have key := (hsum ℂ t₀ t₁ h01 ε m g y).1 hlam hunit
  have hprod : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) =
      ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ) := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    by_cases h : τ = t₁
    · rw [h, hg1, he, sch_comp_perm]
    · rw [hgτ τ h]
  rw [← hprod, ← key]
  refine Finsupp.sum_congr fun α _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [hr t₀, Multiset.map_map]
  refine (Finset.sum_congr rfl fun i _ => ?_ :
    ∑ i, locW t₀ ε α y χ (r t₀ i) = _)
  have hB : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (r t₀ i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (r t₀ k) := fun f => by
    rw [hr t₀]
    exact prod_map_erase_eq_prod_univ_erase _ (hinj t₀) i f
  unfold locW
  rw [mul_comm, Finset.prod_comm]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hx0 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)) = t₀ (α s : F) := rfl
    have hx1 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)) = starRingEnd ℂ (t₀ (α s : F)) :=
      ComplexEmbedding.conjugate_coe_eq t₀ _
    have hA : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀) =
        (1 - t₀ (α s : F) * (y * r t₀ i)) * ∏ k ∈ Finset.univ.erase i, (1 - t₀ (α s : F) * r t₀ k) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx0]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀ = UpperTheory.Gal.Schur.scaleAt y i (r t₀) := by
        simp [UpperTheory.Gal.Schur.twist, hg0]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleAt]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleAt, Finset.ne_of_mem_erase hk]
    have hC : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁) =
        (1 - starRingEnd ℂ (t₀ (α s : F)) * starRingEnd ℂ (r t₀ i)) *
          ∏ k ∈ Finset.univ.erase i, (1 - starRingEnd ℂ (t₀ (α s : F)) * (y * starRingEnd ℂ (r t₀ k))) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx1]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁ =
          UpperTheory.Gal.Schur.scaleOff y i (fun j => starRingEnd ℂ (r t₀ j)) := by
        simp [UpperTheory.Gal.Schur.twist, hg1, h01.symm]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleOff]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleOff, Finset.ne_of_mem_erase hk]
    have hE : ∀ τ ∈ (Finset.univ.erase t₀).erase t₁,
        (Multiset.map (fun z => 1 - τ (α s : F) * (y ^ ε τ * z)) (rts χ τ)).prod =
          UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO τ (α s)))
            (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ) := by
      intro τ hτ
      have hτ1 := Finset.ne_of_mem_erase hτ
      have hτ0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
      rw [hr τ, Multiset.map_map]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ = fun k => y ^ ε τ * r τ k := by
        simp [UpperTheory.Gal.Schur.twist, hτ0, hτ1, hgτ τ hτ1]
      rw [htw]
      rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t₀),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ t₁⟩),
      hA, hC, ← Finset.prod_congr rfl hE]
    unfold fibW
    rw [hB, hB]
    ring
  · unfold ballW
    rw [hB, hg0]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Ring.inverse_eq_inv', div_eq_mul_inv]
end
