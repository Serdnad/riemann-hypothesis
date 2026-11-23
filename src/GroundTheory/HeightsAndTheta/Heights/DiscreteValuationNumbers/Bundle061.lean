module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle054
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Pigeonhole
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Algebra

variable {L : Type*} [Field L]

theorem exists_mul_mem_of_mem_blowUpColon (A : Subring L) (I : Ideal A) (hI : I ≠ ⊥) {g : L}
    (hg : g ∈ blowUpColon L I) : ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := by
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.iSup_induction _ (motive := fun g => ∃ d : A, d ≠ 0 ∧ ∃ r : A,
    algebraMap A L d * g = algebraMap A L r) hg ?_ ⟨1, one_ne_zero, 0, by simp⟩ ?_
  · intro m g hg
    have hy : algebraMap A L y ^ m ∈ (Submodule.map (Algebra.linearMap A L) I) ^ m :=
      Submodule.pow_mem_pow _ (Submodule.mem_map_of_mem hyI) m
    have hgy := (Submodule.mem_div_iff_forall_mul_mem.mp hg) _ hy
    have h1 : Submodule.map (Algebra.linearMap A L) I ≤ 1 := by
      rw [Submodule.one_eq_range]
      exact LinearMap.map_le_range
    have hone : ∀ k : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => exact (pow_zero _).le
      | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul' ih h1).trans (mul_one _).le
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hone m hgy)
    refine ⟨y ^ m, pow_ne_zero _ hy0, r, ?_⟩
    rw [map_pow, hr, mul_comm]
  · rintro g₁ g₂ ⟨d₁, hd₁, r₁, h₁⟩ ⟨d₂, hd₂, r₂, h₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, d₂ * r₁ + d₁ * r₂, ?_⟩
    simp only [map_mul, map_add (f := _), ← h₁, ← h₂]
    ring

theorem finite_finrank_one_of_le_blowUpColon (A B : Subring L) [IsNoetherianRing A] (hAB : A ≤ B)
    (I : Ideal A) (hI : I ≠ ⊥) (hfg : (blowUpColon L I).FG) (hle : ∀ f ∈ B, f ∈ blowUpColon L I) :
    letI := (Subring.inclusion hAB).toAlgebra
    Module.Finite A B ∧ Module.finrank A B = 1 := by
  classical
  let _ := (Subring.inclusion hAB).toAlgebra

  let Bs : Submodule A L :=
    { carrier := B
      add_mem' := fun h₁ h₂ => add_mem h₁ h₂
      zero_mem' := zero_mem _
      smul_mem' := fun r f hf => by
        rw [Algebra.smul_def]
        exact mul_mem (hAB r.2) hf }
  obtain ⟨s, hs⟩ : Bs.FG := hfg.of_le fun f hf => hle f hf

  have hsB : ∀ g ∈ s, ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := fun g hg =>
    exists_mul_mem_of_mem_blowUpColon A I hI (hle g (show g ∈ Bs from hs ▸ Submodule.subset_span hg))
  choose! dg hdg0 rg hrg using hsB
  have hd0 : (∏ g ∈ s, dg g) ≠ 0 := Finset.prod_ne_zero_iff.mpr hdg0
  let T : Submodule A L :=
    { carrier := {g | ∃ r : A, algebraMap A L (∏ g ∈ s, dg g) * g = algebraMap A L r}
      add_mem' := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ => ⟨r₁ + r₂, by rw [map_add (f := _), ← h₁, ← h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c g ⟨r, hr⟩ => ⟨c * r, by
        rw [Algebra.smul_def, map_mul, ← hr]
        ring⟩ }
  have hBT : Bs ≤ T := by
    rw [← hs, Submodule.span_le]
    intro g hg
    refine ⟨(∏ g' ∈ s.erase g, dg g') * rg g, ?_⟩
    rw [map_mul, ← hrg g hg, ← Finset.prod_erase_mul s dg hg, map_mul]
    ring

  let φ : Bs →ₗ[A] L := (LinearMap.mulLeft A (algebraMap A L (∏ g ∈ s, dg g))).comp Bs.subtype
  have hφ : Function.Injective φ := fun f₁ f₂ h => Subtype.ext
    (mul_left_cancel₀ (fun h0 => hd0 (Subtype.ext h0)) h)
  have hφr : LinearMap.range φ ≤ LinearMap.range (Algebra.linearMap A L) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨r, hr⟩ := hBT f.2
    exact ⟨r, hr.symm⟩
  have hinj : Function.Injective (Algebra.linearMap A L) := fun _ _ h => Subtype.ext h
  have hle1 : Module.rank A Bs ≤ 1 := by
    rw [← rank_range_of_injective φ hφ, ← Module.rank_self A,
      ← rank_range_of_injective _ hinj]
    exact Submodule.rank_mono hφr
  let ψ : A →ₗ[A] Bs := (Algebra.linearMap A L).codRestrict Bs fun r => hAB r.2
  have hge1 : 1 ≤ Module.rank A Bs := by
    rw [← Module.rank_self A]
    exact LinearMap.rank_le_of_injective ψ fun x y h =>
      hinj (show Algebra.linearMap A L x = Algebra.linearMap A L y from congrArg (fun z : Bs => (z : L)) h)

  let e : Bs ≃ₗ[A] B :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite A Bs := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle1 (by exact_mod_cast hge1))

end Algebra

theorem BlowUpOverLocFinite.proof (hloc : HomLocRingLocal.Statement.{u})
    (hchart : BlowUpOverLocInChart.Statement.{u}) (hcolon : ChartsInColon.Statement.{u})
    (hfin : BlowUpColonFinite.Statement.{u}) : BlowUpOverLocFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu ⟨j₀, hj₀⟩ c x hx hxP W hW hWrel
  have := hP.multiProj.isPrime
  obtain ⟨hL, hN, hD⟩ := hloc O K ι P hP.multiProj c x hx hxP W hW hWrel
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have he : ∀ f, f ∉ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) ≠ 0 := fun f hf h0 => hf (by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P)) (h0.trans (map_zero _).symm))
  have he0 : ∀ f, f ∈ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) = 0 := fun f hf => by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel N
  have hh0 := he (powMonomial N i) fun hm => hi (hPW hm)
  let a : J → homLocRing P W := fun k =>
    ⟨algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i)),
      Subring.subset_closure ⟨N, u k, powMonomial N i, hu k, isMultiHomog_powMonomial N i, hi, rfl⟩⟩
  have hI : Ideal.span (Set.range a) ≠ ⊥ := by
    intro hb
    have h1 : a j₀ ∈ Ideal.span (Set.range a) := Ideal.subset_span ⟨j₀, rfl⟩
    rw [hb, Ideal.mem_bot] at h1
    exact div_ne_zero (he _ hj₀) hh0 (congrArg Subtype.val h1)

  have hle : ∀ f ∈ blowUpOverLoc P W u, f ∈ blowUpColon (FractionRing (MRing ι O ⧸ P)) (Ideal.span (Set.range a)) := by
    intro f hf
    refine hcolon (homLocRing P W) _ J a f fun k hk => ?_
    have huk : u k ∉ P := fun hm => hk (by
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / _ = 0
      rw [he0 _ hm, zero_div])
    refine (Subring.closure_le (t := (Algebra.adjoin (homLocRing P W) _).toSubring)).mpr
      (Set.union_subset ?_ ?_) (hchart O K ι J P W hP.multiProj.multiHomog hWp hPW hWrel N u hu k huk hf)
    · intro z hz
      exact Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : homLocRing P W)
    · rintro _ ⟨l, rfl⟩
      refine Algebra.subset_adjoin ⟨l, ?_⟩
      exact div_div_div_cancel_right₀ hh0
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u l)))
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)))
  have := hN
  exact finite_finrank_one_of_le_blowUpColon (homLocRing P W) (blowUpOverLoc P W u)
    (homLocRing_le_blowUpOverLoc P W u) _ hI
    (hfin (homLocRing P W) _ (fun _ _ h => Subtype.ext h) hD _ hI) hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

open scoped Pointwise

section

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

theorem ChartsInColon.prod_mem_pow {ι : Type*} (M : Submodule A L) (s : Finset ι) (x : ι → L)
    (hx : ∀ i ∈ s, x i ∈ M) : ∏ i ∈ s, x i ∈ M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.one_le.mp (le_refl (1 : Submodule A L))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact Submodule.mul_mem_mul (hx i (Finset.mem_insert_self i s))
      (ih fun k hk => hx k (Finset.mem_insert_of_mem hk))

theorem ChartsInColon.exists_mul_pow_mem {J : Type*} (a : J → A) (j : J) (hj : algebraMap A L (a j) ≠ 0)
    {g : L} (hg : g ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) :
    ∃ m : ℕ, g * algebraMap A L (a j) ^ m ∈
      (Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a))) ^ m := by
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hmem : ∀ k, algebraMap A L (a k) ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    simpa only [pow_one, div_mul_cancel₀ _ hj] using hmem k
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, pow_zero, mul_one]; exact Submodule.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := Submodule.mul_mem_mul hm (Submodule.pow_mem_pow I (hmem j) n)
    have h2 := Submodule.mul_mem_mul hn (Submodule.pow_mem_pow I (hmem j) m)
    rw [← pow_add] at h1 h2
    rw [add_comm n m] at h2
    convert add_mem h1 h2 using 1
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h := Submodule.mul_mem_mul hm hn
    rw [← pow_add] at h
    convert h using 1
    ring

end

theorem ChartsInColon.proof : ChartsInColon.Statement.{u} := by
  classical
  intro A _ L _ _ J _ a f hf
  unfold blowUpColon
  set b : J → L := fun k => algebraMap A L (a k) with hb
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hIspan : I = Submodule.span A (Set.range b) := by
    rw [hI, Ideal.span, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmem : ∀ k, b k ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  have hex : ∀ j, ∃ m : ℕ, b j ≠ 0 → f * b j ^ m ∈ I ^ m := by
    intro j
    by_cases hj : b j = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨m, hm⟩ := ChartsInColon.exists_mul_pow_mem a j hj (hf j hj)
      exact ⟨m, fun _ => hm⟩
  choose m hm using hex
  set M := ∑ j, m j with hM
  refine Submodule.mem_iSup_of_mem (Fintype.card J * M + 1) ?_
  rw [Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [hIspan, Submodule.span_pow] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := Set.mem_pow.mp hx
    choose k hk using fun i => (g i).2
    have hx' : (List.ofFn fun i => (g i : L)).prod = ∏ i, b (k i) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (hk i).symm
    rw [hx']
    obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := k) (n := M)
      (by rw [Fintype.card_fin]; omega)
    set s := Finset.univ.filter fun i => k i = j with hs
    set t := Finset.univ.filter fun i => ¬ k i = j with ht
    have hsplit : ∏ i, b (k i) = b j ^ s.card * ∏ i ∈ t, b (k i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => k i = j), ← Finset.prod_const]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    have hcard : s.card + t.card = Fintype.card J * M + 1 := by
      rw [hs, ht, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have ht' : ∏ i ∈ t, b (k i) ∈ I ^ t.card :=
      ChartsInColon.prod_mem_pow I t _ fun i _ => hmem (k i)
    rw [hsplit]
    by_cases hbj : b j = 0
    · rw [hbj, zero_pow (by omega), zero_mul, mul_zero]
      exact zero_mem _
    · have hmj : m j ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h1 := Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hm j hbj) (Submodule.pow_mem_pow I (hmem j) (s.card - m j))) ht'
      rw [← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega), hcard] at h1
      convert h1 using 1
      have hc : s.card - m j + m j = s.card := Nat.sub_add_cancel (by omega)
      conv_lhs => rw [← hc, pow_add]
      ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

namespace SegreFlagCutChart

theorem exists_pow_mul_mem_of_mem_sup_map {R S F : Type*} [CommRing R] [CommRing S] [FunLike F S R]
    [RingHomClass F S R] (f : F) (A I : Ideal R) (J : Ideal S) (v : R) (hI : I ≤ A)
    (hJ : ∀ q ∈ J, ∃ n : ℕ, v ^ n * f q ∈ A) : ∀ x ∈ I ⊔ J.map f, ∃ n : ℕ, v ^ n * x ∈ A := by
  let T : Ideal R :=
    { carrier := {x | ∃ n : ℕ, v ^ n * x ∈ A}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : v ^ (m + n) * (a + b) = v ^ n * (v ^ m * a) + v ^ m * (v ^ n * b) := by ring
        rw [h]
        exact A.add_mem (A.mul_mem_left _ hm) (A.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : v ^ n * (c • x) = c * (v ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact A.mul_mem_left _ hn }
  have hle : I ⊔ J.map f ≤ T :=
    sup_le (fun x hx => ⟨0, by simpa using hI hx⟩) (Ideal.map_le_iff_le_comap.2 fun q hq => hJ q hq)
  exact fun x hx => hle hx

end SegreFlagCutChart


open SegreFlagCutChart in
theorem SegreFlagCutChart.proof (hCS : SegreFlagCutChartSection.Statement)
    (hPre : SegreFlagCutPreimage.Statement) : SegreFlagCutChart.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk W hW hWr hPW hϖW
  classical

  choose c hc using fun j : K => hWr (some (some j))
  have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
    intro j h0
    refine hc j (hPW (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
    rw [aeval_X]
    show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
    rw [h0, map_zero]
  have hcne : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => nz j
  have hvW : (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ∉ W := fun hm => by
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j hj
  obtain ⟨-, dl, dm, l, μ, m, hμ, hl, hμh, hdeg, hval, hsat⟩ :=
    hCS O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hcne
  have hμW : μ ∉ W := by
    rw [hμ]
    intro hm
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j (hW.mem_of_pow_mem _ hj)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    refine ⟨dl, dm, l, μ, _, hl, hμh, hdeg, hμW, hvW, hval, fun _ hlW => ?_, fun h => absurd h (lt_irrefl 0)⟩
    obtain ⟨j, hj⟩ := hWr none
    have hq : (X ⟨none, j⟩ : MvPolynomial (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O) ∈
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t 0) := by
      refine mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      show flagClosurePt y w e φ φ' t 0 ⟨none, j⟩ = 0
      simp [flagClosurePt, pairProjCoord, flagCoord]
    obtain ⟨n, hn⟩ := hsat _ hq
    have h1 := sup_le hPW ((Ideal.span_singleton_le_iff_mem W).2 hlW) hn
    rw [rename_X] at h1
    rcases hW.mem_or_mem h1 with h2 | h2
    · exact hvW (hW.mem_of_pow_mem _ h2)
    · exact hj h2
  ·
    obtain ⟨u₀, hu₀W, hu₀⟩ := hPre O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht k hk W hW hWr hPW hϖW
    refine ⟨dl, dm, l, μ, u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O), hl, hμh, hdeg,
      hμW, fun hm => ?_, hval, fun h => absurd h (Nat.pos_iff_ne_zero.mp hk0), fun _ q hq => ?_⟩
    · rcases hW.mem_or_mem hm with h | h
      · exact hu₀W h
      · exact hvW h
    · obtain ⟨n, hn⟩ := hu₀ q hq
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_of_mem_sup_map _ _ _ _ _ le_sup_left hsat _ hn
      refine ⟨n + m', ?_⟩
      have h : (u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ (n + m') * q =
          u₀ ^ m' * (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
            ((∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ m' * (u₀ ^ n * q)) := by
        ring
      rw [h]
      exact Ideal.mul_mem_left _ _ hm'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_of_isLocalization_atPrime' {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMaxPoint.proof (h₁ : BlowUpOverLocMaxCentre.Statement.{u})
    (h₂ : BlowUpOverLocFibreMinimal.Statement.{u}) (h₃ : BlowUpOverLocPointDeg.Statement.{u}) :
    BlowUpOverLocMaxPoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  have hmin := h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h', 𝔫', h𝔫', hl', hdeg⟩ :=
    h₃ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hmin hW'r hW'c
  have := h𝔫.isPrime
  have := h𝔫'.isPrime
  have heq : 𝔫 = 𝔫' := prime_eq_of_isLocalization_atPrime' h 𝔫 𝔫' hl hl'
  subst heq
  exact ⟨W', ⟨hmin, hW'r, hW'c⟩, ⟨h, hl⟩, hdeg⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
