module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
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
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]

omit [Fintype ι] in
theorem tpow_diagonal_alg (n : ℕ) (a : ι → R) :
    tpow n (diagonal a) = diagonal (fun b : Fin n → ι => ∏ j, a (b j)) := by
  ext b c
  simp only [tpow, Matrix.of_apply]
  by_cases h : b = c
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.diagonal_apply_ne _ hj)

omit [Fintype ι] in
theorem tpow_one_alg (n : ℕ) : tpow n (1 : Matrix ι ι R) = 1 := by
  have h := tpow_diagonal_alg (ι := ι) n (fun _ => (1 : R))
  simpa using h

omit [DecidableEq ι] in
theorem tpow_mul_alg (n : ℕ) (y z : Matrix ι ι R) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext b c
  simp only [tpow, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]

theorem act_apply_alg {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) (k : TIdx ι d) :
    act d t y k = ∑ a : Fin (d k.1) → ι, t ⟨k.1, a⟩ * ∏ j, y (a j) (k.2 j) := by
  simp [act, tpow, Matrix.vecMul, dotProduct]

end

theorem tpow_act_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  intro ι _ _ R _
  refine ⟨fun n => ⟨tpow_one_alg n, tpow_mul_alg n, fun y => ?_⟩, fun m d t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext a b
    simp [tpow]
  · funext k
    simp [act, tpow_one_alg]
  · intro y z
    funext k
    simp only [act, tpow_mul_alg, ← Matrix.vecMul_vecMul]
  · intro a k
    simp only [act, tpow_diagonal_alg, Matrix.vecMul_diagonal]
  · intro S y ht hy k
    rw [act_apply_alg]
    exact S.sum_mem fun a _ => S.mul_mem (ht _) (S.prod_mem fun j _ => hy _ _)
  · intro c y
    funext k
    simp only [act_apply_alg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · intro R' _ φ y
    funext k

    simp only [act_apply_alg, map_sum, map_mul, map_prod, Matrix.map_apply]

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem relIndex_le_two_of_coset {G : Type} [CommGroup G] (H K : Subgroup G) (ε : G)
    (h : ∀ x ∈ K, x ∈ H ∨ x * ε⁻¹ ∈ H) : H.relIndex K ≤ 2 := by
  by_cases hK : K ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hK]; norm_num
  · obtain ⟨a, haK, haH⟩ := SetLike.not_le_iff_exists.mp hK
    have ha := (h a haK).resolve_left haH
    apply le_of_eq
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a⁻¹, K.inv_mem haK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ H
    · right
      refine ⟨hb, fun hba => haH ?_⟩
      have := H.mul_mem hb (H.inv_mem hba)
      simpa using this
    · left
      refine ⟨?_, hb⟩
      have := H.mul_mem ((h b b.2).resolve_left hb) (H.inv_mem ha)
      have e : (b : G) * ε⁻¹ * (a * ε⁻¹)⁻¹ = b * a⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at this

theorem relIndex_sqs_le_two_mul :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  intro G _ U H ε hHU hfin hε hsq
  have hle : ∀ V : Subgroup G, sqs V ≤ V := by
    rintro V x ⟨y, hy, rfl⟩
    exact V.pow_mem hy 2
  have hmono : sqs H ≤ sqs U := Subgroup.map_mono hHU
  have h1 := Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU
  have h2 := Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)
  set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'
  have h3 : H'.relIndex U = (sqs H).relIndex (sqs U) := by
    rw [hH', Subgroup.relIndex_comap]; rfl
  have hHH' : H ≤ H' ⊓ U := le_inf (Subgroup.le_comap_map _ _) hHU
  have h4 := Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right
  rw [Subgroup.inf_relIndex_right, h3] at h4
  have h5 : H.relIndex (H' ⊓ U) ≤ 2 := by
    apply relIndex_le_two_of_coset H _ ε
    rintro x ⟨⟨y, hy, hxy⟩, -⟩
    simp only [powMonoidHom_apply] at hxy
    have : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]
    rcases hε _ this with h | h
    · left
      rw [mul_inv_eq_one] at h
      rw [h]; exact hy
    · right
      have e : x * ε⁻¹ = y := by
        rw [← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]
      rw [e]; exact hy
  have hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0 := by
    rw [h2, ← h1]; exact mul_ne_zero hsq hfin
  obtain ⟨hb, ha⟩ := mul_ne_zero_iff.mp hne
  refine ⟨ha, ?_⟩
  apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)
  rw [h2, ← h1, ← h4]
  calc (sqs H).relIndex H * (H.relIndex (H' ⊓ U) * (sqs H).relIndex (sqs U))
      ≤ (sqs H).relIndex H * (2 * (sqs H).relIndex (sqs U)) := by gcongr
    _ = _ := by ring

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem finite_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := hv
  have h0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact x.ne_zero
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h
  · left
    exact h

theorem exists_superset_mem_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (X : Finset Fˣ)
      (S₀ : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ S, S₀ ⊆ S ∧ ∀ S', S ⊆ S' → ∀ x ∈ X, x ∈ sUnits F S' := by
  intro F _ _ X S₀
  classical
  have hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite :=
    X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x
  refine ⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩
  intro S' hS' x hx
  rw [mem_sUnits]
  intro v hv
  by_contra h
  apply hv
  apply hS'
  apply Finset.mem_union_right
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_biUnion hx h

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.CosetSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vanC (S : Set (Matrix ι ι ℂ)) : Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {f | ∀ g ∈ S, evC f g = 0}
  add_mem' := by
    intro a b ha hb g hg
    have h1 := ha g hg
    have h2 := hb g hg
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), h1, h2, add_zero]
  zero_mem' := by
    intro g _
    simp [evC]
  smul_mem' := by
    intro c a ha g hg
    have h1 := ha g hg
    simp only [evC] at h1 ⊢
    rw [smul_eq_mul, map_mul, h1, mul_zero]


omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC] at hp hq ⊢
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p ij hp =>
    simp only [evC] at hp ⊢
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in
lemma exists_rtr (h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ f' : MvPolynomial (ι × ι) ℂ, ∀ z, evC f' z = evC f (z * h) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), map_add (f := _), h1, h2]
  | mul_X p ij hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩
    have h1 := hp z
    simp only [evC] at h1 ⊢
    rw [map_mul, map_mul, h1]
    congr 1
    simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  simp only [evC, ev]
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

lemma mem_of_forall_vanC {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {z : Matrix ι ι ℂ}
    (hz : ∀ f ∈ vanC Γ, evC f z = 0) : z ∈ Γ := by
  apply hΓ.closed
  intro f hf
  rw [← evC_map]
  apply hz
  intro g hg
  rw [evC_map]
  exact hf g hg

lemma vanC_sup_eq_top {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {y : Matrix ι ι ℂ} (hy : y.det = 1)
    (hyΓ : y ∉ Γ) : vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz
  have key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0 := by
    intro f hf
    have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
    simpa [evC, hz] using h1
  have hzΓ : z ∈ Γ := mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)
  have hyy : y * y.adjugate = 1 := by rw [Matrix.mul_adjugate, hy, one_smul]
  have hyy' : y.adjugate * y = 1 := by rw [Matrix.adjugate_mul, hy, one_smul]
  have hwΓ : z * y.adjugate ∈ Γ := by
    refine mem_of_forall_vanC hΓ fun f hf => ?_
    obtain ⟨f', hf'⟩ := exists_rtr y.adjugate f
    rw [← hf']
    refine key f' (Ideal.mem_sup_right ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [hf', mul_assoc, hyy, mul_one]
    exact hf g hg
  apply hyΓ
  have h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1 := by
    rw [Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]
  have h2 : y = (z * y.adjugate).adjugate * z := by
    calc y = (z * y.adjugate).adjugate * (z * y.adjugate) * y := by rw [h1, one_mul]
      _ = (z * y.adjugate).adjugate * (z * (y.adjugate * y)) := by simp only [mul_assoc]
      _ = _ := by rw [hyy', mul_one]
  rw [h2]
  exact hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ

end GlobalTheory.ClassFin.CosetSep

namespace GlobalTheory.ClassFin


open CosetSep in
theorem exists_isInv_evC_one_ne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  intro ι _ _ Γ Rey hΓ hR y hy hyΓ
  have htop := vanC_sup_eq_top hΓ hy hyΓ
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hRa : Rey a ∈ vanC Γ := by
    refine hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha
    intro g hg f hf h hh
    rw [evC_ltr]
    exact hf _ (hΓ.mul_mem _ hg _ hh)
  have hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ) := by
    refine hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb
    rintro g hg f hf _ ⟨h, hh, rfl⟩
    rw [evC_ltr, ← mul_assoc]
    exact hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩
  have hR1 : Rey 1 = 1 := hR.fix 1 (fun g _ z => by simp [evC])
  have hsum : Rey a + Rey b = 1 := by rw [← map_add (f := _), hab, hR1]
  refine ⟨Rey a, hR.inv a, ?_⟩
  have e1 : evC (Rey a) 1 = 0 := hRa 1 hΓ.one_mem
  have e2 : evC (Rey b) y = 0 := hRb y ⟨1, hΓ.one_mem, one_mul y⟩
  have e3 : evC (Rey a) y = 1 := by
    have h := congrArg (fun f => evC f y) hsum
    simp only [evC] at h e2 ⊢
    rw [map_add (f := _), e2, add_zero, map_one] at h
    exact h
  rw [e1, e3]
  exact zero_ne_one

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace DeepSquares

end DeepSquares

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exp_neg_two_mul_le_mul_of_lt {e : ℕ} {a b : ℤᵐ⁰}
    (ha : WithZero.exp (-((e : ℤ) + 1)) < a) (hb : WithZero.exp (-((e : ℤ) + 1)) < b) :
    WithZero.exp (-(2 * (e : ℤ))) ≤ a * b := by
  obtain ⟨k, rfl⟩ : ∃ k, WithZero.exp k = a := ⟨_, WithZero.exp_log (ne_bot_of_gt ha)⟩
  obtain ⟨l, rfl⟩ : ∃ l, WithZero.exp l = b := ⟨_, WithZero.exp_log (ne_bot_of_gt hb)⟩
  rw [WithZero.exp_lt_exp] at ha hb
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  intro F _ _ v e h2 x hx
  unfold _root_.GlobalTheory.QNorm.hiUnits at hx
  unfold _root_.GlobalTheory.QNorm.sqs _root_.GlobalTheory.QNorm.hiUnits
  obtain ⟨-, hx1⟩ := hx
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have h4 : w 4 = WithZero.exp (-(2 * e : ℤ)) := by
    have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    rw [this, map_mul, h2, ← WithZero.exp_add]; congr 1; ring
  have hlt : w ((x : v.adicCompletion F) - 1) < w 4 := by
    refine lt_of_le_of_lt hx1 ?_
    rw [h4, WithZero.exp_lt_exp]; push_cast; omega
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ hlt
  have hprod : w (r - 1) * w (r + 1) ≤ WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [← map_mul, show (r - 1) * (r + 1) = r * r - 1 by ring, ← hr]; exact hx1
  obtain ⟨s, hs, hs1⟩ : ∃ s : v.adicCompletion F, s * s = x ∧
      w (s - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) := by
    by_cases hm : w (r - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · exact ⟨r, hr.symm, hm⟩
    by_cases hp : w (r + 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · refine ⟨-r, by rw [neg_mul_neg, hr], ?_⟩
      rwa [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exfalso
    push_cast at hm hp hprod
    have := (exp_neg_two_mul_le_mul_of_lt (not_le.mp hm) (not_le.mp hp)).trans hprod
    rw [WithZero.exp_le_exp] at this
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact x.ne_zero hs.symm
  have hsv : w s = 1 := by
    have hlt1 : w (s - 1) < 1 :=
      hs1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using Valuation.map_one_add_of_lt w hlt1
  refine ⟨Units.mk0 s hs0, ⟨hsv, hs1⟩, ?_⟩
  ext
  simp [pow_two, hs]

end GlobalTheory.QNorm
end
