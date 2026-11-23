module

public import Development.EtaleCohomology.DivisorCycles.Bundle002
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

section

open Matrix
namespace LateralTheory.DivDb
namespace AlgStruct₂

variable {C : Type} [Field C] {N n : ℕ} {p : Fin n → Mat C N}

theorem pp (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq
theorem pp' (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, pp hp]
theorem pq (hp : Sys p) {i j : Fin n} (h : i ≠ j) : p i * p j = 0 := hp.1.ortho h
theorem pq' (hp : Sys p) {i j : Fin n} (h : i ≠ j) (X : Mat C N) : p i * (p j * X) = 0 := by
  rw [← mul_assoc, pq hp h, zero_mul]

theorem corner_comm (hp : Sys p) (X : Mat C N) (i m : Fin n) :
    p i * X * p i * p m = p m * (p i * X * p i) := by
  by_cases h : m = i
  · rw [h]; simp only [mul_assoc, pp hp, pp' hp]
  · simp only [mul_assoc, pq hp (Ne.symm h), pq' hp h, mul_zero]

theorem decomp (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, p i * a * p j * (p j * b * p k) := by
  have h1 : a * b = a * (∑ j, p j) * b := by rw [hp.1.complete, mul_one]
  rw [h1]; simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, pp' hp]

theorem expand (hp : Sys p) (Y : Mat C N) : Y = ∑ i, ∑ j, p i * Y * p j := by
  have h : Y = (∑ i, p i) * Y * (∑ j, p j) := by rw [hp.1.complete, one_mul, mul_one]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]

def S (p : Fin n → Mat C N) (g : Submodule C (Mat C N)) : Set (Mat C N) :=
  {a | (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i}

variable {g : Submodule C (Mat C N)}

theorem S_add {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a + b ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_add, add_mul]; exact g.add_mem (ha.1 i j h) (hb.1 i j h)
  · obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
    exact ⟨c + c', by rw [mul_add, add_mul, hc, hc', add_smul]⟩

theorem S_alg (hp : Sys p) (r : C) : algebraMap C (Mat C N) r ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ⟨r, ?_⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pq hp h, smul_zero]
    exact g.zero_mem
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pp hp]

theorem S_mul (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a * b ∈ S p g := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [decomp hp]
    refine g.sum_mem fun j _ => ?_
    by_cases hji : j = i
    · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i
      have e : p i * (p i * b * p k) = p i * b * p k := by simp only [mul_assoc, pp' hp]
      rw [hc, smul_mul_assoc, e]; exact g.smul_mem _ (hb.1 _ _ hik)
    by_cases hjk : j = k
    · rw [hjk]; obtain ⟨c, hc⟩ := hb.2 k
      have e : p i * a * p k * p k = p i * a * p k := by simp only [mul_assoc, pp hp]
      rw [hc, mul_smul_comm, e]; exact g.smul_mem _ (ha.1 _ _ hik)
    have h := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j k hjk)
    have z : p j * b * p k * (p i * a * p j) = 0 := by
      simp only [mul_assoc, pq' hp (Ne.symm hik), mul_zero]
    rwa [z, sub_zero] at h
  · have key : ∀ j, ∃ c : C, p i * a * p j * (p j * b * p i) = c • p i := by
      intro j
      by_cases hji : j = i
      · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
        exact ⟨c * c', by rw [hc, hc', smul_mul_assoc, mul_smul_comm, pp hp, smul_smul]⟩
      have hZ := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j i hji)
      have e1 : p i * a * p j * (p j * b * p i) = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc]
      have e2 : p j * b * p i * (p i * a * p j) = p j * (b * p i * (p i * a)) * p j := by
        simp only [mul_assoc]
      rw [e1, e2] at hZ
      have hc : ∀ m, (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) * p m =
          p m * (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) := by
        intro m; rw [sub_mul, mul_sub, corner_comm hp, corner_comm hp]
      obtain ⟨c, hcZ⟩ := hdiag _ hZ hc i
      refine ⟨c, ?_⟩
      rw [e1, ← hcZ, sub_mul]
      have f1 : p i * (a * p j * (p j * b)) * p i * p i = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc, pp hp]
      have f2 : p j * (b * p i * (p i * a)) * p j * p i = 0 := by
        simp only [mul_assoc, pq hp hji, mul_zero]
      rw [f1, f2, sub_zero]
    choose f hf using key
    exact ⟨∑ j, f j, by rw [decomp hp, Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => hf j⟩

theorem S_of_mem (hp : Sys p) (hoff : ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {Y : Mat C N} (hY : Y ∈ g) : Y ∈ S p g := by
  refine ⟨hoff Y hY, fun i => ?_⟩
  set D := ∑ k, p k * Y * p k with hDdef
  have hsplit : Y = D + ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
    conv_lhs => rw [expand hp Y]
    rw [hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hD : D ∈ g := by
    have : D = Y - ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
      rw [eq_sub_iff_add_eq, ← hsplit]
    rw [this]
    refine g.sub_mem hY (g.sum_mem fun k _ => g.sum_mem fun j hj => hoff Y hY k j ?_)
    exact Ne.symm (Finset.ne_of_mem_erase hj)
  have hcomm : ∀ m, D * p m = p m * D := by
    intro m; rw [hDdef, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => corner_comm hp Y k m
  obtain ⟨c, hc⟩ := hdiag D hD hcomm i
  refine ⟨c, ?_⟩
  rw [← hc, hDdef, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [mul_assoc, pp hp]
  · intro k _ hki; simp only [mul_assoc, pq hp hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

def Sa (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) :
    Subalgebra C (Mat C N) where
  carrier := S p g
  mul_mem' := S_mul hp hbr hdiag
  add_mem' := S_add
  algebraMap_mem' := S_alg hp

theorem AlgStruct_of : AlgStruct := by
  intro C _ N n p g hp hbr hoff hdiag a ha
  have hle : Algebra.adjoin C (g : Set (Mat C N)) ≤ Sa hp hbr hdiag :=
    Algebra.adjoin_le fun Y hY => S_of_mem hp hoff hdiag hY
  exact hle ha

end AlgStruct₂
end LateralTheory.DivDb
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DegAll₂
open LateralTheory.DivDb

theorem entries_cont {Γ K : Type} [TopologicalSpace Γ] [TopologicalSpace K] {N : ℕ}
    {φ : Γ → Mat K N} (hφ : Continuous φ) :
    Continuous (fun g => fun p : Fin N × Fin N => φ g p.1 p.2) :=
  continuous_pi fun p => (hφ.matrix_elem p.1 p.2)

theorem poly_cont {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {N : ℕ} {φ : Γ → Mat K N} (hφ : Continuous φ) (f : MP K N) :
    Continuous (fun g => MvPolynomial.aeval (fun p : Fin N × Fin N => φ g p.1 p.2) f) := by
  refine ((MvPolynomial.continuous_eval f).comp (entries_cont hφ)).congr ?_
  intro g
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

end LateralTheory.DivDb.DegAll₂

namespace LateralTheory.DivDb

theorem DegAll_of (hP : DegPoly) : DegAll := by
  intro Γ K _ _ _ _ _ _ N n ρ hρ S hS hSd g
  obtain ⟨𝓕, h𝓕⟩ := hP K N n
  rw [h𝓕 K]
  intro f hf
  have key := Continuous.ext_on hS (DegAll₂.poly_cont hρ f) continuous_const
    (fun s hs => ((h𝓕 K _).1 (hSd s hs)) f hf)
  exact congrFun key g

end LateralTheory.DivDb
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb
end

section

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.DenseAlg₂
open LateralTheory.DivDb

variable {C : Type} [Field C]

theorem pow_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) : ∀ k : ℕ, y ^ k * T = T * z ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, pow_intertwine y z T h k,
      Matrix.mul_assoc]

theorem aeval_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) (q : C[X]) : aeval y q * T = T * aeval z q := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, pow_intertwine y z T h k]

theorem sep_of_roots {n : ℕ} (q : C[X]) (hm : q.Monic) (hd : q.natDegree = n) (l : Fin n → C)
    (hl : Function.Injective l) (hr : ∀ j, q.IsRoot (l j)) : q.Separable := by
  classical
  have hq0 : q ≠ 0 := hm.ne_zero
  have hnd : ((Finset.univ : Finset (Fin n)).val.map l).Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : (Finset.univ : Finset (Fin n)).val.map l ≤ q.roots := (Multiset.le_iff_subset hnd).2 fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hr j)
  have hcs : Multiset.card ((Finset.univ : Finset (Fin n)).val.map l) = n := by simp
  have heq : (Finset.univ : Finset (Fin n)).val.map l = q.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcs, ← hd]; exact card_roots' q)
  have hcard : Multiset.card q.roots = q.natDegree := by rw [← heq, hcs, hd]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  rw [← heq, Multiset.map_map] at hprod
  have e : (∏ j, (X - Polynomial.C (l j))) = q := by rw [← hprod, Finset.prod_eq_multiset_prod]; rfl
  exact e ▸ separable_prod_X_sub_C_iff.2 hl

theorem isRoot_of_aeval {N : ℕ} (y : Mat C N) (q : C[X]) (hq : aeval y q = 0) (l : C)
    (hl : y.charpoly.IsRoot l) : q.IsRoot l := by
  have h1 : l ∈ spectrum C y := Matrix.mem_spectrum_of_isRoot_charpoly hl
  have h2 := spectrum.subset_polynomial_aeval y q ⟨l, h1, rfl⟩
  rw [hq, spectrum.mem_iff, sub_zero] at h2
  by_contra hne
  exact h2 ((IsUnit.mk0 (q.eval l) hne).map (algebraMap C (Mat C N)))

theorem DenseAlg_of (hCh : Chain) (hSP : SepPoly) : DenseAlg := by
  intro Γ C _ _ _ N n ρ r A B hSub U g m hm hE
  obtain ⟨hBA, hint, hspan⟩ := hSub
  have hr : ∀ h : Γ, B * (ρ h : Mat C N) * A = (r h : Mat C n) := fun h => by
    rw [Matrix.mul_assoc, hint h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hgu : ∀ u : Γ, (ρ g : Mat C N) * (ρ u : Mat C N) = (ρ (g * u) : Mat C N) := fun u => by
    rw [map_mul, Units.val_mul]
  by_contra hno
  push Not at hno
  obtain ⟨f, hf⟩ := hSP C n
  let φ : Mat C N →ₗ[C] Mat C n :=
    { toFun := fun x => B * (ρ g : Mat C N) * x * A
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  obtain ⟨f', hf', -⟩ := hCh C N n φ f
  have hz : ¬ (φ m).charpoly.Separable := by
    rw [hf, not_not, ← hf']
    refine hm f' fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
    rw [hf']
    have hφu : φ (((Units.coeHom (Mat C N)).comp ρ) u) = (r (g * u) : Mat C n) := by
      show B * (ρ g : Mat C N) * (ρ u : Mat C N) * A = _
      rw [Matrix.mul_assoc B, hgu, hr]
    rw [hφu]
    by_contra h
    exact hno u hu ((hf _).2 h)
  have hyT : ∀ T : Matrix (Fin N) (Fin n) C, (∀ h, (ρ h : Mat C N) * T = T * (r h : Mat C n)) →
      ((ρ g : Mat C N) * m) * T = T * φ m := by
    intro T hT
    let ψ : Mat C N →ₗ[C] Mat C N :=
      { toFun := fun x => ((ρ g : Mat C N) * x * T - T * (B * (ρ g : Mat C N) * x * A)) * B
        map_add' := fun x y => by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]; abel
        map_smul' := fun c x => by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, RingHom.id_apply, smul_sub] }
    have hψ : ψ m = 0 := by
      ext i j
      obtain ⟨f2, hf2, -⟩ := hCh C N N ψ (MvPolynomial.X (i, j))
      have h0 : ev m f2 = 0 := by
        refine hm f2 fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
        rw [hf2]
        have hψu : ψ (((Units.coeHom (Mat C N)).comp ρ) u) = 0 := by
          show (((ρ g : Mat C N) * (ρ u : Mat C N) * T -
            T * (B * (ρ g : Mat C N) * (ρ u : Mat C N) * A)) * B) = 0
          rw [Matrix.mul_assoc B, hgu, hr, hT, sub_self, Matrix.zero_mul]
        rw [hψu]; simp [ev]
      rw [hf2] at h0
      simpa [ev] using h0
    have h2 : ((ρ g : Mat C N) * m * T - T * φ m) * B * A = 0 := by
      have e : ψ m = ((ρ g : Mat C N) * m * T - T * φ m) * B := rfl
      rw [← e, hψ, Matrix.zero_mul]
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one] at h2
    exact sub_eq_zero.1 h2
  have hqy : aeval ((ρ g : Mat C N) * m) (φ m).charpoly = 0 := by
    apply hspan
    intro T hT
    rw [aeval_intertwine _ _ T (hyT T hT), Matrix.aeval_self_charpoly, Matrix.mul_zero]
  obtain ⟨l, hl, hlr⟩ := hE
  exact hz (sep_of_roots _ (Matrix.charpoly_monic _) (by simp [Matrix.charpoly_natDegree_eq_dim]) l hl
    fun j => isRoot_of_aeval _ _ hqy (l j) (hlr j))

end LateralTheory.DivDb.DenseAlg₂
end
