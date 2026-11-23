module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain
open _root_.Formalism.L2.DIV _root_.Formalism.L2.Col GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (v : InfinitePlace K)

theorem pairAt_add_left (x y z : S.V) : S.pairAt v (x + y) z = S.pairAt v x z + S.pairAt v y z := by
  simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (x y z : S.V) : S.pairAt v x (y + z) = S.pairAt v x y + S.pairAt v x z := by
  simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pairAt_zero_left (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem pairAt_zero_right (y : S.V) : S.pairAt v y 0 = 0 := by
  simp [GSD.pairAt]

theorem pairAt_sum_left {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v (∑ i ∈ s, x i) y = ∑ i ∈ s, S.pairAt v (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_left, ih]

theorem pairAt_sum_right {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v y (∑ i ∈ s, x i) = ∑ i ∈ s, S.pairAt v y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_right, ih]

theorem pairAt_self_nonneg (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have h1 := h.dotProduct_mulVec_nonneg (fun i => v.embedding (S.bV.repr x i))
  have h2 : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      (S.gramV.map v.embedding) *ᵥ (fun i => v.embedding (S.bV.repr x i)) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
    rfl
  rw [h2]
  exact (Complex.nonneg_iff.mp h1).1

theorem pairAt_smul_self (a : K) (x : S.V) :
    (S.pairAt v (a • x) (a • x)).re = ‖v.embedding a‖ ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_left, pairAt_smul_right, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem pairAt_inv_nat_smul_self (n : ℕ) (x : S.V) :
    (S.pairAt v (((n : K))⁻¹ • x) (((n : K))⁻¹ • x)).re = ((n : ℝ)⁻¹) ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_self]
  simp

theorem pairAt_cross_le (h : PosAt S v) (x y : S.V) :
    (S.pairAt v x y).re + (S.pairAt v y x).re ≤ (S.pairAt v x x).re + (S.pairAt v y y).re := by
  have h1 := pairAt_self_nonneg S v h (x + (-1 : K) • y)
  rw [pairAt_add_left, pairAt_add_right, pairAt_add_right, pairAt_smul_left, pairAt_smul_left,
    pairAt_smul_right, pairAt_smul_right] at h1
  simp at h1
  linarith

theorem pairAt_sum_le (h : PosAt S v) {α : Type*} (s : Finset α) (x : α → S.V) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ (s.card : ℝ) * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re := by
  have e1 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x i) (x j)).re := by
    rw [pairAt_sum_left, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pairAt_sum_right, Complex.re_sum]
  have e2 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x j) (x i)).re := by
    rw [e1, Finset.sum_comm]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x j)).re + (S.pairAt v (x j) (x i)).re) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x i)).re + (S.pairAt v (x j) (x j)).re) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairAt_cross_le S v h _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at e3
  linarith

theorem ipAt_re (h : S.Ok) (φ ψ : S.D → S.V) :
    (S.ipAt h v φ ψ).re = ∑ c ∈ @Finset.univ _ h.fintypeCl,
      (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem ipAt_self_nonneg (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) : 0 ≤ (S.ipAt h v φ φ).re := by
  rw [ipAt_re]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (pairAt_self_nonneg S v hp _)

theorem ipAt_self_le (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) (B : ℝ)
    (hB : ∀ d, (S.pairAt v (φ d) (φ d)).re ≤ B) : (S.ipAt h v φ φ).re ≤ (Nat.card S.Cl : ℝ) * B := by
  rw [ipAt_re]
  letI := h.fintypeCl
  calc _ ≤ ∑ _c : S.Cl, B := Finset.sum_le_sum fun c _ => by
        have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
        exact ((mul_le_mul_of_nonneg_right (inv_nat_le_one _) h0).trans (by rw [one_mul])).trans (hB _)
    _ = _ := by simp [Nat.card_eq_fintype_card]


variable {S} in
theorem appOf_le {S' : GSD K} (A : ClsKer S S') (h : S.Ok) (hp : PosAt S v) (hp' : PosAt S' v) (t : ℝ) (ht : 0 ≤ t)
    (φ : S.D → S.V) (d' : S'.D) (hA : ∀ d, OpLe S S' v (A.k d d') t) :
    (S'.pairAt v (A.appOf h S.outSec φ d') (A.appOf h S.outSec φ d')).re ≤
      (Nat.card S.Cl : ℝ) * (t * (S.ipAt h v φ φ).re) := by
  letI := h.fintypeCl
  unfold ClsKer.appOf
  refine (pairAt_sum_le S' v hp' _ _).trans ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card, ipAt_re, Finset.mul_sum _ _ t]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [pairAt_inv_nat_smul_self]
  have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
  have h1 := hA (S.outSec.rep c) (φ (S.outSec.rep c))
  have h2 := inv_nat_le_one ((S.toCSD h).wt c)
  have h3 : (0 : ℝ) ≤ (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := by positivity
  change (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ ^ 2 * _ ≤ _
  generalize (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ = w at *
  calc _ ≤ w ^ 2 * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ w * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.ColNorms.SumBound
end
end

section

noncomputable section

namespace GlobalTheory.ColNorms.DatOne

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem mem_lamY_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) :
    v ∈ LocE.lamY P q n c ex ↔ ∀ l : Fin (n + c), _root_.Formalism.L2.Col.IntAt P (((q : E) ^ LocE.scE n ex l.1)⁻¹ * v l) := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap]
  exact mem_localization_standardLattice P _

theorem proj_mem {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ} {ex : ℕ → ℕ} {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c ex) :
    LinearMap.funLeft E E (Fin.castAdd c) v ∈ stdAt E n P := by
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := (mem_lamY_iff P q n c ex v).1 hv (Fin.castAdd c i)
  simpa [LocE.scE, LinearMap.funLeft_apply] using h

theorem proj_inX {n c : ℕ} (y : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c y) = y := by
  funext i
  simp [LinearMap.funLeft_apply, Loc.inX]

theorem inX_mem_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (y : Sp E n) :
    Loc.inX E n c y ∈ LocE.lamY P q n c ex ↔ y ∈ stdAt E n P := by
  constructor
  · intro h
    simpa [proj_inX] using proj_mem h
  · intro h
    refine (mem_lamY_iff P q n c ex _).2 fun l => ?_
    by_cases hl : l.1 < n
    · have := (mem_localization_standardLattice P _).1 h ⟨l.1, hl⟩
      simpa [LocE.scE, Loc.inX, hl] using this
    · have := _root_.Formalism.L2.Col.IntAt.coe P (0 : 𝓞 E)
      simpa [Loc.inX, hl] using this

theorem joinCol_inX {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (y : Sp E n') :
    (joinCol x₀ y' : HomE E (n' + c') (n + c)) (Loc.inX E n' c' y) = Loc.inX E n c (x₀ y) := by
  have h0 : atNL E (n' + c') n' (Loc.inX E n' c' y) = 0 := by
    unfold atNL
    split_ifs with h
    · simp [Loc.inX]
    · rfl
  simp [joinCol, proj_inX, h0]

theorem joinCol_add {n' c' n c : ℕ} (x₀ z : HomE E n' n) (t : E) (y' : Sp E n) :
    (joinCol (x₀ + t • z) y' : HomE E (n' + c') (n + c)) =
      joinCol x₀ y' + t • (Loc.inX E n c ∘ₗ z ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  abel

theorem locSmall_joinCol {P : HeightOneSpectrum (𝓞 E)} {q n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {Φ : HomE E (n' + c') (n + c) → K} {β : ℝ}
    (h : LocSmall q (LocE.lamY P q n' c' ex') (LocE.lamY P q n c ex) Φ β) (y' : Sp E n) :
    LocSmall q (stdAt E n' P) (stdAt E n P) (fun x₀ => Φ (joinCol x₀ y')) β := by
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => h.2.2 σ _⟩
  · have := h.1 _ hx _ ((inX_mem_iff P q n' c' ex' y).2 hy)
    rw [joinCol_inX] at this
    exact (inX_mem_iff P q n c ex _).1 this
  · show Φ (joinCol (x + (q : E) • z) y') = Φ (joinCol x y')
    rw [joinCol_add]
    exact h.2.1 _ _ fun v hv => (inX_mem_iff P q n c ex _).2 (hz _ (proj_mem hv))

theorem smallDatum_of_frames {a b : ℕ} {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (d : Deco E a ST SG) (d' : DecoSet (E := E) (n := b) (ST := ST) (SG := SG'))
    (f : Frs E a SB) (f' : Frs E b SB) (hf : ∀ (P : SB) x, f P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1)
    (hf' : ∀ (P : SB) x, f' P x ∈ d'.1.at P.1 ↔ x ∈ stdAt E b P.1) (c : ℕ) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (hT : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (Ψ : SB → HomE E a b → K) (β : SB → ℝ)
    (hΨ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Ψ P) (β P)) :
    SmallDatum (ST ∪ SB) d.N d'.1.N c (fun x => phiT K d d'.1 x * ∏ P : SB, Ψ P (inFr (f P) (f' P) x)) (∏ P, β P) := by
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rcases Finset.mem_union.1 hP with hP | hP
    · unfold phiT at h1
      split_ifs at h1 with h
      · exact (h ⟨P, hP⟩ y hy).1
      · exact absurd rfl h1
    · have h3 := Finset.prod_ne_zero_iff.1 h2 ⟨P, hP⟩ (Finset.mem_univ _)
      have h4 : (f ⟨P, hP⟩).symm y ∈ stdAt E a P := (hf ⟨P, hP⟩ _).1 (by simpa using hy)
      have h5 := (hf' ⟨P, hP⟩ _).2 ((hΨ ⟨P, hP⟩).1 _ h3 _ h4)
      simpa [inFr] using h5
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    have hz' : ∀ P ∈ ST ∪ SB, ∀ y ∈ d.at P, z y ∈ d'.1.at P := hz
    have e0 : (((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z) = (c : 𝓞 E) • z := rfl
    rw [e0]
    show phiT K d d'.1 _ * _ = phiT K d d'.1 _ * _
    congr 1
    · unfold phiT
      classical
      refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun P => forall_congr' fun y => forall_congr' fun hy => ?_) rfl rfl
      have hzy : z y ∈ d'.1.at P.1 := hz' P.1 (Finset.mem_union_left _ P.2) y hy
      have hc : (c : 𝓞 E) • z y ∈ d'.1.at P.1 := Submodule.smul_mem _ _ hzy
      have e : (x + (c : 𝓞 E) • z) y = x y + (c : 𝓞 E) • z y := rfl
      rw [e, Submodule.add_mem_iff_left _ hc]
      refine and_congr_right fun hx => ?_
      rw [d'.2.f_add P _ hx _ hc, d'.2.f_smul P _ _ hzy, Ideal.Quotient.eq_zero_iff_mem.2 (hT P.1 P.2), zero_mul, add_zero]
    · refine Finset.prod_congr rfl fun P _ => ?_
      obtain ⟨k, hk⟩ := hq P
      have e : inFr (f P) (f' P) (x + (c : 𝓞 E) • z) =
          inFr (f P) (f' P) x + (q P : E) • inFr (f P) (f' P) (k • z) := by
        refine LinearMap.ext fun v => ?_
        have : (c : 𝓞 E) • z = (q P : E) • (k • z) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hk, mul_smul]
        rw [this]
        simp [inFr]
      rw [e]
      refine (hΨ P).2.1 _ _ fun v hv => (hf' P _).1 ?_
      have := nsmul_mem (hz' P.1 (Finset.mem_union_right _ P.2) _ ((hf P v).2 hv)) k
      simpa [inFr] using this
  · show ‖σ (phiT K d d'.1 x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ‖σ (phiT K d d'.1 x)‖ ≤ 1 := by
      unfold phiT
      split_ifs <;> simp
    have h2 : ∏ P : SB, ‖σ (Ψ P (inFr (f P) (f' P) x))‖ ≤ ∏ P, β P :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => (hΨ P).2.2 σ _
    calc _ ≤ 1 * ∏ P, β P := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Generic

end GlobalTheory.ColNorms.DatOne
end
end

section

noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace EntryDatum

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (c : 𝓞 E) (hc : ∀ P ∈ ST, c ∈ P.asIdeal) (x z : HomE E a b)
    (hz : ∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) : phiT K d d' (x + c • z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y := by
    intro x z hz h P y hy
    obtain ⟨h1, h2⟩ := h P y hy
    have h3 := hz P.1 P.2 y hy
    have h4 : c • z y ∈ d'.at P.1 := Submodule.smul_mem _ c h3
    have e : (x + c • z) y = x y + c • z y := rfl
    rw [e]
    refine ⟨add_mem h1 h4, ?_⟩
    rw [hd'.f_add P _ h1 _ h4, hd'.f_smul P c _ h3, Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul, add_zero, h2]
  have hiff : (∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := by
    refine ⟨fun h => ?_, key x z hz⟩
    have h' := key (x + c • z) (-z) (fun P hP y hy => neg_mem (hz P hP y hy)) h
    have e : x + c • z + c • (-z) = x := by rw [smul_neg, add_neg_cancel_right]
    rwa [e] at h'
  unfold phiT
  by_cases h : ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem phiT_support {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) (hx : phiT K d d' x ≠ 0) : ∀ P ∈ ST, ∀ y ∈ d.at P, x y ∈ d'.at P := by
  intro P hP y hy
  unfold phiT at hx
  split_ifs at hx with h
  · exact (h ⟨P, hP⟩ y hy).1
  · exact absurd rfl hx

theorem norm_phiT_le {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (σ : K →+* ℂ) (x : HomE E a b) : ‖σ (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem inFr_maps_iff (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    {M M₀ : Submodule (𝓞 E) (Sp E a)} {M' M₀' : Submodule (𝓞 E) (Sp E b)}
    (hf : ∀ x, f x ∈ M ↔ x ∈ M₀) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ M₀') (x : HomE E a b) :
    (∀ y ∈ M₀, inFr f f' x y ∈ M₀') ↔ ∀ y ∈ M, x y ∈ M' := by
  have e : ∀ y, f' (inFr f f' x y) = x (f y) := fun y => by simp [inFr]
  constructor
  · intro h y hy
    have h1 : f.symm y ∈ M₀ := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h _ h1)
    rw [e] at h2
    simpa using h2
  · intro h y hy
    rw [← hf', e]
    exact h _ ((hf y).2 hy)

theorem inFr_add_smul (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x z : HomE E a b) (q k : ℕ) :
    inFr f f' (x + ((q * k : ℕ) : 𝓞 E) • z) = inFr f f' x + (q : E) • inFr f f' ((k : 𝓞 E) • z) := by
  have e : ∀ n : ℕ, ((n : ℕ) : 𝓞 E) • z = (n : E) • z := fun n => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, e]
  refine LinearMap.ext fun y => ?_
  simp [inFr, mul_smul]

theorem smallDatum_prod {ST SG SG' SB S : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (hd' : d'.Ok) (fr : Frs E a SB) (fr' : Frs E b SB)
    (hfr : ∀ (P : SB) x, fr P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1) (hfr' : ∀ (P : SB) x, fr' P x ∈ d'.at P.1 ↔ x ∈ stdAt E b P.1)
    (hS : ∀ P, P ∈ S ↔ P ∈ ST ∨ P ∈ SB) (c : ℕ) (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (Φ : SB → HomE E a b → K) (β : SB → ℝ) (hΦ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Φ P) (β P)) :
    SmallDatum S d.N d'.N c (fun x => phiT K d d' x * ∏ P : SB, Φ P (inFr (fr P) (fr' P) x)) (∏ P : SB, β P) := by
  refine ⟨fun x hx P hP => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · rcases (hS P).1 hP with h | h
    · exact phiT_support d d' x (left_ne_zero_of_mul hx) P h
    · have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h⟩ (Finset.mem_univ _)
      exact (inFr_maps_iff _ _ (hfr ⟨P, h⟩) (hfr' ⟨P, h⟩) x).1 ((hΦ ⟨P, h⟩).1 _ h1)
  · obtain ⟨z, hz, rfl⟩ := hy
    have e : ((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z = (c : 𝓞 E) • z := rfl
    rw [e]
    show phiT K d d' _ * _ = phiT K d d' _ * _
    rw [phiT_add d d' hd' _ hc x z (fun P hP => hz P ((hS P).2 (Or.inl hP)))]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk⟩ := hq P
    rw [hk, inFr_add_smul]
    refine (hΦ P).2.1 _ _ ?_
    refine (inFr_maps_iff _ _ (hfr P) (hfr' P) _).2 fun y hy => ?_
    exact Submodule.smul_mem _ (k : 𝓞 E) (hz P.1 ((hS P.1).2 (Or.inr P.2)) y hy)
  · show ‖σ (phiT K d d' x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ ≤ ∏ P : SB, β P :=
      Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => (hΦ P).2.2 σ _
    have h0 : 0 ≤ ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ := Finset.prod_nonneg fun P _ => norm_nonneg _
    exact (mul_le_of_le_one_left h0 (norm_phiT_le d d' σ x)).trans h1

end EntryDatum

end GlobalTheory.ColNorms
end
end

section

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.PresSum

theorem cj_mul_of_mem (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {a b : ℂ} (ha : a ∈ M) (hb : b ∈ M) :
    StandardLatticesGL3.cj M ρ (a * b) = StandardLatticesGL3.cj M ρ a * StandardLatticesGL3.cj M ρ b := by
  unfold StandardLatticesGL3.cj TaylorLogMetric.liftM
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (mul_mem ha hb), ← map_mul]
  rfl

variable {D : D7} {T : TaylorLogMetric.Tor D} {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F₀ : TaylorLogMetric.VC D a b → ℂ}

theorem pres_zero : Pres D T L L' F₀ (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp, by
    funext z; simp [StandardLatticesGL3.comb]⟩

theorem pres_add {F G : TaylorLogMetric.VC D a b → ℂ} {n m : ℝ} (hF : Pres D T L L' F₀ F n) (hG : Pres D T L L' F₀ G m) :
    Pres D T L L' F₀ (fun z => F z + G z) (n + m) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  obtain ⟨k', r', y', h1', h2', h3', rfl⟩ := hG
  refine ⟨k + k', Fin.append r r', Fin.append y y', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h1 j
    · rw [Fin.append_right]; exact h1' j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h2 j
    · rw [Fin.append_right]; exact h2' j
  · intro ρ
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact add_le_add (h3 ρ) (h3' ρ)
  · funext z
    simp only [StandardLatticesGL3.comb, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem pres_smul {F : TaylorLogMetric.VC D a b → ℂ} {n β : ℝ} {c : ℂ} (hβ : 0 ≤ β) (hF : Pres D T L L' F₀ F n)
    (hc : c ∈ TaylorLogMetric.Qbar) (hb : ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ c‖ ≤ β) :
    Pres D T L L' F₀ (fun z => c * F z) (β * n) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  refine ⟨k, fun i => c * r i, y, fun i => mul_mem hc (h1 i), h2, fun ρ => ?_, ?_⟩
  · simp only [fun i => cj_mul_of_mem TaylorLogMetric.Qbar ρ hc (h1 i), norm_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul (hb ρ) (h3 ρ) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hβ
  · funext z
    simp only [StandardLatticesGL3.comb, Finset.mul_sum, mul_assoc]

theorem pres_sum : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  intro D T a b L L' F₀ α R c F n β hβ hF hc
  classical
  induction R using Finset.induction_on with
  | empty => simpa using pres_zero
  | insert x s hx ih =>
    have h1 := pres_smul hβ (hF x (Finset.mem_insert_self _ _)) (hc x (Finset.mem_insert_self _ _)).1
      (hc x (Finset.mem_insert_self _ _)).2
    have h2 := ih (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (fun y hy => hc y (Finset.mem_insert_of_mem hy))
    have h3 := pres_add h1 h2
    have e : ((insert x s).card : ℝ) * β * n = β * n + s.card * β * n := by
      rw [Finset.card_insert_of_notMem hx]; push_cast; ring
    rw [e]
    simpa only [Finset.sum_insert hx] using h3

end GlobalTheory.PresSum
end
