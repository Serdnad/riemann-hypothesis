module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_summand_of_quot

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {E : Type} [AddCommGroup E] [Module Ω E]

def toSub (L : AddSubgroup E) (h : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : Submodule R E where
  carrier := L
  add_mem' := fun ha hb => L.add_mem ha hb
  zero_mem' := L.zero_mem
  smul_mem' := fun a e he => h a a.2 e he

theorem exists_dual {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) :
    Module.finrank Ω E = r ∧ ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → E),
      (∀ i, v i ∈ L) ∧ (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • v i = e := by
  have h' : LocFree R r (toSub R L h.1).toAddSubgroup := h
  refine ⟨(LocFreeProj.main R r (toSub R L h.1) h').2.2.1, ?_⟩
  obtain ⟨k, f, c, B, hsum, hgen, hcoord⟩ := LocFreeProj.exists_charts h'
  choose n0 hn0 using hgen
  have hs : ∀ j q, ((f j : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2)) • B j q ∈ toSub R L h.1 :=
    fun j q => LocFreeProj.pow_smul_mem (f j)
      (Finset.le_sup (f := fun i : Fin k × Fin r => n0 i.1 i.2) (Finset.mem_univ (j, q))) (hn0 j q)
  generalize hN0 : (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2) = N0 at hs
  have hP0 : ∀ (l : Fin k) (p : Fin r) (jq : Fin k × Fin r),
      ∃ n, (f l : Ω) ^ n * (B l).repr ((f jq.1 : Ω) ^ N0 • B jq.1 jq.2) p ∈ R :=
    fun l p jq => hcoord l p _ (hs jq.1 jq.2)
  choose nP hnP using hP0
  have hbound : ∀ e ∈ toSub R L h.1, ∀ l p,
      (f l : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) * (B l).repr e p ∈ R := by
    intro e he l p
    choose m hm using fun (jq : Fin k × Fin r) => hcoord jq.1 jq.2 e he
    obtain ⟨d, hd⟩ := LocFreeProj.exists_pow_cover f c hsum (Finset.univ.sup m + N0)
    have hexp := LocFreeProj.expand f d B (Finset.univ.sup m) N0 hd e
    have key : (B l).coord p e = ∑ i : Fin k × Fin r,
        ((d i.1 : Ω) * ((f i.1 : Ω) ^ (Finset.univ.sup m) * (B i.1).repr e i.2)) *
          (B l).coord p ((f i.1 : Ω) ^ N0 • B i.1 i.2) := by
      conv_lhs => rw [← hexp]

      simp only [map_sum, map_smul, smul_eq_mul]
    rw [← Module.Basis.coord_apply, key, Finset.mul_sum]
    refine R.sum_mem fun i _ => ?_
    rw [mul_left_comm]
    refine R.mul_mem (R.mul_mem (d i.1).2
      (LocFreeProj.pow_mul_mem (f i.1) (Finset.le_sup (Finset.mem_univ i)) (hm i))) ?_
    rw [Module.Basis.coord_apply]
    exact LocFreeProj.pow_mul_mem (f l)
      (Finset.le_sup (f := fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2)
        (Finset.mem_univ (l, p, i))) (hnP l p i)
  generalize (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) = P at hbound
  obtain ⟨d', hd'⟩ := LocFreeProj.exists_pow_cover f c hsum (P + N0)
  refine ⟨k, fun i => ((d' i.1 : Ω) * (f i.1 : Ω) ^ P) • (B i.1).coord i.2,
    fun i => (f i.1 : Ω) ^ N0 • B i.1 i.2, fun i => hs i.1 i.2, ?_, ?_⟩
  · intro i e he
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [mul_assoc]
    exact R.mul_mem (d' i.1).2 (hbound e he i.1 i.2)
  · intro e
    have hx := LocFreeProj.expand f d' B P N0 hd' e
    convert hx using 2 with i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, mul_assoc]

theorem locFree_of_dual {ι : Type} [Fintype ι] {r : ℕ} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) (hr : Module.finrank Ω E = r)
    (φ : ι → Module.Dual Ω E) (v : ι → E) (hvL : ∀ i, v i ∈ L) (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R)
    (hv : ∀ e, ∑ i, φ i e • v i = e) : LocFree R r L := by
  have h1 := LocFreeProj.finite_projective (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  have h2 := LocFreeProj.isBaseChange (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  exact LocFreeProj.locFree_of_projective R r (toSub R L hL) h1.1 h1.2 hr h2

end PositivityTheory.Xgn.A_summand_of_quot

open PositivityTheory.Xgn.A_summand_of_quot in
theorem PositivityTheory.Xgn.summand_iff_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  intro o Ω _ _ _ R V _ _ U N m L hN
  have hst : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L := hN.1
  constructor
  · intro hm
    obtain ⟨-, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hm
    have hlift : ∀ i, ∃ e ∈ L, U.mkQ e = v i := fun i => by
      obtain ⟨e, he, hev⟩ := AddSubgroup.mem_map.1 (hv i)
      exact ⟨e, he, hev⟩
    choose w hw hwv using hlift
    have hkey : ∀ x : V ⧸ U, U.mkQ (∑ i, φ i x • w i) = x := by
      intro x

      rw [map_sum]
      simp only [map_smul, hwv]
      exact hsum x
    refine ⟨LinearMap.id - (∑ i, LinearMap.smulRight (φ i) (w i)) ∘ₗ U.mkQ, ?_, ?_, ?_⟩
    · intro x
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply, map_sub, hkey, sub_self]
    · intro u hu
      have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).2 hu
      simp [h0]
    · intro e he
      have hme : U.mkQ e ∈ AddSubgroup.map U.mkQ.toAddMonoidHom L := AddSubgroup.mem_map_of_mem _ he
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply]
      exact sub_mem he (AddSubgroup.sum_mem _ fun i _ => hst _ (hφ i _ hme) _ (hw i))
  · rintro ⟨ρ, hρU, hρid, hρL⟩
    obtain ⟨hrank, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hN
    have hfin : Module.Finite Ω V := by
      refine Module.Finite.of_surjective (∑ i, LinearMap.smulRight (LinearMap.proj i : (Fin k × Fin N → Ω) →ₗ[Ω] Ω) (v i)) ?_
      intro e
      refine ⟨fun i => φ i e, ?_⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
      exact hsum e
    constructor
    · refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R (fun a ha e he => hst a ha _ he) rfl
        (fun i => (φ i).comp U.subtype) (fun i => ⟨ρ (v i), hρU _⟩) (fun i => hρL _ (hv i))
        (fun i e he => hφ i _ he) ?_
      intro e
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.comp_apply, Submodule.subtype_apply]
      calc ∑ i, φ i e • ρ (v i) = ρ (∑ i, φ i e • v i) := by simp [map_sum, map_smul]
        _ = e := by rw [hsum]; exact hρid _ e.2
    · have hker : ∀ i, U ≤ LinearMap.ker ((φ i).comp (LinearMap.id - ρ)) := by
        intro i u hu
        simp [LinearMap.mem_ker, hρid u hu]
      refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R ?_ ?_
        (fun i => U.liftQ ((φ i).comp (LinearMap.id - ρ)) (hker i)) (fun i => U.mkQ (v i))
        (fun i => AddSubgroup.mem_map_of_mem _ (hv i)) ?_ ?_
      · intro a ha x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        refine AddSubgroup.mem_map.2 ⟨a • e, hst a ha e he, ?_⟩
        simp
      · rw [← hrank, ← Submodule.finrank_quotient_add_finrank U]
        omega
      · intro i x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        simp only [LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        exact hφ i _ (sub_mem he (hρL e he))
      · intro x
        obtain ⟨e, rfl⟩ := U.mkQ_surjective x
        simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.id_apply]
        have h1 : ∑ i, φ i (e - ρ e) • (Submodule.Quotient.mk (v i) : V ⧸ U) =
            U.mkQ (∑ i, φ i (e - ρ e) • v i) := by

          simp [map_sum, map_smul]
        rw [h1, hsum, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero U).2 (hρU e), sub_zero]
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualFrame

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f a : Ω}
    (hf : f ∈ R) {m n : ℕ} (hmn : m ≤ n) (h : f ^ m * a ∈ R) : f ^ n * a ∈ R := by
  have key : f ^ n * a = f ^ (n - m) * (f ^ m * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  rw [key]
  exact R.mul_mem (R.pow_mem hf _) h

theorem exists_unif {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f : Ω}
    (hf : f ∈ R) {m : ℕ} (a : Fin m → Ω) (h : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) :
    ∃ n : ℕ, ∀ q, f ^ n * a q ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun q => ?_⟩
  exact pow_mul_mem hf (Finset.le_sup (Finset.mem_univ q)) (hn q)

theorem exists_dual {Ω : Type} [Field Ω] {r : ℕ} (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤) :
    ∃ d : Fin r → Fin r → Ω, (∀ (a : Fin r → Ω) (q : Fin r), (∑ p, a p • b p) ⬝ᵥ d q = a q) ∧
      ∀ e : Fin r → Ω, e = ∑ q, (b q ⬝ᵥ e) • d q := by
  classical
  let M : Matrix (Fin r) (Fin r) Ω := Matrix.of b
  have hu : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have hrow : ∀ p q, b p ⬝ᵥ (fun i => M⁻¹ i q) = if p = q then 1 else 0 := by
    intro p q
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  refine ⟨fun q i => M⁻¹ i q, ?_, ?_⟩
  · intro a q
    rw [sum_dotProduct]
    simp_rw [smul_dotProduct, hrow]
    simp
  · intro e
    have h := Matrix.mulVec_mulVec e M⁻¹ M
    rw [Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec] at h
    funext i
    calc e i = Matrix.mulVec M⁻¹ (Matrix.mulVec M e) i := by rw [h]
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro q _
        rw [mul_comm]
        rfl

theorem main {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) {m : ℕ} (s : Fin m → Fin r → Ω) (hs : ∀ k, s k ∈ L)
    (hgen : ∀ e ∈ L, ∃ a : Fin m → Ω, (∀ k, a k ∈ R) ∧ e = ∑ k, a k • s k)
    {f : Ω} (hf : f ∈ R) (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hfr : ∀ e : Fin r → Ω, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ d : Fin r → Fin r → Ω, LinearIndependent Ω d ∧
      Submodule.span Ω (Set.range d) = ⊤ ∧ ∀ e : Fin r → Ω,
        ((∃ n : ℕ, f ^ n • e ∈ dotDual R L) ↔
          ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • d q) := by
  classical
  obtain ⟨d, hd1, hd2⟩ := exists_dual b hli hsp
  have hδ : ∀ p q, b p ⬝ᵥ d q = if p = q then 1 else 0 := by
    intro p q
    have h := hd1 (Pi.single p 1) q
    have hs : (∑ p', (Pi.single p (1 : Ω) : Fin r → Ω) p' • b p') = b p := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro p' _ hp'
        simp [Pi.single_eq_of_ne hp']
      · simp
    rw [hs] at h
    rw [h]
    by_cases hpq : p = q
    · subst hpq
      simp
    · simp [hpq, Pi.single_eq_of_ne (Ne.symm hpq)]
  have hcoord : ∀ (a : Fin r → Ω) q, b q ⬝ᵥ (∑ p, a p • d p) = a q := by
    intro a q
    rw [dotProduct_sum]
    simp_rw [dotProduct_smul, hδ]
    simp
  have hli' : LinearIndependent Ω d := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have h := hcoord g q
    rw [hg, dotProduct_zero] at h
    exact h.symm
  have hsp' : Submodule.span Ω (Set.range d) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    rw [hd2 e]
    exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩))
  choose c hc hce using fun k => (hfr (s k)).mp ⟨0, by simpa using hs k⟩
  refine ⟨d, hli', hsp', fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => b q ⬝ᵥ e, fun q => ?_, hd2 e⟩
    have hbq : ∃ N : ℕ, f ^ N • b q ∈ L := by
      apply (hfr (b q)).mpr
      refine ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          simp
        · simp [Pi.single_eq_of_ne hpq]
      · rw [Finset.sum_eq_single q]
        · simp
        · intro p _ hp
          simp [Pi.single_eq_of_ne hp]
        · simp
    obtain ⟨N, hN⟩ := hbq
    refine ⟨N + n, ?_⟩
    have h := (mem_dotDual R L _).mp hn _ hN
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
    show f ^ (N + n) * (b q ⬝ᵥ e) ∈ R
    rw [pow_add, mul_assoc]
    exact h
  · rintro ⟨a, ha, rfl⟩
    have hsk : ∀ k, s k ⬝ᵥ (∑ p, a p • d p) = ∑ p, c k p * a p := by
      intro k
      rw [hce k, sum_dotProduct]
      simp_rw [smul_dotProduct, hcoord, smul_eq_mul]
    have hk : ∀ k, ∃ n : ℕ, f ^ n * (s k ⬝ᵥ (∑ p, a p • d p)) ∈ R := by
      intro k
      obtain ⟨n, hn⟩ := exists_unif hf (fun p => c k p * a p) (fun p => by
        obtain ⟨n1, h1⟩ := hc k p
        obtain ⟨n2, h2⟩ := ha p
        refine ⟨n1 + n2, ?_⟩
        have hm : f ^ (n1 + n2) * (c k p * a p) = (f ^ n1 * c k p) * (f ^ n2 * a p) := by ring
        rw [hm]
        exact R.mul_mem h1 h2)
      refine ⟨n, ?_⟩
      rw [hsk k, Finset.mul_sum]
      exact sum_mem (fun p _ => hn p)
    obtain ⟨N, hN⟩ := exists_unif hf (fun k => s k ⬝ᵥ (∑ p, a p • d p)) hk
    refine ⟨N, (mem_dotDual R L _).mpr fun l hl => ?_⟩
    obtain ⟨g, hg, rfl⟩ := hgen l hl
    rw [sum_dotProduct]
    refine sum_mem (fun k _ => ?_)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact R.mul_mem (hg k) (hN k)

end PositivityTheory.Xgn.HodgeDualFrame

theorem PositivityTheory.Xgn.hodge_dual_frame_exists : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  intro O _ Ω _ _ ι x r B hB i hi
  obtain ⟨k, f, c, hf, hc, hsum, hfr⟩ := B.frame i hi
  refine ⟨k, f, c, hf, hc, hsum, fun l => ?_⟩
  obtain ⟨b, hli, hsp, hb⟩ := hfr l
  obtain ⟨m, s, hs, hgen⟩ := hB i hi
  exact PositivityTheory.Xgn.HodgeDualFrame.main (chartRing O x i) (B.lat i) s hs hgen
    (hf l) b hli hsp hb
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualOverlap

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

end PositivityTheory.Xgn.HodgeDualOverlap

private theorem exists_div_pow_mul_mem_chartRing {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : Type}
    (x : ι → Ω) (i j : ι) (hi : x i ≠ 0) (y : Ω) (hy : y ∈ chartRing O x i) :
    ∃ d : ℕ, (x i / x j) ^ d * y ∈ chartRing O x j := by
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  have mono : ∀ z : Ω, ∀ d n : ℕ, d ≤ n → (x i / x j) ^ d * z ∈ chartRing O x j →
      (x i / x j) ^ n * z ∈ chartRing O x j := by
    intro z d n hdn hz
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdn
    rw [pow_add, mul_comm ((x i / x j) ^ d), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hz
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, rfl⟩ := hz
    refine ⟨1, ?_⟩
    have h : (x i / x j) ^ 1 * (x t / x i) = x t / x j := by
      rw [pow_one, div_mul_div_comm, mul_comm (x i), mul_div_mul_right _ _ hi]
    rw [h]
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (mono _ d _ (by omega) hd) (mono _ e _ (by omega) he)
  | mul a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    have h : (x i / x j) ^ (d + e) * (a * b) = ((x i / x j) ^ d * a) * ((x i / x j) ^ e * b) := by
      ring
    rw [h]
    exact Subalgebra.mul_mem _ hd he

open PositivityTheory.Xgn.HodgeDualOverlap in
theorem PositivityTheory.Xgn.hodge_dual_lattice_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  intro O _ Ω _ _ ι x r L _ h2 h3 i j hi hj e he
  rw [mem_dotDual] at he
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  obtain ⟨n, s, hs, hgen⟩ := h3 j hj
  have hk : ∀ k, ∃ m : ℕ, (x i / x j) ^ m * (s k ⬝ᵥ e) ∈ chartRing O x j := by
    intro k
    obtain ⟨a, ha⟩ := h2 j i hj hi (s k) (hs k)
    have hmem := he _ ha
    rw [smul_dotProduct, smul_eq_mul] at hmem
    obtain ⟨d, hd⟩ := exists_div_pow_mul_mem_chartRing x i j hi _ hmem
    refine ⟨d, ?_⟩
    have hc1 : x i / x j * (x j / x i) = 1 := by field_simp
    have hc : (x i / x j) ^ a * (x j / x i) ^ a = 1 := by rw [← mul_pow, hc1, one_pow]
    have h : (x i / x j) ^ d * (s k ⬝ᵥ e) =
        (x i / x j) ^ a * ((x i / x j) ^ d * ((x j / x i) ^ a * (s k ⬝ᵥ e))) := by
      linear_combination (-((x i / x j) ^ d * (s k ⬝ᵥ e))) * hc
    rw [h]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hd
  choose m hm using hk
  refine ⟨∑ k, m k, ?_⟩
  rw [mem_dotDual]
  intro l hl
  obtain ⟨c, hc, rfl⟩ := hgen l hl
  rw [sum_dotProduct]
  refine Subalgebra.sum_mem _ (fun k _ => ?_)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine Subalgebra.mul_mem _ (hc k) ?_
  have hle : m k ≤ ∑ k, m k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  rw [ht, pow_add, mul_comm ((x i / x j) ^ m k), mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) (hm k)
end
