module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Gen

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ} (g : Fin d → R)

def monSpan (k : ℕ) : Submodule R M where
  carrier := {x | ∃ cf : (Fin d → ℕ) → M, x = ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, g i ^ α i) • cf α}
  add_mem' := by
    rintro x y ⟨c1, rfl⟩ ⟨c2, rfl⟩
    exact ⟨c1 + c2, by simp [smul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r x ⟨c1, rfl⟩
    exact ⟨r • c1, by simp [Finset.smul_sum, smul_comm r]⟩

theorem single_mem_monSpan {k : ℕ} {α : Fin d → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (m : M) :
    (∏ i, g i ^ α i) • m ∈ monSpan (M := M) g k := by
  refine ⟨fun β => if β = α then m else 0, ?_⟩
  rw [Finset.sum_eq_single α]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hα h

theorem prod_pow_add_single (α : Fin d → ℕ) (i : Fin d) :
    (∏ l, g l ^ (α + Pi.single i 1 : Fin d → ℕ) l) = g i * ∏ l, g l ^ α l := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pow_smul_top_le_monSpan (k : ℕ) :
    (Ideal.span (Set.range g)) ^ k • (⊤ : Submodule R M) ≤ monSpan (M := M) g k := by
  induction k with
  | zero =>
    intro x _
    refine ⟨fun _ => x, ?_⟩
    simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ k ih =>
    rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
    intro r hr n hn
    obtain ⟨cf, rfl⟩ := ih hn
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    rw [Finset.sum_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hβ' : β + Pi.single i 1 ∈ Finset.Nat.antidiagonalTuple d (k + 1) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      simp [Finset.sum_add_distrib, hβ]
    have e : (a i • g i) • ((∏ l, g l ^ β l) • cf β) =
        (∏ l, g l ^ (β + Pi.single i 1 : Fin d → ℕ) l) • (a i • cf β) := by
      rw [smul_smul, smul_smul, prod_pow_add_single g β i, smul_eq_mul]
      congr 1
      ring
    rw [e]
    exact single_mem_monSpan g hβ' _

end Gen

theorem taylorRep_holds : TaylorRep := by
  intro D B P j X ka wL wF G la k x hx
  obtain ⟨cf, hcf⟩ := pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨cf, ?_⟩
  have : x - ∑ α ∈ mon D j k, ym G la α • cf α = 0 := by
    rw [sub_eq_zero]; exact hcf
  rw [this]
  exact Submodule.zero_mem _

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem prod_sec_pow_mul_mem {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j)))
    {n : ℕ} {v : Rp X la N} (hv : v ∈ Vw X la N (addL u wL n)) :
    (∏ i ∈ s, sec X la w i.succ ^ α i) * v ∈ Vw X la N (addL u wL (n + ∑ i ∈ s, α i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using hv
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have := sec_pow_mul_mem X la w a.succ u _ (α a) ih
    rwa [show n + ∑ i ∈ s, α i + α a = n + (α a + ∑ i ∈ s, α i) by ring] at this

theorem taylorSpanGenerators : TaylorSpanGenerators := by
  intro D B P j X ka wL wF G la T k hk α hα i
  have hs : ∑ i, α i = k := Finset.Nat.mem_antidiagonalTuple.1 hα
  have hkT : ∑ i, α i ≤ T := by
    have : a0 D j T ≤ T := Nat.sub_le _ _
    omega
  have h0 : emb X la G.N (X.inc wF (G.th' i)) ∈ Vw X la G.N (addL wF wL 0) := by
    rw [addL_zero]; exact emb_mem_Vw X la G.N wF _
  have h1 := sec_pow_mul_mem X la G.w 0 wF 0 (T - ∑ i, α i) h0
  have h2 := prod_sec_pow_mul_mem G.w wF α Finset.univ h1
  rw [show 0 + (T - ∑ i, α i) + ∑ i, α i = T by omega] at h2
  have hf : secPow X la G.w α * sec X la G.w 0 ^ (T - ∑ i, α i) * emb X la G.N (X.inc wF (G.th' i)) ∈
      Vw X la G.N (addL wF wL T) := by
    rw [mul_assoc]; exact h2
  refine ⟨toHK X la G.w wF T ⟨_, hf⟩,
    toHK0 X la G.w wF ⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩, ?_, ?_, rfl⟩
  · exact Submodule.subset_span ⟨⟨_, hf⟩, ⟨α, i, by omega, rfl⟩, rfl⟩
  · apply Subtype.ext
    have e1 : ((ym G la α : ↥(Frac0 X la G.w)) : Lw X la G.w) = frac X la G.w (∑ i, α i) (secPow X la G.w α) :=
      coe_prod_sfr X la G.w α
    rw [Submodule.coe_smul, Subalgebra.smul_def, smul_eq_mul, e1, coe_toHK, coe_toHK0, ← frac_zero, frac_mul,
      add_zero]
    have e2 := frac_pow_mul X la G.w (∑ i, α i) (T - ∑ i, α i)
      (secPow X la G.w α * emb X la G.N (X.inc wF (G.th' i)))
    rw [show ∑ i, α i + (T - ∑ i, α i) = T by omega] at e2
    rw [← e2]
    congr 1
    show _ = _
    ring

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

def YmDeriv : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) (γ α : Fin (WeightFamilies.dimY D j) → ℕ),
    (∑ i, γ i) ≤ ∑ i, α i →
      hasse X la G.w (bcol jj α) ((ym G la γ : ↥(Frac0 X la G.w)) : Lw X la G.w) =
        if γ = α then ((wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) ^ (∑ i, α i) else 0

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Ord

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem ord_prod_eq_zero (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i ∈ s, ord ϖ ζ (f i) = 0) : ord ϖ ζ (∏ i ∈ s, f i) = 0 := by
  refine Finset.prod_induction f (fun x => ord ϖ ζ x = 0) (fun a b ha hb => ?_) (ord_one ζ h) hf
  rw [ord_mul ζ h, ha, hb, add_zero]

theorem eq_zero_of_ord_top [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by
  obtain ⟨n, hn⟩ := h.denom x
  have h0 : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) = 0 := by
    refine eq_zero_of_localization _ fun J hJ => ?_
    have h1 := hx ⟨J, hJ⟩
    rw [ord_eq _ h hn, ordAt, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · rw [ENat.map_eq_top_iff] at h1
      exact (vL_eq_top_iff (ζ := (⟨J, hJ⟩ : Pts O A)) _).1 h1
    · exact absurd h1 (WithTop.coe_ne_top)
  have h2 : ϖ ^ n • x = 0 := congrArg Subtype.val h0
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

end Ord

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem ord_uC_eq_zero {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (hC : Q.InCurve)
    (ζ : PtsG G la) (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ)
    (h0 : ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) = 0) :
    ord (unifO X la G.N) ζ (uC G la jj α) = 0 := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  unfold uC
  refine ord_prod_eq_zero ζ hU _ _ fun i _ => ?_
  rw [ord_pow ζ hU, h0, smul_zero]

theorem uBall_of_column (hCol : Column) : UBall := by
  unfold UBall
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  unfold LocalPointData.A0 at hb ⊢
  rw [mem_ballO_iff Q.c hU hC.2.2]
  intro ζ
  obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
  have h1 := (mem_ballO_iff Q.c hU hC.2.2 _).1 (hb jj) ζ
  rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add] at h1
  exact h1

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_snd_le {D : D7} {j N : ℕ} {β : Idx D j N →₀ ℕ} {q : (Idx D j N →₀ ℕ) × (Idx D j N →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal β) :
    (q.2.sum fun _ n => n) ≤ (β.sum fun _ n => n) := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Nat.le_add_left _ _

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j}
  {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {w : Fin N → B.Cusp j wL}

theorem hasse_Op_smul (o : Op X la N) (x : ↥(HK X la w wF)) (β : Idx D j N →₀ ℕ) :
    hasse X la w β (((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF))) : Lw X la w) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
        @algebraMap (Op X la N) (Kp X la N) _ _ _ (hasseOp X la N q.1 o) • hasse X la w q.2 (x : Lw X la w) := by
  have e1 : ((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF)) : Lw X la w) =
      algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) o) * (x : Lw X la w) := by
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w),
      ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  rw [e1]
  refine (hasse_mul X la w β _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  rw [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lc X la w),
    ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  exact hasse_algebraMap_Op X la w q.1 o

theorem aaRep_holds : AARep := by
  unfold AARep
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw x hx
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  suffices key : ∃ x' : ↥(HK X la G.w wF),
      (∃ hx' : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
          hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF,
        ∀ β hβ, toA0K X la G.w wF ⟨_, hx' β hβ⟩ ∈ Q.A0) ∧
      toWK X la G.w wF (a0 D j T) x' = x by
    obtain ⟨x', ⟨_, h2⟩, h3⟩ := key
    exact ⟨x', h3, fun β hβ _ => h2 β hβ⟩
  unfold LocalPointData.AA LocalPointData.AAp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, ⟨hx0, hb0⟩, rfl⟩ := hy
    refine ⟨x0, ⟨hx0, fun β hβ => ?_⟩, rfl⟩
    unfold LocalPointData.A0
    rw [mem_ballO_iff Q.c hU hC.2.2]
    intro ζ
    have h := hb0 β hβ ζ
    simpa [LocalPointData.ordA] using h
  | zero =>
    have hz : ∀ β : Idx D j G.N →₀ ℕ,
        hasse X la G.w β ((0 : ↥(HK X la G.w wF)) : Lw X la G.w) = 0 := fun β => by
      exact map_zero (hasse X la G.w β)
    refine ⟨0, ⟨fun β _ => by rw [hz]; exact (HK X la G.w wF).zero_mem, fun β hβ => ?_⟩, map_zero _⟩
    convert Q.A0.zero_mem using 1
    rw [← map_zero (toA0K X la G.w wF)]
    exact congrArg _ (Subtype.ext (hz β))
  | add a b _ _ ha hb =>
    obtain ⟨xa, ⟨ha1, ha2⟩, rfl⟩ := ha
    obtain ⟨xb, ⟨hb1, hb2⟩, rfl⟩ := hb
    have hs : ∀ β : Idx D j G.N →₀ ℕ, hasse X la G.w β ((xa + xb : ↥(HK X la G.w wF)) : Lw X la G.w) =
        hasse X la G.w β (xa : Lw X la G.w) + hasse X la G.w β (xb : Lw X la G.w) := fun β => by
      exact map_add (hasse X la G.w β) _ _
    refine ⟨xa + xb, ⟨fun β hβ => by rw [hs]; exact add_mem (ha1 β hβ) (hb1 β hβ), fun β hβ => ?_⟩, map_add _ _ _⟩
    convert Q.A0.add_mem (ha2 β hβ) (hb2 β hβ) using 1
    rw [← map_add (f := _)]
    exact congrArg _ (Subtype.ext (hs β))
  | smul o y _ ih =>
    classical
    obtain ⟨x0, ⟨h1, h2⟩, rfl⟩ := ih
    let g : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun q =>
      if h : hasse X la G.w q.2 (x0 : Lw X la G.w) ∈ HK X la G.w wF then ⟨_, h⟩ else 0
    have hg' : ∀ q : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ), ∀ hq : (q.2.sum fun _ n => n) ≤ a0 D j T - 1,
        g q = ⟨_, h1 q.2 hq⟩ := fun q hq => dif_pos (h1 q.2 hq)
    let F : (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun β =>
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, @algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o) • g q
    have he : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β ((@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) =
          ((F β : ↥(HK X la G.w wF)) : Lw X la G.w) := by
      intro β hβ
      rw [hasse_Op_smul, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Submodule.coe_smul_of_tower, hg' q ((sum_snd_le hq).trans hβ)]
      rfl
    refine ⟨@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0, ⟨fun β hβ => ?_, fun β hβ => ?_⟩, ?_⟩
    · rw [he β hβ]
      exact Submodule.coe_mem _
    · have hm : toA0K X la G.w wF (F β) ∈ Q.A0 := by

        rw [map_sum]
        refine Q.A0.sum_mem fun q hq => ?_
        rw [LinearMap.map_smul_of_tower, algebraMap_smul, hg' q ((sum_snd_le hq).trans hβ)]
        exact Q.A0.smul_mem _ (h2 q.2 ((sum_snd_le hq).trans hβ))
      convert hm using 1
      exact congrArg _ (Subtype.ext (he β hβ))
    · rw [LinearMap.map_smul_of_tower]
      rfl

end PoleLengthBounds
end
end
