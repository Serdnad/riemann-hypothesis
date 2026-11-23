module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedRestrict

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev locMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

section General

variable {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N]

theorem locMap_mk (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_cellRes (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    locMap (KH.cellMon S I) g (KH.cellRes S M J I x) = KH.cellRes S N J I (locMap (KH.cellMon S J) g x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h, locMap_mk, locMap_mk, GenTwistGenerated.cellRes_mk h]
  · unfold KH.cellRes
    rw [dite_eq_right h, dite_eq_right h]
    simp

end General

variable {V W : Ideal (MRingOver S ι)}

abbrev quotMap (hVW : V ≤ W) : (MRingOver S ι ⧸ V) →ₗ[MRingOver S ι] (MRingOver S ι ⧸ W) :=
  (Ideal.Quotient.factorₐ (MRingOver S ι) hVW).toLinearMap

theorem quotMap_mul (hVW : V ≤ W) (x y : MRingOver S ι ⧸ V) :
    quotMap hVW (x * y) = quotMap hVW x * quotMap hVW y := by
  simp [quotMap]

theorem quotMap_smul (hVW : V ≤ W) (s : S) (x : MRingOver S ι ⧸ V) :
    quotMap hVW (s • x) = s • quotMap hVW x :=
  LinearMap.map_smul_of_tower _ s x

theorem locMap_smul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (s : S)
    (x : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (s • x) = s • locMap T (quotMap hVW) x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.smul'_mk, locMap_mk, locMap_mk, LocalizedModule.smul'_mk, quotMap_smul]

theorem locMap_mul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (x y : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (x * y) = locMap T (quotMap hVW) x * locMap T (quotMap hVW) y := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_mul_mk, locMap_mk, locMap_mk, locMap_mk, LocalizedModule.mk_mul_mk, quotMap_mul]

theorem locMap_one (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) :
    locMap T (quotMap hVW) (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = 1 := by
  have e : ∀ (P : Type) [CommRing P] [Algebra (MRingOver S ι) P],
      (1 : LocalizedModule T P) = LocalizedModule.mk 1 1 := fun _ _ _ => OreLocalization.one_def
  have h1 : quotMap hVW (1 : MRingOver S ι ⧸ V) = 1 := by simp [quotMap]
  rw [e, e, locMap_mk, h1]

theorem cechD_cechMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (f : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n f) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n f) := by
  funext I

  simp only [KH.cechD, KH.cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
  LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (congrArg (fun y => KH.faceSign I.1 k i • y) (locMap_cellRes g _ I.1 (f ⟨_, h⟩))).symm.trans
      (map_zsmul (locMap (KH.cellMon S I.1) g) _ _).symm
  · simp

theorem quotMap_mem_quotPart (hVW : V ≤ W) {c : K → ℤ} {x : MRingOver S ι ⧸ V}
    (hx : x ∈ KH.quotPart S V c) : quotMap hVW x ∈ KH.quotPart S W c := by
  unfold KH.quotPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [quotMap_smul]; exact Submodule.smul_mem _ s hx

theorem locMap_mem_locPart (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    locMap T (quotMap hVW) x ∈ KH.locPart ι (KH.quotPart S W) T c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [locMap_mk]
    exact GenTwistGenerated.mk_mem_locPart _ t a ht (quotMap_mem_quotPart hVW hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [locMap_smul]; exact Submodule.smul_mem _ s hx

end GeneratedRestrict


open GeneratedRestrict in
theorem GeneratedRestrict.proof : GeneratedRestrict.Statement := by
  intro S _ K _ _ ι _ _ V W a hVW hV I
  obtain ⟨r, z, u, hz, hu, h1⟩ := hV I
  refine ⟨r, fun j => KH.cechMap S ι (quotMap hVW) 0 (z j), fun j => locMap _ (quotMap hVW) (u j),
    fun j => ?_, fun j => locMap_mem_locPart hVW _ (hu j), ?_⟩
  · obtain ⟨hzc, hzd⟩ := hz j
    refine GenTwistGenerated.mem_cechZc_zero (fun J => ?_) ?_
    · exact locMap_mem_locPart hVW _ ((Submodule.mem_pi.mp hzc) J (Set.mem_univ _))
    · rw [cechD_cechMap, LinearMap.mem_ker.mp hzd, map_zero]
  · have hc : ∀ j, KH.cechMap S ι (quotMap hVW) 0 (z j) I = locMap _ (quotMap hVW) (z j I) := fun j => rfl

    simp only [hc, ← locMap_mul, ← map_sum, h1, locMap_one]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelSectionsLarge

theorem chartMonomial_mem_relSecM {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (b : K → ℕ) :
    ∏ k, y ⟨k, c0 k⟩ ^ b k ∈ relSecM R y b := by
  classical
  have h := monomial_mem_relSecM R y (b := b) (fun p => if p.2 = c0 p.1 then b p.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c0 k) (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem descend {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (n₁ : ℕ)
    (hstep : ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b) :
    ∀ (m : ℕ) (e : K → ℕ), ∑ k, e k = m → ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ s ∈ relChartLat R y (fun k => (b k : ℤ)) 1,
        s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relSecM R y (b + e) → s ∈ relSecM R y b := by
  intro m
  induction m with
  | zero =>
    intro e he b _ s _ hs
    have h0 : e = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp he) k (Finset.mem_univ k)
    subst h0
    simpa using hs
  | succ m ih =>
    intro e he b hb s hsL hs
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < e k0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ k, e k = 0 := Finset.sum_eq_zero fun k _ => Nat.le_zero.mp (hcon k)
      omega
    set e' : K → ℕ := e - Pi.single k0 1 with he'
    have hee : e = e' + Pi.single k0 1 := by
      funext k
      simp only [he', Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = k0
      · subst hk; simp; omega
      · simp [hk]
    have hsum : ∑ k, e' k = m := by
      have : ∑ k, e k = ∑ k, e' k + 1 := by
        rw [hee]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib]; simp
      omega
    refine ih e' hsum b hb s hsL ?_
    have htL : s * ∏ k, y ⟨k, c0 k⟩ ^ e' k ∈ relChartLat R y (fun k => ((b + e') k : ℤ)) 1 :=
      mul_prod_mem_relChartLat R y (a := fun k => (b k : ℤ)) (a' := fun k => ((b + e') k : ℤ)) (n := 1) e' c0
        (fun k => by simp only [Pi.add_apply]; push_cast; ring) hsL
    have hb' : ∀ k, n₁ ≤ (b + e') k := fun k => le_trans (hb k) (Nat.le_add_right _ _)
    refine hstep (b + e') hb' k0 _ htL ?_
    have hprod : y ⟨k0, c0 k0⟩ * (s * ∏ k, y ⟨k, c0 k⟩ ^ e' k) = s * ∏ k, y ⟨k, c0 k⟩ ^ e k := by
      rw [hee]
      have h1 : ∏ k, y ⟨k, c0 k⟩ ^ (Pi.single k0 1 : K → ℕ) k = y ⟨k0, c0 k0⟩ := by
        rw [Fintype.prod_eq_single k0 (fun k hk => by simp [hk])]
        simp
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, h1]
      ring
    rw [hprod, add_assoc, ← hee]
    exact hs

theorem proof (hC : RelChartPoly.Statement) (hO : RelOneStep.Statement) : RelSectionsLarge.Statement := by
  classical
  intro K _ ι _ Ω _ R hR y hy
  choose c0 hc0 using hy
  obtain ⟨n₁, hn₁⟩ := hO K ι Ω R hR y c0 hc0
  refine ⟨n₁, fun b hb s hs => ?_⟩
  obtain ⟨N, hN⟩ := hC K ι Ω R y c0 _ (hs c0 hc0)
  have hform := mul_mem_relSecM R y hN (chartMonomial_mem_relSecM R y c0 b)
  refine descend R y c0 n₁ hn₁ (∑ _k : K, N) (fun _ => N) rfl b hb s hs ?_
  rw [add_comm]
  convert hform using 1
  have hcancel : (∏ k, y ⟨k, c0 k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c0 k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Nat.cast_one, one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc0 k))]
  rw [← Finset.prod_pow]
  linear_combination (-(s * ∏ k, y ⟨k, c0 k⟩ ^ N)) * hcancel

end RelSectionsLarge

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelOneStep

theorem chart_monomial_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) (c : ∀ k, ι k) :
    ∏ k, y ⟨k, c k⟩ ^ b k ∈ relSecM R y b := by
  classical
  let μ : (Σ k, ι k) → ℕ := fun p => if p.2 = c p.1 then b p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k := by
    intro k
    simp [μ]
  have h := monomial_mem_relSecM R y μ hμ
  have heq : ∏ p, y p ^ μ p = ∏ k, y ⟨k, c k⟩ ^ b k := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [μ]
    rw [Finset.prod_congr rfl fun i _ => (show y ⟨k, i⟩ ^ (if i = c k then b k else 0) =
      if i = c k then y ⟨k, i⟩ ^ b k else 1 by split_ifs <;> simp)]
    simp
  rwa [heq] at h

end RelOneStep

theorem RelOneStep.proof (hC : RelChartPoly.Statement) (hT : RelTorsionBound.Statement) : RelOneStep.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0
  choose n hn using fun k0 : K => hT K ι Ω R hR y c0 hc0 k0
  refine ⟨Finset.univ.sup n, fun b hb k0 t ht hxt => ?_⟩
  have hbk : ∀ k, n k0 ≤ b k := fun k => le_trans (Finset.le_sup (Finset.mem_univ k0)) (hb k)
  obtain ⟨g', hg', hfg⟩ := hn k0 b hbk (y ⟨k0, c0 k0⟩ * t) hxt (by
    intro c hc
    obtain ⟨N, hN⟩ := hC K ι Ω R y c _ (ht c hc)
    refine ⟨N, t * (∏ k, y ⟨k, c k⟩) ^ N, ?_, by ring⟩
    have hm := mul_mem_relSecM R y hN (RelOneStep.chart_monomial_mem R y b c)
    have hone : (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c k⟩ ^ b k = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← zpow_natCast, ← zpow_add₀ (hc k)]
      simp
    have heq : t * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * (∏ k, y ⟨k, c k⟩) ^ N *
        ∏ k, y ⟨k, c k⟩ ^ b k = t * (∏ k, y ⟨k, c k⟩) ^ N := by
      linear_combination (t * (∏ k, y ⟨k, c k⟩) ^ N) * hone
    rw [heq, add_comm] at hm
    exact hm)
  have hx : y ⟨k0, c0 k0⟩ ≠ 0 := hc0 k0
  rwa [mul_left_cancel₀ hx hfg]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ e : Fin D → Fin 2 → ℤ,
      ∑ᶠ W ∈ topComps (twoBlockMInner x (matAct B x) l) D,
          ((multAt (twoBlockMInner x (matAct B x) l) W : ℝ) - multAt (twoBlockMOuter x (matAct B x) c) W) *
            Real.log (charOf W) * (geoNum D W e : ℝ) =
        twoBlockVert x (matAct B x) c l e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleFinite.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    IsMultiHomogIdeal (twoBlockMOuter x (matAct B x) c) ∧ IsMultiHomogIdeal (twoBlockMInner x (matAct B x) l) ∧
      twoBlockMInner x (matAct B x) l ≤ twoBlockMOuter x (matAct B x) c ∧
      (∃ N : ℕ, 0 < N ∧ ∀ f ∈ twoBlockMOuter x (matAct B x) c,
        (N : MRing (FinTwoTypeFamily κ)) * f ∈ twoBlockMInner x (matAct B x) l) ∧
      ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), W.IsPrime → twoBlockMInner x (matAct B x) l ≤ W → IsRelevant W →
        ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) ≤ ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockStep x (matAct B x) a b =
      Real.log (modPieceCard (twoBlockMOuter x (matAct B x) c) (twoBlockMInner x (matAct B x) l) ![a + 1, b + 1])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ArithmeticVolumeDegreeZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A → genDeg (mCoordIdeal y) D A.a ≤ 0 →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

namespace ArithmeticVolumeDegreeZero

end ArithmeticVolumeDegreeZero

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
