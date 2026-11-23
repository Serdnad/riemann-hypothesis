module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LenTLeThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle009
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem smul_sub_eq_smul_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Lk' Lk L0 Lκ0 Ls G X Ec Q U' P1 P2 FΛ S Φ Rr C1 C2 f₂ : R) (e1 e2 e3 n2v z : M)
    (hL0 : L0 = Lκ0 * Lk) (hG : G = P1 * P2 * FΛ) (hC1 : C1 = Lk' * Lk * FΛ * U' * P1)
    (hC2 : C2 = X * (P1 * P2 * Rr)) (hz : z = FΛ • e2)
    (h2 : Lk' • (Lk • e1 - Ls • e3) = Φ • e2) (h1 : n2v = S • e1)
    (h4 : P1 * (Lκ0 * f₂ - Ec * X) = Ec * Q * U') (h5 : P1 * S = P2)
    (h6 : Ec • e1 = e1) (h7 : Φ = Q * Rr) :
    (Lk' * G) • (L0 • (f₂ • e1) - Ls • (X • e3)) = Q • (C1 • n2v + C2 • z) := by
  subst hL0 hG hC1 hC2 hz h1 h7
  have h4v := congrArg (fun t : R => t • ((P2 * FΛ * Lk' * Lk) • e1)) h4
  have h5v := congrArg (fun t : R => t • ((FΛ * Lk' * Lk * Ec * Q * U') • e1)) h5
  linear_combination (norm := module) (P1 * P2 * FΛ * X) • h2 +
    (P1 * P2 * FΛ * Lk' * Lk * X + FΛ * Lk' * Lk * Q * U' * P1 * S) • h6 + h4v - h5v

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem dfd_ps_succ (k : ℕ) : ps W (k + 1) = W.φA (ps W k) := by
  unfold ps
  rw [pow_succ', AlgHom.mul_apply]

theorem dfd_ps_zero : ps W 0 = qA W := by
  unfold ps
  rw [pow_zero, AlgHom.one_apply]

theorem dfd_φLam_mem (A : ArcP n) (a : ZMod n) (e : ℕ) :
    W.φA (abelian₂ W A a e) ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} := by
  unfold abelian₂
  rw [map_prod]
  refine Submonoid.prod_mem _ fun s _ => ?_
  rw [map_pow, ← dfd_ps_succ]
  exact Submonoid.pow_mem _ (Submonoid.subset_closure
    (show ps W (s + 1) ∈ {x : LetA O n | ∃ k ≥ 1, x = ps W k} from ⟨s + 1, by omega, rfl⟩)) _

theorem dfd_φD_three (T : LocLat G Qp LL O) (x : W.DD T) :
    ((W.φD T) ^ 3) x = W.φD T (((W.φD T) ^ 2) x) := by
  rw [pow_succ']
  rfl

theorem dfd_φA_lA (k : ℕ) : W.φA (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem dfd_alg_lA (k : ℕ) : algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
  simp only [lA, lE, map_pow, map_natCast]

theorem dfd_closure_AΔ {x : LetA O n}
    (hx : x ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) : x ∈ W.AΔ := by
  have key : Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} ≤ W.AΔ.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact TypesA.ps_mem W k
  exact key hx

end Local

end Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.SatW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem coef_step_of (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA2 : ∀ f ∈ W.AΔ, ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g)
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hinj : Function.Injective (algebraMap O LL))
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (bi : ℕ) (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (j : ℕ) (hj : j ≤ bi) (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ h ∈ W.AΔ, W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) -
        algebraMap (LetA O n) W.EE (qA W ^ j * g) * s =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ j *
        (algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) * g + qA W * h)) * s := by
  obtain ⟨hbij, hs1, hp2⟩ := hcase
  have hfin : Module.finrank K₀ K = 1 := finrank_one_of_bij' hbij
  obtain ⟨-, -, h9c⟩ := hP9 T hT hs1 hp2
  obtain ⟨⟨hπΔ', -, ⟨wπ, hwπ⟩, -⟩, -⟩ := h9c hfin
  have hπ : W.π₀ ∈ W.AΔ := hπΔ'
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := p_nzd_O W hinj
  have hQe : qA W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
  have hQΔ : qA W ∈ W.AΔ := by rw [hQe]; exact add_mem hπ (natCast_mem _ _)
  have hUπ : UPi PD.p W.π₀ := ⟨wπ, PD.p - 1, 0, by rw [hwπ, mul_zero, add_zero]⟩
  have hUQ : UPi PD.p (qA W) := ⟨wπ, PD.p - 1, 1, by rw [hQe, hwπ, mul_one]⟩
  have hEQ : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := isUnit_EE_of_UPi W hUQ
  have hΓ : ∀ a : LetA O n, W.γE W.gam (algebraMap (LetA O n) W.EE a) =
      algebraMap (LetA O n) W.EE (W.γA W.gam a) := fun a => W.γE_ext W.gam a

  obtain ⟨g4, hg4, h4⟩ := hA4
  obtain ⟨Xc, hXc⟩ : ∃ X : LetA O n, X = algebraMap O (LetA O n) ((W.χΓ W.gam : Oˣ) : O) :=
    ⟨_, rfl⟩
  have hXcΔ : Xc ∈ W.AΔ := by rw [hXc]; exact Subalgebra.algebraMap_mem _ _
  obtain ⟨w, hw⟩ : ∃ w : LetA O n, w = Xc + qA W * g4 := ⟨_, rfl⟩
  have hwΔ : w ∈ W.AΔ := by rw [hw]; exact add_mem hXcΔ (mul_mem hQΔ hg4)
  have h4' : W.γA W.gam (qA W) = qA W * w := by
    rw [h4, hw, hXc, Algebra.smul_def]; ring
  obtain ⟨g5, hg5, h5⟩ := hA2 (qA W) hQΔ
  have hw1 : w = 1 + W.π₀ * g5 := by
    apply W.EE_inj
    apply hEQ.mul_left_cancel
    rw [← map_mul (algebraMap (LetA O n) W.EE), ← map_mul (algebraMap (LetA O n) W.EE)]
    exact congrArg (algebraMap (LetA O n) W.EE) (by linear_combination h5 - h4')

  have hmulw : w * (fun i => PowerSeries.invOfUnit (w i) 1) = 1 := funext fun i => by
    show w i * PowerSeries.invOfUnit (w i) 1 = 1
    refine PowerSeries.mul_invOfUnit (w i) 1 ?_
    rw [hw1, hwπ]
    simp [letπ, zero_pow hp1]
  have hwU : IsUnit w := ⟨⟨w, _, hmulw, by rw [mul_comm]; exact hmulw⟩, rfl⟩
  obtain ⟨wu, hwu⟩ := id hwU
  obtain ⟨wi, hwi⟩ : ∃ x : LetA O n, x = ((wu⁻¹ : (LetA O n)ˣ) : LetA O n) := ⟨_, rfl⟩
  have hwwi : w * wi = 1 := by rw [hwi, ← hwu]; exact wu.mul_inv
  have hwiΔ : wi ∈ W.AΔ := by
    have hwδ : ∀ δ ∈ W.DelF, W.γA δ w = w := hwΔ
    show ∀ δ ∈ W.DelF, W.γA δ wi = wi
    intro δ hδ
    apply hwU.mul_left_cancel
    calc w * W.γA δ wi = W.γA δ w * W.γA δ wi := by rw [hwδ δ hδ]
      _ = W.γA δ (w * wi) := (map_mul (W.γA δ) w wi).symm
      _ = w * wi := by rw [hwwi, map_one]

  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = bi - j := ⟨_, rfl⟩
  have hbi : bi = j + m := by omega
  have e' : -((bi : ℤ) - (j : ℤ)) = -((m : ℕ) : ℤ) := by rw [hm, Nat.cast_sub hj]
  have key : ((((W.χΓ W.gam) ^ m)⁻¹ : Oˣ) : O) = 1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j) := by
    have h0 := hcc ((bi : ℤ) - j)
    rw [e', zpow_neg, zpow_natCast] at h0
    linear_combination -h0
  have hc' : ((W.χΓ W.gam : Oˣ) : O) ^ m * (1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j)) = 1 := by
    rw [← key, ← Units.val_pow_eq_pow_val, Units.mul_inv]
  obtain ⟨C, hC⟩ : ∃ C : LetA O n, C = algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) := ⟨_, rfl⟩
  have hCΔ : C ∈ W.AΔ := by rw [hC]; exact Subalgebra.algebraMap_mem _ _
  have hcA : Xc ^ m * (1 - ((PD.p : ℕ) : LetA O n) * C) = 1 := by
    have := congrArg (algebraMap O (LetA O n)) hc'
    simpa only [map_mul, map_sub, map_one, map_pow, map_natCast, ← hC, ← hXc] using this

  obtain ⟨R1, hR1d⟩ : ∃ R : LetA O n,
      R = (Finset.range m).sum (fun i => w ^ i * Xc ^ (m - 1 - i)) := ⟨_, rfl⟩
  obtain ⟨R2, hR2d⟩ : ∃ R : LetA O n, R = (Finset.range m).sum (fun i => w ^ i) := ⟨_, rfl⟩
  have hR1 : R1 * (w - Xc) = w ^ m - Xc ^ m := by rw [hR1d]; exact geom_sum₂_mul w Xc m
  have hR2 : R2 * (w - 1) = w ^ m - 1 := by rw [hR2d]; exact geom_sum_mul w m
  have hR1Δ : R1 ∈ W.AΔ := by
    rw [hR1d]; exact sum_mem fun i _ => mul_mem (pow_mem hwΔ _) (pow_mem hXcΔ _)
  have hR2Δ : R2 ∈ W.AΔ := by rw [hR2d]; exact sum_mem fun i _ => pow_mem hwΔ _
  obtain ⟨M, hMd⟩ : ∃ M : LetA O n, M = Xc ^ m * C + g4 * R1 * (1 + W.π₀ * C) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N : LetA O n, N = g5 * R2 * (1 + W.π₀ * C) + C := ⟨_, rfl⟩
  have hQM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * M := by
    linear_combination (-(1 + W.π₀ * C)) * hR1 + (R1 * (1 + W.π₀ * C)) * hw + hcA -
      (Xc ^ m * C) * hQe - qA W * hMd
  have hπN : w ^ m * (1 + W.π₀ * C) = 1 + W.π₀ * N := by
    linear_combination (-(1 + W.π₀ * C)) * hR2 + (R2 * (1 + W.π₀ * C)) * hw1 - W.π₀ * hNd
  have hpM : ((PD.p : ℕ) : LetA O n) ^ 1 * M = W.π₀ * (N - M) := by
    linear_combination hπN - hQM - M * hQe
  obtain ⟨Z, hZ⟩ := dvd_of_UPi hO hUπ 1 (N - M) M hpM
  have hMZ : M = W.π₀ * Z := by
    apply p_cancel hO
    linear_combination hpM + W.π₀ * hZ
  have hMΔ : M ∈ W.AΔ := by
    rw [hMd]
    exact add_mem (mul_mem (pow_mem hXcΔ _) hCΔ)
      (mul_mem (mul_mem hg4 hR1Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ)))
  have hNΔ : N ∈ W.AΔ := by
    rw [hNd]
    exact add_mem (mul_mem (mul_mem hg5 hR2Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ))) hCΔ
  have hZΔ : Z ∈ W.AΔ := mem_AΔ_of_p_pow W hO 1 (by rw [← hZ]; exact sub_mem hNΔ hMΔ)
  have hYM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * (W.π₀ * Z) := by rw [← hMZ]; exact hQM

  let S : Submonoid (LetA O n) :=
    { carrier := {x | ∃ t ∈ W.AΔ, W.γA W.gam x = x * (1 + W.π₀ * qA W * t)}
      mul_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb + W.π₀ * qA W * ta * tb,
          add_mem (add_mem hta htb) (mul_mem (mul_mem (mul_mem hπ hQΔ) hta) htb), ?_⟩
        rw [map_mul (W.γA W.gam), ha, hb]; ring
      one_mem' := ⟨0, zero_mem _, by simp⟩ }
  have hsub : {x : LetA O n | ∃ k ≥ 1, x = ps W k} ⊆ (S : Set (LetA O n)) := by
    rintro x ⟨k, hk, rfl⟩
    exact hA3 k hk
  have hsS : s' ∈ S := Submonoid.closure_le.mpr hsub hs'
  obtain ⟨t, ht, hts⟩ := hsS

  have h1 := congrArg (W.γE W.gam) hs
  rw [map_mul (W.γE W.gam), hΓ, hΓ, hts, map_pow (W.γA W.gam), h4', mul_pow,
    map_mul (algebraMap (LetA O n) W.EE), map_mul (algebraMap (LetA O n) W.EE), ← hs] at h1
  have hu : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ bi)) := by
    rw [map_pow]; exact hEQ.pow bi
  have h2' : algebraMap (LetA O n) W.EE (w ^ bi) * W.γE W.gam s =
      s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t) := by
    apply hu.mul_left_cancel
    linear_combination h1
  have hEwb : algebraMap (LetA O n) W.EE w ^ bi * algebraMap (LetA O n) W.EE wi ^ bi = 1 := by
    rw [← mul_pow, ← map_mul, hwwi, map_one, one_pow]
  rw [map_pow] at h2'
  have hΓs : W.γE W.gam s = algebraMap (LetA O n) W.EE wi ^ bi *
      (s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t)) := by
    linear_combination (algebraMap (LetA O n) W.EE wi ^ bi) * h2' - (W.γE W.gam s) * hEwb

  obtain ⟨g2, hg2, h2⟩ := hA2 g hg
  have hg' : W.γA W.gam g = g + W.π₀ * qA W * g2 := by linear_combination h2
  have hwj : w ^ j * wi ^ j = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwm1 : w ^ m * wi ^ m = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwbi : wi ^ bi = wi ^ j * wi ^ m := by rw [← pow_add, ← hbi]
  obtain ⟨h, hh⟩ : ∃ h : LetA O n,
      h = wi ^ m * (g2 + g * t + W.π₀ * qA W * g2 * t - g * Z) := ⟨_, rfl⟩
  have keyA : W.γA W.gam (qA W ^ j * g) * (wi ^ bi * (1 + W.π₀ * qA W * t)) =
      qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h) := by
    rw [map_mul (W.γA W.gam), map_pow (W.γA W.gam), h4', hg']
    linear_combination
      ((qA W * w) ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t)) * hwbi +
      (qA W ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t) * wi ^ m) * hwj -
      (qA W ^ j * g * wi ^ m) * hYM + (qA W ^ j * g * (1 + W.π₀ * C)) * hwm1 -
      (W.π₀ * qA W ^ j * qA W) * hh
  have hfin2 : W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) =
      algebraMap (LetA O n) W.EE (qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h)) * s := by
    rw [map_mul (W.γE W.gam), hΓ, hΓs, ← keyA]
    simp only [map_mul, map_pow]
    ring
  refine ⟨h, ?_, ?_⟩
  · rw [hh]
    exact mul_mem (pow_mem hwiΔ _) (sub_mem (add_mem (add_mem hg2 (mul_mem hg ht))
      (mul_mem (mul_mem (mul_mem hπ hQΔ) hg2) ht)) (mul_mem hg hZΔ))
  · rw [← hC, hfin2, map_add (f := _)]
    ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_setup_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (hDc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL)
    (hJ21 : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) :
    let A := arcOf b w S η up size
    A.OK ∧ Win W A T₁ ∧ Win W A T₂ ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * _root_.Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
    ∃ rr : ℕ, (rr : ℝ) ≤ 3 * _root_.Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) ∧
      ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
        cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
          Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr) :=
  SetupA.arcSetup_of W hcase F hB CR hWR hJmp hJ21

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arcBasic [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi) :
    let A := arcOf b w S η up size
    A.OK ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
  SetupA.arcBasic_core W F hB

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem jumps_of_surjective_lattice_map : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hJ : UsedJ D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL),
    (∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L),
      Formalism.MainNotions.LiftingTheory.Sur ((HW l).W K 1 LL hG) f →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) T₂.ρ τ a →
        IsJumpV ((D.loc l).PD K) T₁.ρ τ a) ∧
    (∀ (T₂ Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₂.L Y.L)
      (π : LatHom Y.L ((HW l).W K 1 LL hG).one.L) (cc : ↥(GK K) → T₂.V),
      cc ∈ latticeCocycles T₂.L → IsCrys ((D.loc l).PD K) T₂.ρ → IsCrys ((D.loc l).PD K) Y.ρ →
      Formalism.MainNotions.LiftingTheory.IsExtOf ((HW l).W K 1 LL hG) ι π cc →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) Y.ρ τ a →
        a = 0 ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) := by
  intro D HW F hJ l _ K LL hG
  refine ⟨?_, ?_⟩
  · intro T₁ T₂ f hS τ a ha
    obtain ⟨c1, c2, hO⟩ := hS
    obtain ⟨T₀, ι, hses, c0⟩ := Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F hJ.a22 l K 1 LL hG T₁ T₂ f ⟨c1, c2, hO⟩
    exact (hJ.a23 l K LL T₀ T₁ T₂ ι f hses c0 c1 c2 τ a).2 (Or.inr ha)
  · intro T₂ Y ι π cc _ c2 cY hext τ a ha
    obtain ⟨cone, hone0⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL hG
    rcases (hJ.a23 l K LL T₂ Y _ ι π hext.1 c2 cY cone τ a).1 ha with h | h
    · exact Or.inr h
    · exact Or.inl (hone0 τ a h)

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem step_ii (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T₁ T₂ : LocLat G Qp LL O}
    (hc₁ : IsCrys PD T₁.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (F : LatHom T₁.L T₂.L) (i : ZMod n) (Ai ri : ℕ)
    (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (P : O[X])
    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P y))
    {x : W.DD T₂} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x) : InImg W F i (aeval dop₂ P x) := by
  have hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧ IsUnit (algebraMap (LetA O n) W.EE (qA W)) ∧
      IsUnit ((W.DelF.card : ℕ) : O) := by
    exact lemG_units W hcase hP9 hc₁ hO hOv hinj
  obtain ⟨hπ, hq, -⟩ := hU
  have hz : InImg W F i (qA W ^ (Ai + ri) • x) := by
    exact q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hx
  obtain ⟨z, hzN, hzx⟩ := hz
  set N := Ai + ri
  set e : W.EE := (↑hq.unit⁻¹ : W.EE) ^ N with he
  have key : algebraMap (LetA O n) W.EE (qA W ^ N) * e = 1 := by
    rw [he, map_pow, ← mul_pow, hq.mul_val_inv, one_pow]
  have hqy : qA W ^ N • (e • z) = z := by
    rw [← algebraMap_smul W.EE (qA W ^ N), smul_smul, key, one_smul]
  have hFy : W.map F (e • z) = x := by
    rw [LinearMap.map_smul, hzx, ← algebraMap_smul W.EE (qA W ^ N) x, smul_smul, mul_comm, key, one_smul]
  have hy : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P (e • z)) := by
    apply hCONS
    rw [hqy]
    exact hzN
  exact ⟨aeval dop₁ P (e • z), hy, by rw [aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂, hFy]⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
