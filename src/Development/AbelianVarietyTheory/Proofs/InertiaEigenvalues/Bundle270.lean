module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle240
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PushCob

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage TensorProduct

theorem contract_equivariant {R Y Q : Type} [CommRing R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Q] [Module R Q] (ψ : Y →ₗ[R] R) (A : Y →ₗ[R] Y) (B : Q →ₗ[R] Q) (u t : R)
    (h : ∀ y, ∃ z, ψ (A y) - u * ψ y = t * z) (x : Y ⊗[R] Q) :
    ∃ q : Q, TensorProduct.lid R Q (ψ.rTensor Q (TensorProduct.map A B x)) =
      u • B (TensorProduct.lid R Q (ψ.rTensor Q x)) + t • q := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul y q =>
    obtain ⟨z, hz⟩ := h y
    refine ⟨z • B q, ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_smul, ← add_smul]
    rw [← hz]; congr 1; ring
  | add x x' hx hx' =>
    obtain ⟨q, hq⟩ := hx
    obtain ⟨q', hq'⟩ := hx'
    refine ⟨q + q', ?_⟩
    simp only [map_add (f := _), hq, hq', smul_add]
    abel

theorem actQab_mk {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
    {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (h : XiOK AA act ξ) (a b : ℤ)
    (g : G) (m : ↥(Mxi AA ξ a)) :
    actQab h a b g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (actM h a g m) := rfl

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem inclW_zl (z : ℤ_[l]) :
    inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z

theorem mem_Mxi {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) (w : WCb l)
    (hw : w ∈ Mxi (AinfSub l) (xiU AI) (k : ℤ)) : ∃ a : Ainf l, w = inclW l (AI.ξ ^ k * a) := by
  obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hw
  refine ⟨a, ?_⟩
  rw [LinearMap.mulLeft_apply, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rfl

theorem mem_Mxi_zero {P : LocPrime l} (AI : LocAinf l P) (w : ↥(Mxi (AinfSub l) (xiU AI) 0)) :
    ∃ a : Ainf l, (w : WCb l) = inclW l a := by
  simpa using mem_Mxi AI 0 w w.2

def scaled {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) : Y →ₗ[ℤ_[l]] ℤ_[l] where
  toFun y := ⟨(l : ℚ_[l]) ^ r * ψ y, by
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p, inv_pow,
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact h y⟩
  map_add' y y' := by
    apply Subtype.ext
    change _ = (l : ℚ_[l]) ^ r * ψ y + (l : ℚ_[l]) ^ r * ψ y'
    rw [← mul_add, ← map_add (f := _)]
  map_smul' z y := by
    apply PadicInt.ext
    change (l : ℚ_[l]) ^ r * ψ (z • y) = (z : ℚ_[l]) * ((l : ℚ_[l]) ^ r * ψ y)
    rw [map_smul, Algebra.smul_def, PadicInt.algebraMap_apply]
    ring

theorem scaled_coe {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) (y : Y) :
    ((scaled ψ r h y : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ r * ψ y := rfl

theorem push_coboundary : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s e r N : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥(Gj K s) →* (Y →ₗ[ℤ_[l]] Y)) (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]), (∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) → (∀ (σ : GQ l) (hσ : σ ∈ Gj K s) (y : Y), ‖ψ (ρ ⟨σ, hσ⟩ y) - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) → ∀ (f : ↥(Gj K s) → Y) (c : GQ l → ℚ_[l]), (∀ (σ : GQ l) (hσ : σ ∈ Gj K s), c σ = ψ (f ⟨σ, hσ⟩)) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → IsCob (repQ (D.locA l) (Gj K s) ρ 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ N • (f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) → ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1) := by
  intro D l _ K s e r N Y _ _ ρ ψ hψ hρ f c hc one hone hcob
  obtain ⟨x, hx⟩ := hcob
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (l : ℚ_[l]) ^ r ≠ 0 := pow_ne_zero _ hl
  obtain ⟨m0, hm0⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ x))
  obtain ⟨a0, ha0⟩ := mem_Mxi_zero _ m0
  refine ⟨qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * io (D.locA l) a0, qB_mul_mem _ (io_mem _ _), ?_⟩
  intro σ hσ
  have hn : ‖(((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l _ (D.loc l).χQ_cyc).1, one_zpow]
  set u' : ℚ_[l] := (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) with hu'
  let u : ℤ_[l] := ⟨u', hn⟩
  have hu : (u : ℚ_[l]) = u' := rfl
  obtain ⟨q, hq⟩ := contract_equivariant (scaled ψ r hψ) (ρ ⟨σ, hσ⟩)
    (actQab (act := (D.locA l).actWCbHom.comp (Gj K s).subtype)
      ⟨fun g x hx => (xiOK (D.locA l)).1 (g : GQ l) x hx, (xiOK (D.locA l)).2.1,
        fun g => (xiOK (D.locA l)).2.2 (g : GQ l)⟩ 0 ((e : ℤ) + 1) ⟨σ, hσ⟩) u ((l : ℤ_[l]) ^ r)
    (fun y => ⟨⟨_, hρ σ hσ y⟩, by
      apply Subtype.ext
      change (l : ℚ_[l]) ^ r * ψ (ρ ⟨σ, hσ⟩ y) - u' * ((l : ℚ_[l]) ^ r * ψ y) =
        (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * (ψ (ρ ⟨σ, hσ⟩ y) - u' * ψ y)
      push_cast
      ring⟩) x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := mem_Mxi_zero _ m
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ w))
    (hx ⟨σ, hσ⟩)
  simp only [map_smul, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  rw [← hm0] at hq
  have h2 := h1.trans (congrArg₂ (· - ·) hq hm0.symm)
  beta_reduce at h2
  erw [actQab_mk] at h2
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_sub] at h2
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h2
  obtain ⟨a', ha'⟩ := mem_Mxi (D.locA l) (e + 1) _ (by rw [Nat.cast_succ]; exact h2)
  have h3 : algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ N * scaled ψ r hψ (f ⟨σ, hσ⟩)) -
      (algebraMap ℤ_[l] (Ainf l) u * (D.locA l).actW σ a0 +
        algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ r) * a - a0) = (D.locA l).ξ ^ (e + 1) * a' := by
    apply inclW_injective
    rw [← ha']
    have h4 : inclW l ((D.locA l).actW σ a0) = (D.locA l).actWCbHom σ (m0 : WCb l) := by
      rw [ha0, inclW_act]; rfl
    rw [map_sub, map_sub, map_add (f := _), inclW_zl, map_mul (inclW l), map_mul (inclW l), inclW_zl,
      inclW_zl, h4, ← ha0, ← ha]
    change _ = (l : ℤ_[l]) ^ N • scaled ψ r hψ (f ⟨σ, hσ⟩) • (one : WCb l) -
      (u • (D.locA l).actWCbHom σ (m0 : WCb l) + (l : ℤ_[l]) ^ r • (m : WCb l) - (m0 : WCb l))
    rw [hone, smul_smul, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def]
  have h5 := congrArg (io (D.locA l)) h3
  rw [map_sub, map_sub, map_add (f := _), io_zl _ (D.locT l), map_mul (io _), map_mul (io _),
    map_mul (io _), map_pow (io _), io_zl _ (D.locT l), io_zl _ (D.locT l), io_act] at h5
  have h6 : io (D.locA l) (D.locA l).ξ ^ (e + 1) * io (D.locA l) a' ∈
      FilB (D.loc l) ((e : ℤ) + 1) := by
    have := FilB_mul (FilB_pow (io_ξ_mem (D.locA l)) (e + 1)) (io_mem (D.locA l) a')
    simpa using this
  refine ⟨a, ?_⟩
  have h7 := qB_mul_mem ((l : ℚ_[l]) ^ r)⁻¹ h6
  rw [← h5] at h7
  convert h7 using 1
  have h8 : qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * qB (D.loc l) ((l : ℚ_[l]) ^ r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlr, map_one]
  rw [map_mul ((D.loc l).actQdR σ), AlgEquiv.commutes, hc σ hσ, ← io_apply, PadicInt.coe_mul,
    scaled_coe, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast, hu]
  simp only [map_mul]
  linear_combination (-(qB (D.loc l) ((l : ℚ_[l]) ^ N) * qB (D.loc l) (ψ (f ⟨σ, hσ⟩))) + io (D.locA l) a) * h8

end GlobalTheory.PushCob
end
end

section

noncomputable section

namespace GlobalTheory

open PowerSeries GlobalTheory.BK

theorem nat_mul_add_le_pow {l : ℕ} (hl : 2 ≤ l) (n : ℕ) : n * l + l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right l ih
    have h2 := Nat.mul_le_mul_left (n * l + l) hl
    nlinarith

theorem zeta_add_lphi_conn_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hηH hHl hy₀
  set y : Vec K a ι := (X : K⟦X⟧) ^ e • y₀ with hy
  set A := l - 14 * H with hA
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hlA : (l : K) ^ A ≠ 0 := pow_ne_zero _ hl0
  set c : K := ((l : K) ^ A)⁻¹ with hc
  set w : Vec K a ι := c • (D.zeta y + D.lphi (D.conn y)) with hw
  let t : ℕ → Vec K a ι := fun n => -(c • (D.lphi ^ (n + 2)) (D.conn y))
  have hterm : ∀ n, ∃ v ∈ D.MM, t n = (l : K) ^ n • v := by
    intro n
    obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀ (n + 1)
    obtain ⟨w', hw', h₂⟩ := GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule O K l e a ι D.toPhiMod (n + 1) w₁ hw₁
    set B := H + 2 * η + (n + 1) * (η - 1) with hB
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hineq : B + A + n ≤ l ^ (n + 1) := by
      have h1 := nat_mul_add_le_pow hl2 n
      have h2 : (n + 1) * (η - 1) ≤ (n + 1) * H := Nat.mul_le_mul_left _ (by omega)
      have h3 : n * (H + 1) ≤ n * l := Nat.mul_le_mul_left _ (by omega)
      have h4 : (n + 1) * H = n * H + H := by ring
      have h5 : n * (H + 1) = n * H + n := by ring
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hineq
    rw [h₂, hd, show B + A + n + d = B + (A + (n + d)) by ring, pow_add (l : K) B, mul_smul] at h₁
    have h₃ := congrArg (fun v => ((l : K) ^ B)⁻¹ • v) h₁
    simp only [inv_smul_smul₀ (pow_ne_zero B hl0)] at h₃
    refine ⟨-((l : K) ^ d • w'), neg_mem (PhiMod.l_pow_smul_mem_MM _ d hw'), ?_⟩
    change -(c • (D.lphi ^ (n + 1 + 1)) (D.conn y)) = _
    rw [h₃, pow_add, mul_smul, hc, inv_smul_smul₀ hlA, pow_add, mul_smul, smul_neg]
  have hpart : ∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m := by
    intro m
    have key := D.zeta_add_sum_mem y (m + 1)
    rw [Finset.sum_range_succ'] at key
    have heq : w - ∑ n ∈ Finset.range m, t n = c • (D.zeta y + (∑ n ∈ Finset.range m,
        (D.lphi ^ (n + 1 + 1)) (D.conn y) + (D.lphi ^ (0 + 1)) (D.conn y))) := by
      simp only [t, hw, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add, pow_one, smul_add,
        Finset.smul_sum]
      abel
    rw [heq]
    exact Submodule.smul_of_tower_mem _ c (uPow_anti (by omega) key)
  refine ⟨w, GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms O K l e a ι D.toPhiMod w t hterm hpart, ?_⟩
  rw [hw, hc, smul_inv_smul₀ hlA]

end GlobalTheory
end
end

section

noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.ExactTripleBK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem smul_eq_of_retr {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) {n : ℕ}
    {τ : ZMod a} {Λ : Matrix ι κ K⟦X⟧} (h : Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (v : Vec K a ι) : (l : K) ^ n • v τ = Λ *ᵥ F.app v τ := by
  rw [Hom.app_apply, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem onPol_injective {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) :
    Function.Injective F.onPol := by
  refine (injective_iff_map_eq_zero F.onPol).2 fun w hw => ?_
  obtain ⟨v, rfl⟩ := P.Man.mkQ_surjective w
  have hv : F.app v ∈ Q.Man := Q.cls_eq_zero_iff.1 hw
  change P.cls v = 0
  rw [PhiMod.cls_eq_zero_iff]
  have h1 : (l : K) ^ n • v ∈ P.Man := by
    refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
    obtain ⟨Λ, hΛA, hΛF⟩ := hΛ τ
    have hFv := mem_tot.1 (Q.mem_Man.1 hv) τ
    have h2 : ((l : K) ^ n • v) τ = Λ *ᵥ F.app v τ := by
      rw [Pi.smul_apply]
      exact smul_eq_of_retr F hΛF v
    rw [h2]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (A_le_Rpi l e (hΛA i k)) (hFv k)
  have h3 := P.Man.smul_mem ((l : K) ^ n)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)), one_smul] at h3


omit [CompleteSpace K] in
theorem onD_actD {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (g : TameGal K l e a) (d : P.D) :
    F.onD (Δ₁.actD g d) = Δ₂.actD g (F.onD d) := by
  have h1 : Δ₁.actD g d = red (Δ₁.act g (cst d)) := rfl
  rw [h1, ← Hom.red_app, F.app_act, Δ₂.red_act, Hom.red_app, red_cst]

theorem map_constantCoeff_smul_one (c : K) :
    (c • (1 : Matrix ι ι K⟦X⟧)).map constantCoeff = c • (1 : Matrix ι ι K) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_smul]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem chars_subset {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    (F : BKHom D₀ D₁) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) (τ : ZMod a) :
    D₀.desc.chars τ ⊆ D₁.desc.chars τ := by
  rintro c ⟨d, hd, hc⟩
  refine ⟨F.onD d, fun h0 => hd ?_, fun ζ => ?_⟩
  · obtain ⟨Λ, -, hΛF⟩ := hΛ τ
    have h1 : Λ.map constantCoeff *ᵥ F.onD d τ = (l : K) ^ n • d τ := by
      rw [show F.onD d τ = (F.mat τ).map constantCoeff *ᵥ d τ from rfl, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, hΛF, map_constantCoeff_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (l_ne_zero l))
  · rw [← onD_actD]
    change (F.mat τ).map constantCoeff *ᵥ _ = _ • ((F.mat τ).map constantCoeff *ᵥ d τ)
    rw [hc ζ, Matrix.mulVec_smul]

theorem exists_Z_of_onPol_eq_zero {μ : Type} [Fintype μ] [DecidableEq μ] {η H : ℕ}
    {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H} {D₂ : BKDat O K l e a μ η H}
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    (hinj : Function.Injective F.onPol) (n : ℕ)
    (hn : ∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) {w : D₁.Pol} (hw : w ∈ D₁.Z)
    (hG : G.onPol w = 0) : ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w := by
  obtain ⟨⟨y, hy, rfl⟩, hinv⟩ := D₁.desc.mem_Z.1 hw
  have hGy : G.app y ∈ D₂.M :=
    D₂.mem_M_of_mem_Man (G.app_mem_EM hy) (D₂.cls_eq_zero_iff.1 hG)
  obtain ⟨x, hx, hxy⟩ := hn _ hGy
  have hGz : G.app ((l : K) ^ n • y - x) = 0 := by
    rw [map_sub, LinearMap.map_smul_of_tower, hxy, sub_self]
  have hlM : ∀ {m : Vec K a κ}, m ∈ D₁.M → (l : K) ^ n • m ∈ D₁.M := fun hm => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hm _
  have hEz : E K l e ^ η • ((l : K) ^ n • y - x) ∈ D₁.M := by
    rw [smul_sub, smul_comm]
    refine sub_mem (hlM hy) ?_
    exact D₁.M.smul_mem (⟨E K l e ^ η, pow_mem (E_mem l e _) η⟩ : A O K) hx
  have hker : G.app (E K l e ^ η • ((l : K) ^ n • y - x)) = 0 := by rw [map_smul, hGz, smul_zero]
  obtain ⟨m₀, hm₀, hFm⟩ := Submodule.mem_map.1 ((hex.exact _ hEz).1 hker)
  have hFm' : F.app m₀ = E K l e ^ η • ((l : K) ^ n • y - x) := hFm
  have hFy : F.app (Ezpow K l e (-η) • m₀) = (l : K) ^ n • y - x := by
    rw [map_smul, hFm', smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]
  have hy₀M : Ezpow K l e (-η) • m₀ ∈ D₀.EM η := by
    show E K l e ^ η • (Ezpow K l e (-η) • m₀) ∈ D₀.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hm₀
  have hF : F.onPol (D₀.cls (Ezpow K l e (-η) • m₀)) = (l : K) ^ n • D₁.cls y := by
    rw [BK.Hom.onPol_cls, hFy, map_sub, map_smul, D₁.cls_eq_zero_iff.2 (D₁.M_le_Man hx), sub_zero]
  refine ⟨D₀.cls (Ezpow K l e (-η) • m₀), D₀.desc.mem_Z.2 ⟨⟨_, hy₀M, rfl⟩, fun g => hinj ?_⟩, hF⟩
  rw [F.onPol_act, hF, map_smul, hinv g]

end GlobalTheory.ExactTripleBK


open GlobalTheory.ExactTripleBK in
theorem GlobalTheory.exactTriple_jumps_chars_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ μ _ _ _ _ η H D₀ D₁ D₂ F G hex
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker O K l e a κ μ D₁.toPhiMod D₂.toPhiMod G.toHom hex.finiteLength
  have hΛ := GlobalTheory.T.exists_integral_leftInverse_of_phiModule_exactTriple O K l e a ι κ μ D₀.toPhiMod D₁.toPhiMod D₂.toPhiMod F.toHom G.toHom hex n hn
  have hinj := onPol_injective F.toHom n hΛ
  exact ⟨GlobalTheory.T.breuilKisin_jumps_subset_of_split_mono O K l e a ι κ η H D₀ D₁ F.toHom n hΛ, fun τ => chars_subset F n hΛ τ, hinj,
    fun m hm w hw hG => exists_Z_of_onPol_eq_zero F G hex hinj m hm hw hG⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  first | exact @GlobalTheory.Cyc.act_laws | exact GlobalTheory.Cyc.act_laws | (intros; apply GlobalTheory.Cyc.act_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  first | exact @GlobalTheory.Cyc.phi_free | exact GlobalTheory.Cyc.phi_free | (intros; apply GlobalTheory.Cyc.phi_free <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.admissibleLetterData_window_arithmetic : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  first | exact @GlobalTheory.WindowArith.windows | exact GlobalTheory.WindowArith.windows | (intros; apply GlobalTheory.WindowArith.windows <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem reduction_sameSS_of_lattices :
    ∀ {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
      (ρ : Representation LL G V) (L L' : Lattice (O := O) ρ) (lam : O), Irreducible lam →
      SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) :=
  fun _ L L' _ hlam => lattice_reduction_sameSS hlam L L'

end GlobalTheory.TopSteps
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair

namespace GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_cong_one [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  obtain ⟨b, hb⟩ := exists_int_cong P z hz
  obtain ⟨a, ha⟩ := (hef P hP).2.2 b
  have h3 := OrderUnits.val_int_le P 1 _ (by simpa using ha)
  refine ⟨a, ?_⟩
  rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
  have := Valuation.map_sub_le _ hb h3
  rw [sub_sub_sub_cancel_left] at this
  exact this

theorem exists_cong [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (m : ℕ) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  induction m with
  | zero => exact ⟨0, by simpa [iota_zero, zero_coord] using hz⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top m
    have hv : Valued.v (iota t P) = WithZero.exp (-(m : ℤ)) := by
      refine eq_exp_of_le (val_iota_le_of_mem hP m ht) fun h3 => ht' ?_
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      convert h3 using 2
      push_cast; ring
    have ht0 : iota t P ≠ 0 := fun h => by
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨c, hc⟩ := exists_cong_one hs hP ((iota a P - z) / iota t P) (by
      rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]; exact ha)
    refine ⟨a - t * c, ?_⟩
    have : iota (a - t * c) P - z = -(iota t P * (iota c P - (iota a P - z) / iota t P)) := by
      rw [iota_sub, iota_mul, sub_coord, mul_coord]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, hv]
    refine (mul_le_mul' le_rfl hc).trans_eq ?_
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring


end GlobalTheory.LamTie.ConjLevel
end
end
